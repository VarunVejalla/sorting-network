#!/usr/bin/env python3
"""Exchange rate  tolerated eps_B  ->  slope  for Chvatal-type trees with sort-based separators.

Parameter model only (floats, no certificates).  Conditions are Chvatal DCS-TR-294 (4.2)-(4.5)
(printed pp. 12-13, Lemmas 4.3/4.4), written multiplied through by A*nu:

  (4.4)  mu <= (dF/2) (A nu k - 1)/(A^2 k^2)                      [fringe capacity]
  (4.3)  mu <= nu/(A k^2)                                          [top node outsider-free]
  (4.2)  eps_B*side + slack + mu*(1 + (k-1)*sib(delta) + delta*A^2*k) <= mu*A*nu
         slack = (A nu k - 2 A nu + 1)/(2 A^2 k^2)   (block/boundary misalignment, Lemma 4.2)
         sib(delta) = delta k A^2/(1 - (delta k A)^2)  (Lemma 4.1)
  (4.5)  eps_F <= A nu delta - A^2 k delta^2,  delta k A < 1

Separator models (m = column height):
  one round : eps_B(m) = sqrt(2(1+ln m)/m)                         (Lemma 6.1 / Theorem 5.1)
  two rounds: eps_B2(m) from BULK2 (e)-(g): min d s.t. max_lam m(lam d/2 - c(lam) E1) >= ln(2(m+1)) + ln(1000)/16,
              E1 = sqrt(2(1+ln m)/m), c(lam) = lam^2 (1/2 + 2 lam/9)
Fringe model: f = m * f_over_m(k,A,nu) rows; eps_F = 1/(cF * f), f >= f_floor.
  two-round proved route: cF = 656 (1/86e6 at f = 131040, F2ROUND.md), f_floor = 92160
  one-round proved:       cF = 1/99 (1/86e6 needs f ~ 8.5e9);  obstruction: cF <= 2 (eps_F (2f+1) > 1)
Cost: slope = sorts * T(lg m) * (x+y)/(x z), T(L) = L(L+1)/2 (continuous, 'ideal');
      'win' = sorts * T(ceil(lg m)+1) * spb (power-of-two window as in the 1419 package).
"""
import math
import numpy as np

LN2 = math.log(2)


def eps1(L):
    return np.sqrt(2 * (1 + L * LN2) / 2.0 ** L)


def eps2_scalar(L):
    m = 2.0 ** L
    E1 = math.sqrt(2 * (1 + L * LN2) / m)
    rhs = math.log(2 * (m + 1)) + math.log(1000) / 16
    lo, hi = 1e-30, 1.0
    for _ in range(90):
        d = math.sqrt(lo * hi)
        # best lambda: maximise lam d/2 - lam^2(1/2+2lam/9)E1 on a fine grid around d/(2E1)
        lam0 = min(1.0, d / (2 * E1))
        lams = lam0 * np.linspace(0.5, 1.5, 201)
        lams = lams[lams <= 1]
        K = np.max(lams * d / 2 - lams ** 2 * (0.5 + 2 * lams / 9) * E1)
        if m * K >= rhs:
            hi = d
        else:
            lo = d
    return hi


_LG = np.arange(8.0, 100.0, 0.02)
_E1 = eps1(_LG)
_E2 = np.array([eps2_scalar(L) for L in _LG])


def lgm_for(eps, rounds):
    """least lg m with eps_sep(m) <= eps (eps array ok)."""
    tab = _E1 if rounds == 1 else _E2           # decreasing in L
    eps = np.asarray(eps, dtype=float)
    idx = np.searchsorted(-tab, -eps, side="left")
    idx = np.clip(idx, 0, len(_LG) - 1)
    return _LG[idx]


def f_over_m(k, A, nu):
    return (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)


DEFAULT = dict(rounds=2, dF=128 / 4095, use43=True, slack=1.0, sib=1.0, side=1.0,
               cF=656.0, f_floor=92160.0)


def evaluate(eps, x, y, z, P):
    """Vectorised. Returns (lg m, slope_ideal, slope_win, details) ; inf where infeasible."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    with np.errstate(all="ignore"):
        mu44 = 0.5 * P["dF"] * (A * nu * k - 1) / (A * A * k * k)
        mu = np.minimum(mu44, nu / (A * k * k)) if P["use43"] else mu44
        slack = P["slack"] * (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
        base = mu * (A * nu - 1) - slack - P["side"] * eps
        ok = (A * nu > 1) & (base > 0) & (y > z)

        def g(dl):
            s = dl * k * A * A / (1 - (dl * k * A) ** 2)
            mult = (k - 1) if P.get("sibmult") is None else np.minimum(k - 1, P["sibmult"])
            return base - mu * (P["sib"] * mult * s + dl * A * A * k)
        lo = np.zeros_like(base)
        hi = np.minimum(1 / (k * A), nu / (2 * A * k)) * (1 - 1e-12)
        # if g(hi) >= 0 we can take hi directly
        ghi = g(hi)
        for _ in range(55):
            mid = (lo + hi) / 2
            gm = g(mid)
            lo = np.where(gm >= 0, mid, lo)
            hi = np.where(gm >= 0, hi, mid)
        dl = np.where(ghi >= 0, np.minimum(1 / (k * A), nu / (2 * A * k)) * (1 - 1e-12), lo)
        epsF = A * nu * dl - A * A * k * dl * dl
        ok &= epsF > 0
        f_need = np.maximum(1 / (P["cF"] * epsF), P["f_floor"])
        lgm_F = np.log2(f_need / f_over_m(k, A, nu))
        lgm_B = lgm_for(np.full_like(base, eps), P["rounds"])
        lgm_51 = 2 * (x + y)
        lgm = np.maximum(np.maximum(lgm_F, lgm_B), lgm_51)
        sorts = 2 if P["rounds"] == 1 else 3
        spb = (x + y) / (x * z)
        ideal = sorts * lgm * (lgm + 1) / 2 * spb
        Lw = np.ceil(lgm - 1e-9) + 1
        win = sorts * Lw * (Lw + 1) / 2 * spb
        ideal = np.where(ok, ideal, np.inf)
        win = np.where(ok, win, np.inf)
    return lgm, ideal, win, dict(lgm_F=lgm_F, lgm_B=lgm_B, epsF=epsF, mu=mu, spb=spb)


def best(eps, P, step=0.2, integer=False):
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    X, Z, D = np.meshgrid(xs, zs, ds, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(eps, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return dict(x=float(X[i]), y=float(Y[i]), z=float(Z[i]), lgm=float(lgm[i]), ideal=float(ideal[i]),
                win=float(win[i]), spb=float(det["spb"][i]), lgm_F=float(det["lgm_F"][i]),
                lgm_B=float(det["lgm_B"][i]), epsF=float(det["epsF"][i]))


VARIANTS = [
    ("V0 Chvatal as is (2-round sep)", {}),
    ("V0' slack removed", dict(slack=0.0)),
    ("V0'' sibling term removed", dict(sib=0.0)),
    ("V1 per-side Property B (eps/2)", dict(side=0.5)),
    ("V2 V1 + dF = 1/2", dict(side=0.5, dF=0.5)),
    ("V3 V2 + drop (4.3)", dict(side=0.5, dF=0.5, use43=False)),
    ("V4 V3 + no slack", dict(side=0.5, dF=0.5, use43=False, slack=0.0)),
    ("V5 V4 + no sibling", dict(side=0.5, dF=0.5, use43=False, slack=0.0, sib=0.0)),
]

TARGETS = [26, 23, 20, 18, 16, 14, 12, 10, 8]


def main():
    print("calibration: two-round threshold for d = 1/59e6: lg m =", float(lgm_for(1 / 59e6, 2)),
          "(BULK2: 41.658); one-round for 1/59e6:", float(lgm_for(1 / 59e6, 1)))
    P0 = dict(DEFAULT)
    k, A, nu = 64.0, 4096.0, 1 / 64
    lg, idl, win, det = evaluate(1 / 59e6, np.array(6.0), np.array(12.0), np.array(6.0), P0)
    print(f"check (6,12,6) eps=1/59e6: lg m={float(lg):.2f} (F needs {float(det['lgm_F']):.2f}, "
          f"B needs {float(det['lgm_B']):.2f}) ideal={float(idl):.0f} win={float(win):.0f}")
    for floor_name, extra in [("f_floor=92160 (proved 2-round F route)", {}),
                              ("f_floor=2^10 (hypothetical F proof at small fringe)", dict(f_floor=1024.0))]:
        for rounds in (2, 1):
            print(f"\n===== {floor_name}; {rounds}-round separator =====")
            for name, kn in VARIANTS:
                P = dict(DEFAULT); P.update(kn); P.update(extra); P["rounds"] = rounds
                if rounds == 1:
                    P["cF"] = 1 / 99 if "f_floor" not in extra else 2.0
                    P["f_floor"] = max(P["f_floor"], 1.0)
                bb = [(best(2.0 ** -w, P), w) for w in TARGETS]
                row = ["   -  " if b is None else f"{b['ideal']:6.0f}" for b, w in bb]
                bb = [(b, w) for b, w in bb if b]
                bw = min(bb, key=lambda t: t[0]["ideal"]) if bb else None
                s = (f" | best {bw[0]['ideal']:.0f} at eps=2^-{bw[1]} (x,y,z)=({bw[0]['x']:.1f},{bw[0]['y']:.1f},"
                     f"{bw[0]['z']:.1f}) lg m={bw[0]['lgm']:.1f} [B {bw[0]['lgm_B']:.1f}, F {bw[0]['lgm_F']:.1f}]"
                     f" spb={bw[0]['spb']:.3f}") if bw else ""
                print(f"{name:34s}", " ".join(row), s)
    print("\ncolumns: eps_B = 2^-w for w in", TARGETS, "; entries: best continuous slope (ideal cost)")


if __name__ == "__main__":
    main()
