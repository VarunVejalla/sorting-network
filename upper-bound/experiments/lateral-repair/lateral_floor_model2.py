#!/usr/bin/env python3
"""UB-20 cost model after the spill-locality review (SPILL-LOCALITY.md sec. 7).

Parameter model only.  Chvatal's (4.2)-(4.5) are implemented here directly (following
../tapered/exchange_rate.py) so the lateral terms can be inserted:

  (4.2-L)  mu(A nu - 1) - slack - side (eta_d2 + eta_sh) - mu( sib*mult*s(delta) + 2 delta A^2 k ) >= 0
           * eta_d2: distance-2 spill, a bulk excess at block margin d0 = m/k (u's keys in I_j ~ beta);
           * eta_sh: shift damage at v_j's internal cuts, margin from fringe inflow:
             d0 = (1 - delta_F) pi(v)/(2 n_u) - D/n_u  ~ m[(1-delta_F)(A nu k - 1) A nu/(2 A^2 k^2) - (3 mu + slack)];
           * the factor 2 on delta A^2 k: v_{j+1}'s order-0 outsiders from its children are passed to
             v_j by the merge (review item A4).
  floors   eta(d0) = 2 ln(2(m+1)) * l1 / (lam* m), with Bennett's bound c(lam) = e^lam - 1 - lam:
           lam* = largest lam with (e^lam - 1 - lam)/lam <= R, R = d0/(E1 m), E1 = sqrt(2(1+ln m)/m);
           l1 = (1 + ln(1 + E1 m) + ln 2) / ln(2(m+1))  (count of admissible states, review item A2).
  (4.4-L)  mu = (delta_F/(2L)) (A nu k - 1)/(A^2 k^2)  (with (4.3) if kept);
  (4.5-L)  L eps_F <= A nu delta - A^2 k delta^2;  fringe floor certified at delta_F.
  (O-L)    m g >= t sqrt(2 lam_spill),  g = f/m - (L mu + (3 mu + slack + eta_d2 + eta_sh)/(A nu)).
  cost     3 T(lg m) + 2 (lg m + 1).

Run:  python -I lateral_floor_model2.py [variant-substring ...]
"""
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
sys.path.insert(0, HERE)
import exchange_rate as E  # noqa: E402
from lateral_certfloor_model import FLOOR  # noqa: E402

LADDER = np.arange(12.0, 40.01, 0.25)
LAM_TAB = np.linspace(1e-4, 30, 30000)
RATIO_TAB = (np.expm1(LAM_TAB) - LAM_TAB) / LAM_TAB      # increasing in lam


def lam_star(R):
    """Largest lam with (e^lam - 1 - lam)/lam <= R (0 where R <= 0)."""
    idx = np.searchsorted(RATIO_TAB, np.maximum(R, 0), side="right") - 1
    return np.where(R > 0, LAM_TAB[np.clip(idx, 0, len(LAM_TAB) - 1)], 0.0)


def floor_eta(d0, m):
    E1 = np.sqrt(2 * (1 + np.log(m)) / m)
    lam = lam_star(d0 / (E1 * m))
    l1 = (1 + np.log1p(E1 * m) + math.log(2)) / np.log(2 * (m + 1))
    with np.errstate(divide="ignore"):
        return np.where(lam > 0, 2 * np.log(2 * (m + 1)) * l1 / (lam * m), np.inf)


def conditions(x, y, z, G, P, L):
    """Chvatal-type conditions with the lateral terms; returns ok, mu, epsF_allowed, eta_d2, eta_sh."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    m = 2.0 ** G
    with np.errstate(all="ignore"):
        mu44 = 0.5 * (P["dF"] / L) * (A * nu * k - 1) / (A * A * k * k)
        mu = np.minimum(mu44, nu / (A * k * k)) if P["use43"] else mu44
        slack = P["slack"] * (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
        eta_d2 = floor_eta(m / k, m)
        d0_sh = m * ((1 - P["dF"]) * (A * nu * k - 1) * A * nu / (2 * A * A * k * k) - (3 * mu + slack))
        eta_sh = floor_eta(d0_sh, m)
        base = mu * (A * nu - 1) - slack - P["side"] * (eta_d2 + eta_sh)
        ok = (A * nu > 1) & (base > 0) & (y > z) & np.isfinite(eta_d2) & np.isfinite(eta_sh)
        mult = (k - 1) if P.get("sibmult") is None else np.minimum(k - 1, P["sibmult"])

        def g(dl):
            s = dl * k * A * A / (1 - (dl * k * A) ** 2)
            return base - mu * (P["sib"] * mult * s + 2 * dl * A * A * k)
        hi0 = np.minimum(1 / (k * A), nu / (2 * A * k)) * (1 - 1e-12)
        lo, hi = np.zeros_like(base), hi0.copy()
        ghi = g(hi0)
        for _ in range(55):
            mid = (lo + hi) / 2
            gm = g(mid)
            lo = np.where(gm >= 0, mid, lo)
            hi = np.where(gm >= 0, hi, mid)
        dl = np.where(ghi >= 0, hi0, lo)
        epsF_allowed = A * nu * dl - A * A * k * dl * dl
        ok &= epsF_allowed > 0
    return ok, mu, epsF_allowed, eta_d2, eta_sh, slack


def search(P, L=2.0, t=6.0, integer=False, step=0.5, wstep=0.5):
    if integer:
        xs, zs, ds = np.arange(1, 13.0), np.arange(1, 13.0), np.arange(1, 17.0)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    X, Z, D, G = np.meshgrid(xs, zs, ds, LADDER, indexing="ij")
    Y = Z + D
    k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
    ok0, mu, epsFa, eta_d2, eta_sh, slack = conditions(X, Y, Z, G, P, L)
    Af, pf = FLOOR[P["dF"]]
    with np.errstate(all="ignore"):
        fom = E.f_over_m(k, A, nu)
        lgm_F = np.log2(Af * (L / epsFa) ** pf / fom)
        base_ok = ok0 & (G >= lgm_F) & (G >= 2 * (X + Y))
        g = fom - (L * mu + (3 * mu + slack + eta_d2 + eta_sh) / (A * nu))
    spb = (X + Y) / (X * Z)
    sorts = 2 if P["rounds"] == 1 else 3
    best = None
    for w in np.arange(2, 30.01, wstep):
        eB = 2.0 ** -w
        lgm_B = float(E.lgm_for(np.array([eB]), P["rounds"])[0])
        with np.errstate(all="ignore"):
            lgm_O = np.where(g > 0, np.log2(2 * t * t * P["side"] * eB / (A * nu * np.maximum(g, 1e-300) ** 2)), np.inf)
        ok = base_ok & (G >= lgm_B) & (G >= lgm_O)
        if integer:
            Lw = np.ceil(G - 1e-9) + 1
            cost = (sorts * Lw * (Lw + 1) / 2 + 2 * Lw) * spb
        else:
            cost = (sorts * G * (G + 1) / 2 + 2 * (G + 1)) * spb
        cost = np.where(ok, cost, np.inf)
        i = np.unravel_index(np.argmin(cost), cost.shape)
        if np.isfinite(cost[i]) and (best is None or cost[i] < best["obj"]):
            best = dict(obj=float(cost[i]), w=float(w), x=float(X[i]), y=float(Y[i]), z=float(Z[i]), lgm=float(G[i]),
                        eta_d2=float(eta_d2[i]), eta_sh=float(eta_sh[i]), epsF=float(epsFa[i] / L), spb=float(spb[i]),
                        lgm_B=lgm_B, lgm_F=float(lgm_F[i]), lgm_O=float(lgm_O[i]))
    return best


L4 = dict(side=0.5, sibmult=2.0, use43=False, slack=0.0)
VARIANTS = [
    ("S   slack removed", dict(dF=128 / 4095, slack=0.0)),
    ("L4' dF=1/16", dict(L4, dF=1 / 16)),
    ("L4' dF=1/8", dict(L4, dF=1 / 8)),
    ("L4' dF=1/5", dict(L4, dF=1 / 5)),
]


def main():
    names = sys.argv[1:]
    print(" variant          | ideal (win)  eps_B    eta_d2   eta_sh   eps_F    (x,y,z)          lg m [B, F, O]")
    for name, kn in VARIANTS:
        if names and not any(nm in name for nm in names):
            continue
        P = dict(E.DEFAULT); P.update(kn)
        b = search(P)
        bi = search(P, integer=True)
        if b is None:
            print(f" {name:16s} | infeasible", flush=True)
            continue
        wi = f"{bi['obj']:5.0f}" if bi else "   - "
        print(f" {name:16s} | {b['obj']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['eta_d2']:.1e}  {b['eta_sh']:.1e}  {b['epsF']:.1e}  "
              f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.2f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f},{b['lgm_O']:4.1f}]", flush=True)


if __name__ == "__main__":
    main()
