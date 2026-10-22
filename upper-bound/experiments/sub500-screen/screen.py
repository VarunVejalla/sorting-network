#!/usr/bin/env python3
"""UB-37 / structural screen: re-price the R1 route under idealized hypotheticals.

Parameter model only (floats, no certificates). Calibrated to the kernel-checked 789.75 point
(upper-bound/best/notes/sub800/R1-PROOF.md, r1_point.py):

  schedule  k = 2^x, A = 2^y, nu = 2^-z (integers, y > z), stages per bit (x+y)/(x z)
  mu        (1 - 2^-10) min( dF/2 (A nu k - 1)/(A^2 k^2) , nu/(A k^2) )          (4.4), (4.3)
  (4.2')    mu + (k-1) mu sib(d) + mu d A^2 k + r* + 0.1 mu + eps_B eta <= mu A nu
            r* = (k-1)/(2 A^2 k^2) (design P residual), sib(d) = d k A^2/(1 - d^2 k^2 A^2)
  (4.5)     eps_F <= A nu d - A^2 k d^2
  bulk      lg m_B: walk bound (ROUND2, cached ../walk-bound/na_tables.npz) at eps_B;
            two-round separator (3 sorts) uses d(m), one-round (2 sorts) uses E1(m)
  fringe    f = CAL * a_dF * J^p_dF, J = 1/eps_F (fits of ../lateral-repair/lateral_certfloor_model.py;
            CAL = 1.32 matches the certified f = 7934 at J = 190000, dF = 1/8);
            lg m_F = lg(f / f_over_m), f_over_m ~ p/2 with p = (A nu k - 1)/(A^2 k^2)
  rows      q = ceil(max(lg m_B, lg m_F)) (power-of-two window as in the Lean package)
  cost      (stage depth) * (x+y)/(x z), stage depth = sorts * S(q) unless a hypothetical says otherwise

The delta of (4.2')/(4.5) is chosen to minimise q (it trades eps_B against eps_F).
Run:  python -I screen.py            (writes nothing; screen.out is its stdout)
"""
import math
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_Z = np.load(os.path.join(HERE, "..", "walk-bound", "na_tables.npz"))
_LS, _LE1, _LD = _Z["Ls"], np.log(_Z["e1"]), np.log(_Z["d"])

# certified-route fringe floor fits f = a * J^p (fringe_general_screen); 1/4 and 1/3 are extrapolated
FLOOR = {128 / 4095: (6.41, 0.518), 1 / 16: (7.43, 0.523), 1 / 8: (14.79, 0.494), 1 / 5: (36.91, 0.454)}
CAL = 7934 / (14.79 * 190000 ** 0.494)
ETA = 1 + 7 / 4096


def floor_fit(dF):
    if dF in FLOOR:
        return FLOOR[dF]
    # log-linear extrapolation in lg dF from the 1/8 and 1/5 fits (flagged in the output)
    (a1, p1), (a2, p2) = FLOOR[1 / 8], FLOOR[1 / 5]
    s = (math.log(dF) - math.log(1 / 8)) / (math.log(1 / 5) - math.log(1 / 8))
    return math.exp(math.log(a1) + s * (math.log(a2) - math.log(a1))), p1 + s * (p2 - p1)


def lgm_bulk(eps, rounds):
    """least lg m with walk-bound precision <= eps (log-interpolated, decreasing tables)."""
    tab = _LE1 if rounds == 1 else _LD
    le = math.log(eps)
    if le >= tab[0]:
        return float(_LS[0])
    if le < tab[-1]:
        return math.inf
    return float(np.interp(-le, -tab, _LS))


S = lambda q: q * (q + 1) / 2  # noqa: E731  Batcher depth


def evaluate(x, y, z, H):
    """Return dict with q, cost, details for one integer schedule under hypothetical H."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    if A * nu <= 1 or x < 2:
        return None
    dF = H.get("dF", 1 / 8)
    p = (A * nu * k - 1) / (A * A * k * k)
    mu44 = 0.5 * dF * p
    mu = (1 - 2 ** -10) * (mu44 if H.get("no43") else min(mu44, nu / (A * k * k)))
    rstar = H.get("rstar", 1.0) * (k - 1) / (2 * A * A * k * k)
    tol = H.get("tol", 1.0)          # idealized error tolerance multiplier on eps_B
    rounds = H.get("rounds", 2)
    a_f, p_f = floor_fit(dF)
    f_over_m = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
    best = None
    dmax = 1 / (k * A) * (1 - 1e-9)
    for d in np.geomspace(dmax * 1e-6, dmax, 160):
        sib = d * k * A * A / (1 - (d * k * A) ** 2)
        budget = mu * A * nu - mu - (k - 1) * mu * sib - mu * d * A * A * k - rstar - 0.1 * mu
        epsF = A * nu * d - A * A * k * d * d
        kap = H.get("R2")            # SLACKFREE route R2: residual kappa (mu + eps_B/2)/(A nu - 1), no r*
        if kap is not None:
            budget -= kap * mu / (A * nu - 1)
        if H.get("center2"):         # refined centred chain (v3): |s| <= (mu (A nu + 1) + eps_B eta / 2)/(2 A nu - 1)
            budget += mu - mu * A * nu / (2 * (A * nu - 1))           # v4: w/2 = (mu A nu + eps_B eta/2)/(2(A nu - 1))
        if H.get("center3"):         # review-corrected: w/2 = (mu A nu + cross)/(2(A nu - 1)), cross = far crossings
            qq = max(8, int(math.ceil(H.get("q_hint", 24))))  # over half a child range (rows ~ 0.026 m: walk tail)
            cross = 2 * tail_frac(qq, 0.5 * (p / 2 + 0.0) * 0 + 0.026 * 2.0 ** qq) if H.get("cross") is None else H["cross"]
            budget += mu - mu * A * nu / (2 * (A * nu - 1)) - cross / (2 * (A * nu - 1))
        if H.get("dyn"):             # dynamic O_L (reviewer remark): outsider term -> 2 cross/(A nu - 1) only
            qq = max(8, int(math.ceil(H.get("q_hint", 24))))
            cross = 2 * tail_frac(qq, 0.026 * 2.0 ** qq)
            budget += mu - 2 * cross / (A * nu - 1)
        if H.get("dyn2"):            # dynamic O_L with full parent crossings: w (1 - 3/(2 A nu)) = eps_B eta/(A nu) + 2 far
            qq = max(8, int(math.ceil(H.get("q_hint", 24))))
            far = 2 * tail_frac(qq, 0.026 * 2.0 ** qq)
            amp = 1 - 3 / (2 * A * nu)
            if amp <= 0:
                budget = -1.0
            else:
                budget += mu - (2 * far / amp) / 2          # the eps_B part of w/2 goes into the coefficient below
        if H.get("center_sib"):      # per-boundary centred offsets: (k-1) Delta_1 -> (k-1) Delta_1 / 2
            budget += (k - 1) * mu * sib / 2
        if H.get("center1"):         # one-sided centred: interior theta = 0, split of G unknown in [0, G]:
            g_ss = p / (2 * (A * nu - 1))          # steady-state deficit fraction with end-only deficits
            budget += mu / 2 + rstar - g_ss / 2     # replaces mu + r* by (mu + g)/2
        if H.get("center"):          # centred design offset: per-child shift |O_L + e - o| <= (mu + U)/2
            budget += mu / 2 + (kap * mu / (A * nu - 1) / 2 if kap is not None else 0.0)
        if budget <= 0 or epsF <= 0:
            continue
        epsB = tol * budget / (ETA * (1 + (1 / (4 * (A * nu - 1)) if H.get('center2') else 0.0) + ((1 / (2 * A * nu * (1 - 3 / (2 * A * nu)))) if H.get('dyn2') and A * nu > 1.5 else 0.0)) + ((kap / (2 * (A * nu - 1))) * (0.5 if H.get('center') else 1.0) if kap is not None else 0.0))
        lb = lgm_bulk(epsB, rounds)
        if H.get("fexp") is not None:   # hypothetical fringe scaling f = 7934 (J/190000)^fexp / fdiv
            f = 7934 * (1 / (epsF * 190000)) ** H["fexp"] / H.get("fdiv", 1.0)
        else:
            f = CAL * a_f * (1 / epsF) ** p_f / H.get("fdiv", 1.0)
        lf = math.log2(f / f_over_m)
        if H.get("split"):
            lf = H.get("split_floor", 0.0)
        lgm = max(lb, lf, 2 * (x + y) if H.get("thm51", False) else 0.0)
        if best is None or lgm < best["lgm"]:
            best = dict(lgm=lgm, lgm_B=lb, lgm_F=lf, d=d, epsB=epsB, epsF=epsF, f=f, mu=mu)
    if best is None or not math.isfinite(best["lgm"]):
        return None
    q = math.ceil(best["lgm"] - 1e-9)
    spb = (x + y) / (x * z)
    if H.get("stage", "").startswith("band"):
        # runfix: merge runs are the children's F-block rows p m / 2 (not the fringe f), with the
        # alignment cost of unaligned runs (one extra depth-l block merge): S(q) - S(l) + l
        run = (lambda qq: -(p * 2.0 ** qq / 2)) if H.get("runfix") else (lambda qq: best["f"])
        q = min(range(q, q + 4), key=lambda qq: stage_depth(qq, H, k, run(qq), best["epsB"]))
        st = stage_depth(q, H, k, run(q), best["epsB"])
        best.update(q=q, spb=spb, x=x, y=y, z=z, stage=st, ideal=st * spb)
    else:
        best.update(q=q, spb=spb, x=x, y=y, z=z, stage=stage_depth(q, H, k, best["f"]),
                    ideal=stage_depth(best["lgm"], H, k, best["f"]) * spb)
    best["cost"] = best["stage"] * spb
    return best


def tail_frac(q, W):
    """walk-bound round-1 tail beyond distance W of the level, as a fraction of m n (per cut):
    max_p [sqrt(pi/2) sqrt(m p(1-p)) + sqrt(2 p' H(p) m) - W p] / m  (WALK-BOUND.md sec. 3 with the
    W-shifted sum over S). It decays only like 1/W: the adversary can fill a few output columns."""
    m = 2.0 ** q
    ps = np.geomspace(1e-14, 0.5, 2000)
    H = -(ps * np.log(ps) + (1 - ps) * np.log1p(-ps))
    v = math.sqrt(math.pi / 2) * np.sqrt(m * ps * (1 - ps)) + np.sqrt(2 * ps * H * m) - W * ps
    return max(float(v.max()), 0.0) / m


def band(q, H, epsB=None):
    """band repair at every cut instead of the third sort: one band sort of height 2W. W is the least
    power of two with d(2^q) + 2 tail(W) <= eps_B (or W = cW sqrt(m) when H['cW'] is given)."""
    if "cW" in H or epsB is None:
        w = math.ceil(math.log2(2 * H.get("cW", 3.0)) + q / 2)
        return S(min(w, q))
    room = epsB - math.exp(float(np.interp(q, _LS, _LD)))
    if room <= 0:
        return math.inf
    for lw in range(4, q + 1):
        if 2 * tail_frac(q, 2.0 ** lw) <= room:
            return S(min(lw + 1, q))
    return S(q)


def merge_first(q, f):
    """first sort on columns made of sorted runs of length >= f + 1 (children's F blocks): skip the
    first floor(lg(f+1)) merge levels of Batcher's sort. A negative f means runfix: run length -f,
    unaligned, so pay one extra depth-l block merge."""
    if f < 0:
        l = min(q, int(math.floor(math.log2(-f))))
        return S(q) - S(l) + l
    return S(q) - S(min(q, int(math.floor(math.log2(f + 1)))))


def stage_depth(q, H, k, f=1.0, epsB=None):
    mode = H.get("stage", "sort3")
    if mode == "band":                        # sort, scramble, sort, scramble, band repair
        return 2 * S(q) + band(q, H, epsB)
    if mode == "band+merge":                  # merge first sort, full second sort, band repair
        return merge_first(q, f) + S(q) + band(q, H, epsB)
    if mode == "merge1r":                     # merge first sort only (refined run length f + 1)
        return merge_first(q, f) + 2 * S(q)
    if mode == "sort3":
        return 3 * S(q)
    if mode == "sort2":                       # one-round separator or idealized repair, plus R
        return 2 * S(q) + H.get("R", 0.0)
    if mode == "merge1":                      # first sort replaced by a merge of k+1 sorted runs
        return math.ceil(math.log2(k + 1)) * q + 2 * S(q)
    if mode == "mergeall":                    # every sort a merge of k+1 runs (most optimistic)
        return 3 * math.ceil(math.log2(k + 1)) * q
    if mode == "periodic":                    # one precise stage (sort3 at q_prec) every P stages
        P, qp = H["P"], H["q_prec"]
        return ((P - 1) * 3 * S(q) + 3 * S(qp)) / P
    raise ValueError(mode)


def sweep(H, xs=range(2, 9), ys=range(1, 13), zs=range(1, 9)):
    res = [r for x in xs for y in ys for z in zs if (r := evaluate(x, y, z, H)) is not None]
    return min(res, key=lambda r: (r["cost"], r["ideal"])) if res else None


def fmt(name, r, flag=""):
    if r is None:
        return f"  {name:44s} infeasible"
    return (f"  {name:44s} {r['cost']:7.1f} ({r['ideal']:6.1f})  ({r['x']},{r['y']},{r['z']}) q={r['q']:2d} "
            f"[B {r['lgm_B']:5.1f}, F {r['lgm_F']:5.1f}]  epsB {r['epsB']:.1e} epsF {r['epsF']:.1e} "
            f"f {r['f']:8.0f} spb {r['spb']:.3f}{flag}")


HYP = [
    ("H0  status quo (dF 1/8)", {}),
    ("H0' status quo at (4,5,3) only", {"_fixed": (4, 5, 3)}),
    ("H1a dF = 1/5 (fit)", {"dF": 1 / 5}),
    ("H1b dF = 1/4 (extrapolated fit)", {"dF": 1 / 4}),
    ("H1c dF = 1/3 (extrapolated fit)", {"dF": 1 / 3}),
    ("H2  r* = 0 (two-sided invariant)", {"rstar": 0.0}),
    ("H3  fringe idealized away (upper bound)", {"split": True}),
    ("F1  fringe f / 10 (same J scaling)", {"fdiv": 10.0}),
    ("F2  fringe f ~ J^0.25 (anchored at 7934)", {"fexp": 0.25}),
    ("F3  fringe f ~ J^0.25, / 10", {"fexp": 0.25, "fdiv": 10.0}),
    ("H4a two sorts, idealized repair R = 0", {"stage": "sort2"}),
    ("H4b two sorts, repair R = 2(q+1) (two merges)", {"stage": "sort2", "Rq": 2}),
    ("H4c one-round separator (2 sorts, E1 precision)", {"stage": "sort2", "rounds": 1}),
    ("H5a first sort -> merge of k+1 runs", {"stage": "merge1"}),
    ("H5b all sorts -> merges (optimistic)", {"stage": "mergeall"}),
    ("H6a tolerance x10 (larger-error invariant)", {"tol": 10.0}),
    ("H6b tolerance x100", {"tol": 100.0}),
    ("H6c tolerance x1000", {"tol": 1000.0}),
    ("C1  dF 1/4 + split fringe", {"dF": 1 / 4, "split": True}),
    ("C2  r* = 0 + split fringe", {"rstar": 0.0, "split": True}),
    ("C3  r* = 0 + dF 1/4 + split", {"rstar": 0.0, "dF": 1 / 4, "split": True}),
    ("C4  split + two sorts (R = 0)", {"split": True, "stage": "sort2"}),
    ("C5  r* = 0 + split + two sorts", {"rstar": 0.0, "split": True, "stage": "sort2"}),
    ("C6  dF 1/4 + r* = 0 + split + two sorts", {"dF": 1 / 4, "rstar": 0.0, "split": True, "stage": "sort2"}),
    ("C7  dF 1/4 + split + merge first sort", {"dF": 1 / 4, "split": True, "stage": "merge1"}),
    ("C8  tol x100 + split", {"tol": 100.0, "split": True}),
    ("C10 f/10 + two sorts", {"fdiv": 10.0, "stage": "sort2"}),
    ("C11 f/10 + r* = 0 + two sorts", {"fdiv": 10.0, "rstar": 0.0, "stage": "sort2"}),
    ("C12 f~J^0.25 + two sorts", {"fexp": 0.25, "stage": "sort2"}),
    ("C13 f/10 + merge first sort", {"fdiv": 10.0, "stage": "merge1"}),
    ("R1  band repair (walk-bound 1/W tail) for the third sort", {"stage": "band"}),
    ("R2  band repair, optimistic W = 3 sqrt m", {"stage": "band", "cW": 3.0}),
    ("R3  merge first sort (runs f+1) only", {"stage": "merge1r"}),
    ("R4  merge first + band (1/W tail)", {"stage": "band+merge"}),
    ("R5  R4 + fringe f / 2.4", {"stage": "band+merge", "fdiv": 2.4}),
    ("R6  R4 + r* = 0", {"stage": "band+merge", "rstar": 0.0}),
    ("R7  R4 + r* = 0 + f / 2.4", {"stage": "band+merge", "rstar": 0.0, "fdiv": 2.4}),
    ("R8  band + r* = 0", {"stage": "band", "rstar": 0.0}),
    ("R9  R4 + tolerance x4", {"stage": "band+merge", "tol": 4.0}),
    ("C9  tol x100 + split + two sorts", {"tol": 100.0, "split": True, "stage": "sort2"}),
]


def run(H):
    H = dict(H)
    if H.pop("Rq", None):
        # R depends on q: evaluate with R = 2(q+1) by a fixed point over q
        best = None
        for qguess in range(8, 40):
            Hq = dict(H, R=2 * (qguess + 1))
            r = sweep(Hq)
            if r and r["q"] == qguess and (best is None or r["cost"] < best["cost"]):
                best = r
        return best
    fixed = H.pop("_fixed", None)
    if fixed:
        return evaluate(*fixed, H)
    return sweep(H)


def gate(base, key, tgt, lo=1.0, hi=1e6):
    """least multiplier (geometric bisection) with best cost < tgt; cost is monotone in the knob."""
    def ok(v):
        r = sweep(dict(base, **{key: v}))
        return r if r and r["cost"] < tgt else None
    rh = ok(hi)
    if not rh:
        return None
    for _ in range(18):
        mid = math.sqrt(lo * hi)
        r = ok(mid)
        if r:
            hi, rh = mid, r
        else:
            lo = mid
    return hi, rh


def main():
    r0 = evaluate(4, 5, 3, {})
    print("Calibration at (4,5,3), dF = 1/8, three sorts (accepted 789.75):")
    print(fmt("model", r0) + f"  delta {r0['d']:.2e} mu {r0['mu']:.3e}")
    print("\nBest integer schedule per hypothetical: cost (continuous-q cost)  (x,y,z) q [bulk, fringe floors]")
    for name, H in HYP:
        flag = "  [extrapolated fringe fit]" if H.get("dF") in (1 / 4, 1 / 3) and not H.get("split") else ""
        print(fmt(name, run(H), flag), flush=True)
    print("\nPeriodic restoration (idea 3): cheap stages at tolerance T, one precise 3-sort stage at q = 26 every P")
    for T in (100.0, 1000.0):
        for P in (2, 4, 8):
            r = sweep(dict(tol=T, split=True, stage="periodic", P=P, q_prec=26))
            print(fmt(f"T = {T:g}, P = {P}, split fringe", r), flush=True)



def gates():
    print("\nGates: least multiplier reaching each target (geometric bisection; model)")
    rows = [("fringe f / c, three sorts", {}, "fdiv"),
            ("fringe f / c, two sorts", {"stage": "sort2"}, "fdiv"),
            ("fringe f / c, r* = 0, three sorts", {"rstar": 0.0}, "fdiv"),
            ("eps_B tolerance T, fringe idealized away", {"split": True}, "tol"),
            ("eps_B tolerance T, fringe f/100", {"fdiv": 100.0}, "tol"),
            ("eps_B tolerance T, f/100, two sorts", {"fdiv": 100.0, "stage": "sort2"}, "tol")]
    for label, base, key in rows:
        for tgt in (500, 300, 200):
            g = gate(base, key, tgt)
            if g:
                v, r = g
                print(f"  {label:42s} < {tgt}: {key} >= {v:9.1f}  ({r['cost']:.1f} at ({r['x']},{r['y']},{r['z']}), "
                      f"q = {r['q']} [B {r['lgm_B']:.1f}, F {r['lgm_F']:.1f}])", flush=True)
            else:
                print(f"  {label:42s} < {tgt}: not reached for {key} <= 1e6", flush=True)


if __name__ == "__main__":
    import sys
    if sys.argv[1:] != ["gates"]:
        main()
    gates()
