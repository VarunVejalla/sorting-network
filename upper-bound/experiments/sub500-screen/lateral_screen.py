"""Lateral line repair priced in the R1-era screen (experiments/lateral-line/PLAN.md; COMPOSITION.md sec. 5).

Model only. Per schedule (x, y, z) and delta:
  (4.2-L) order-0 budget  mu A nu - mu - (k-1) mu sib - mu d A^2 k - r* - 0.1 mu  >=  eps2 eta
          (eps2 = distance-2 + shift spill; energy method gives ~1e-7 of mn, modelled as EPS2);
  (O-L)   residual fits the fringe rows: m g >= t sqrt(2 lam), lam = side eps_B m / (A nu),
          g = f/m - (L mu + (3 mu + r* + eps2) / (A nu))  ->  eps_B <= m g^2 A nu / (2 side t^2);
  bulk    lgm_bulk(eps_B) <= lg m (separator precision);
  fringe  f needed at eps_F / L with delta_F / L per node (L = 2), f <= g' m;
  band    the band's escapes beyond W are far spill: W from the order-0 budget, not from eps_B;
  cost    stage(q) + 2 (q + 1) per stage (two merge phases).
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import screen as Sc  # noqa: E402

L, SIDE, T = 2.0, 0.5, 8.0


def evaluate(x, y, z, H):
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    if A * nu <= 1 or x < 2:
        return None
    dF = H.get("dF", 1 / 8)
    p = (A * nu * k - 1) / (A * A * k * k)
    mu = (1 - 2 ** -10) * min(0.5 * (dF / L) * p, nu / (A * k * k))
    rstar = H.get("rstar", 1.0) * (k - 1) / (2 * A * A * k * k)
    eps2 = H.get("eps2", 1e-6)
    a_f, p_f = Sc.floor_fit(dF)
    fom = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
    g = fom - (L * mu + (3 * mu + rstar + eps2) / (A * nu))
    if g <= 0:
        return None
    best = None
    dmax = 1 / (k * A) * (1 - 1e-9)
    for d in np.geomspace(dmax * 1e-6, dmax, 120):
        sib = d * k * A * A / (1 - (d * k * A) ** 2)
        budget = mu * A * nu - mu - (k - 1) * mu * sib - mu * d * A * A * k - rstar - 0.1 * mu
        if budget < eps2 * Sc.ETA:
            continue
        epsF = A * nu * d - A * A * k * d * d
        if epsF <= 0:
            continue
        f = Sc.CAL * a_f * (L / epsF) ** p_f / H.get("fdiv", 1.0)
        lf = math.log2(f / g) if not H.get("split") else 0.0
        # smallest lg m >= lf with lgm_bulk(eps_B(m)) <= lg m, eps_B(m) = m g^2 A nu / (2 side T^2)
        lm = max(lf, 6.0)
        while lm < 60:
            epsB = min(0.25, (2 ** lm) * g * g * A * nu / (2 * SIDE * T * T))
            if Sc.lgm_bulk(epsB, 2) <= lm:
                break
            lm += 0.05
        if best is None or lm < best["lgm"]:
            best = dict(lgm=lm, d=d, epsB=epsB, budget=budget, f=f, epsF=epsF, mu=mu)
    if best is None:
        return None
    q = math.ceil(best["lgm"] - 1e-9)
    spb = (x + y) / (x * z)
    run = -(p * 2.0 ** q / 2) if H.get("runfix", True) else best["f"]
    mode = H.get("stage", "sort3")
    if mode.startswith("band"):
        st = Sc.stage_depth(q, H, k, run, best["budget"] / Sc.ETA) + 2 * (q + 1)
    else:
        st = Sc.stage_depth(q, H, k, run) + 2 * (q + 1)
    best.update(q=q, x=x, y=y, z=z, spb=spb, stage=st, cost=st * spb)
    return best


def sweep(H):
    best = None
    for x in range(2, 9):
        for y in range(1, 13):
            for zz in range(1, 9):
                r = evaluate(x, y, zz, H)
                if r and math.isfinite(r["cost"]) and (best is None or r["cost"] < best["cost"]):
                    best = r
    return best


if __name__ == "__main__":
    for name, H in [("lateral, 3 sorts", {}),
                    ("lateral, 3 sorts, fringe /5.8", {"fdiv": 5.8}),
                    ("lateral, band + merge", {"stage": "band+merge"}),
                    ("lateral, band + merge, fringe /5.8", {"stage": "band+merge", "fdiv": 5.8}),
                    ("lateral, band + merge, fringe /5.8, eps2 1e-7", {"stage": "band+merge", "fdiv": 5.8, "eps2": 1e-7}),
                    ("lateral, band + merge, fringe /5.8, r* = 0", {"stage": "band+merge", "fdiv": 5.8, "rstar": 0.0}),
                    ("lateral, band + merge, fringe away", {"stage": "band+merge", "split": True})]:
        r = sweep(H)
        if r:
            print(f"{name:50s} {r['cost']:7.1f}  ({r['x']},{r['y']},{r['z']}) q {r['q']}  eps_B {r['epsB']:.2e}  f {r['f']:.0f}  stage {r['stage']:.0f}", flush=True)
        else:
            print(name, "infeasible")
