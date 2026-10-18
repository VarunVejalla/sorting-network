#!/usr/bin/env python3
"""UB-20 cost model with the provable spill-locality floor (SPILL-LOCALITY.md).

Parameter model only.  Same conditions as lateral_composed_model.py (COMPOSITION.md sec. 5 with the
review fixes), except that the distance-2 / shift error is the union-bound floor

    eps_2(m) = kappa * 2 ln(m+1) / m,     kappa ~ 1 + 1/(A nu)  (distance-2 spill + shift errors),

which depends on the column height m, together with the margin condition m >= 1.04 k^4 (1 + ln m).
Because eps_2 depends on m, the search runs over a ladder of lg m values and keeps, for each
(k, A, nu, eps_B), the smallest m satisfying every condition.

Run:  python -I lateral_floor_model.py [kappa] [variant-substring ...]
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


def search(P, kappa, L=2.0, t=6.0, integer=False, step=0.5, wstep=0.5):
    if integer:
        xs, zs, ds = np.arange(1, 13.0), np.arange(1, 13.0), np.arange(1, 17.0)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    X, Z, D, G = np.meshgrid(xs, zs, ds, LADDER, indexing="ij")
    Y = Z + D
    k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
    m = 2.0 ** G
    eps2 = kappa * 2 * np.log(m + 1) / m
    P2 = dict(P); P2["dF"] = P["dF"] / L; P2["f_floor"] = 1.0; P2["cF"] = 1e300
    _, ideal0, _, det = E.evaluate(eps2, X, Y, Z, P2)
    Af, pf = FLOOR[P["dF"]]
    with np.errstate(all="ignore"):
        fom = E.f_over_m(k, A, nu)
        lgm_F = np.log2(Af * (L / det["epsF"]) ** pf / fom)
        lgm_loc = np.log2(1.04 * k ** 4 * (1 + G * math.log(2)))
        base_ok = np.isfinite(ideal0) & (G >= lgm_F) & (G >= 2 * (X + Y)) & (G >= lgm_loc)
        slack_v = P["slack"] * (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
        g = fom - (L * det["mu"] + (3 * det["mu"] + slack_v + eps2) / (A * nu))
    spb = det["spb"]
    best = None
    for w in np.arange(2, 30.01, wstep):
        eB = 2.0 ** -w
        lgm_B = float(E.lgm_for(np.array([eB]), P["rounds"])[0])
        with np.errstate(all="ignore"):
            lgm_O = np.where(g > 0, np.log2(2 * t * t * P["side"] * eB / (A * nu * np.maximum(g, 1e-300) ** 2)), np.inf)
        ok = base_ok & (G >= lgm_B) & (G >= lgm_O)
        sorts = 2 if P["rounds"] == 1 else 3
        if integer:
            Lw = np.ceil(G - 1e-9) + 1
            cost = (sorts * Lw * (Lw + 1) / 2 + 2 * Lw) * spb
        else:
            cost = (sorts * G * (G + 1) / 2 + 2 * (G + 1)) * spb
        cost = np.where(ok, cost, np.inf)
        i = np.unravel_index(np.argmin(cost), cost.shape)
        if np.isfinite(cost[i]) and (best is None or cost[i] < best["obj"]):
            best = dict(obj=float(cost[i]), w=float(w), x=float(X[i]), y=float(Y[i]), z=float(Z[i]),
                        lgm=float(G[i]), eps2=float(eps2[i]), epsF=float(det["epsF"][i]), spb=float(spb[i]),
                        lgm_B=lgm_B, lgm_F=float(lgm_F[i]), lgm_loc=float(lgm_loc[i]), lgm_O=float(lgm_O[i]))
    return best


L4 = dict(side=0.5, sibmult=2.0, use43=False, slack=0.0)
VARIANTS = [
    ("S   slack removed", dict(dF=128 / 4095, slack=0.0)),
    ("L4' dF=1/16", dict(L4, dF=1 / 16)),
    ("L4' dF=1/8", dict(L4, dF=1 / 8)),
    ("L4' dF=1/5", dict(L4, dF=1 / 5)),
]


def main():
    args = sys.argv[1:]
    kappa = float(args[0]) if args and args[0].replace(".", "").isdigit() else 1.7
    names = args[1:] if args and args[0].replace(".", "").isdigit() else args
    print(f"kappa = {kappa}: eps_2 = kappa * 2 ln(m+1)/m; L = 2, t = 6")
    print(" variant          | ideal (win)  eps_B    eps_2    eps_F    (x,y,z)          lg m [B, F, loc, O]")
    for name, kn in VARIANTS:
        if names and not any(nm in name for nm in names):
            continue
        P = dict(E.DEFAULT); P.update(kn)
        b = search(P, kappa)
        bi = search(P, kappa, integer=True)
        if b is None:
            print(f" {name:16s} | infeasible", flush=True)
            continue
        wi = f"{bi['obj']:5.0f}" if bi else "   - "
        print(f" {name:16s} | {b['obj']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['eps2']:.1e}  {b['epsF']:.1e}  "
              f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.2f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f},{b['lgm_loc']:4.1f},{b['lgm_O']:4.1f}]",
              flush=True)


if __name__ == "__main__":
    main()
