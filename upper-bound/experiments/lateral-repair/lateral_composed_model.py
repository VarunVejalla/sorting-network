#!/usr/bin/env python3
"""UB-20 cost model with the composition corrections of COMPOSITION.md sec. 5.

Parameter model only.  Differences from lateral_certfloor_model.py:

  (4.2-L)  the separator's adjacent spill is removed from (4.2); only the distance-2 spill
           eps_2 = c2 * eps_B^2 remains (heuristic, ../tapered/NOTES.md sec. 2.2);
  (4.4-L)  each node may use fringe fraction delta_F / L (L = fringe-load factor from sibling drift),
           while Property F is certified at delta_F (fringe floors from fringe_general_screen.py);
  (4.5-L)  fringe misses of L siblings' far loads reach one child, so eps_F is needed at eps_F/L;
  (O-L)    the per-column residual must fit the fringe rows together with the co-resident loads
           (L far loads, drift mean, sibling hiding, distance-2 spill): m g >= t sqrt(2 lam);
           overflow is then treated as negligible in (4.5).  L = 2 for even k (review, 2026-10-18);
  cost     3 T(lg m) + 2 (lg m + 1) per stage (two full-column merge phases).

Run:  python -I lateral_composed_model.py [variant-substring ...]
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
sys.path.insert(0, HERE)
import exchange_rate as E  # noqa: E402
from lateral_certfloor_model import FLOOR  # noqa: E402


def evaluate(eps_sep, L, t, c2, x, y, z, P):
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    shape = np.broadcast_shapes(np.shape(eps_sep), np.shape(x))
    eps_sep = np.broadcast_to(eps_sep, shape)
    P2 = dict(P); P2["dF"] = P["dF"] / L; P2["f_floor"] = 1.0; P2["cF"] = 1e300
    eps2 = EPS2_FRAC * eps_sep if EPS2_FRAC > 0 else c2 * eps_sep ** 2
    _, ideal0, _, det = E.evaluate(eps2, x, y, z, P2)                     # (4.2-L), (4.4-L), (4.5)
    Af, pf = FLOOR[P["dF"]]
    with np.errstate(all="ignore"):
        # (4.5-L): a child receives the fringe misses of L siblings' far loads, so the fringe precision
        # must be eps_F / L, certified at the combined fraction delta_F.
        f_need = Af * (L / det["epsF"]) ** pf
        fom = E.f_over_m(k, A, nu)
        lgm_F = np.log2(f_need / fom)
        # (O-L): the fringe rows also hold L siblings' far loads (L mu per row of height), the drift mean
        # D/n (u's residual outsiders, sibling hiding ~2 mu, slack, distance-2 spill), and the residual
        # tail t sqrt(2 lam).  Need m * g >= t sqrt(2 lam), g = f/m minus the co-resident loads.
        mu = det["mu"]
        slack_v = P["slack"] * (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
        g = fom - (L * mu + (3 * mu + slack_v + eps2) / (A * nu))
        lgm_O = np.where(g > 0, np.log2(2 * t * t * P["side"] * eps_sep / (A * nu * np.maximum(g, 1e-300) ** 2)), np.inf)
    lgm_B = E.lgm_for(eps_sep, P["rounds"])
    lgm = np.maximum.reduce([lgm_F, lgm_B, lgm_O, 2 * (x + y) + 0 * eps_sep])
    sorts = 2 if P["rounds"] == 1 else 3
    with np.errstate(all="ignore"):
        ok = np.isfinite(ideal0) & np.isfinite(lgm_F)
        spb = det["spb"]
        ideal = np.where(ok, (sorts * lgm * (lgm + 1) / 2 + 2 * (lgm + 1)) * spb, np.inf)
        Lw = np.ceil(lgm - 1e-9) + 1
        win = np.where(ok, (sorts * Lw * (Lw + 1) / 2 + 2 * Lw) * spb, np.inf)
    return lgm, ideal, win, dict(lgm_B=lgm_B, lgm_F=lgm_F, lgm_O=lgm_O, spb=spb, f=f_need, epsF=det["epsF"])


def best(L, t, c2, P, step=0.5, wstep=0.5, integer=False):
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    ws = np.arange(2, 30.01, wstep)
    X, Z, D, W = np.meshgrid(xs, zs, ds, ws, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(2.0 ** -W, L, t, c2, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return {kk: float(v[i]) for kk, v in dict(w=W, x=X, y=Y, z=Z, lgm=lgm, ideal=ideal, win=win, **det).items()}


# Distance-2 spill model: EPS2_FRAC > 0 means eps_2 = EPS2_FRAC * eps_B (e.g. 0.01, the one-round
# adversary in ../tapered/NOTES.md sec. 4); otherwise eps_2 = c2 * eps_B^2.
EPS2_FRAC = float(os.environ.get("EPS2_FRAC", "0"))

L4 = dict(side=0.5, sibmult=2.0, use43=False, slack=0.0)
VARIANTS = [
    ("S   slack removed", dict(dF=128 / 4095, slack=0.0)),
    ("L4' dF=1/16", dict(L4, dF=1 / 16)),
    ("L4' dF=1/8", dict(L4, dF=1 / 8)),
    ("L4' dF=1/5", dict(L4, dF=1 / 5)),
]
CASES = [("L=2 t=6", 2.0, 6.0), ("L=2 t=10", 2.0, 10.0)]


def main():
    names = sys.argv[1:]
    print(" variant          case      | ideal (win)  eps_B    eps_F    f rows   (x,y,z)          lg m [B, F, O]        spb")
    for name, kn in VARIANTS:
        if names and not any(nm in name for nm in names):
            continue
        P = dict(E.DEFAULT); P.update(kn)
        for cname, L, t in CASES:
            b = best(L, t, 1.0, P)
            bi = best(L, t, 1.0, P, integer=True)
            if b is None:
                print(f" {name:16s} {cname:9s} | infeasible", flush=True)
                continue
            wi = f"{bi['win']:5.0f}" if bi else "   - "
            print(f" {name:16s} {cname:9s} | {b['ideal']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['epsF']:.1e} {b['f']:7.0f}  "
                  f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f},{b['lgm_O']:4.1f}]  {b['spb']:.3f}", flush=True)


if __name__ == "__main__":
    main()
