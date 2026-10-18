#!/usr/bin/env python3
"""UB-20 gate: what a lateral (sibling) repair channel must achieve for a given slope.

Parameter model only (floats, no certificates).  Extends ../tapered/exchange_rate.py, which encodes
Chvatal DCS-TR-294 conditions (4.2)-(4.5) for trees with sort-based separators.

Lateral model.  A sort-based separator's bulk error at a cut is symmetric in mass when the block
size matches the key count: sum_c (X_c - r)_+ = sum_c (r - X_c)_+.  Keys can therefore be exchanged
between the two sibling blocks without changing either block's size.  Suppose a fixed lateral
repair network of depth G per stage cancels all but a fraction rho of the separator's symmetric bulk
spill.  The asymmetric terms (schedule slack, outsider-driven boundary shifts, sibling hiding) are
unchanged; only the separator term of (4.2) is scaled:

    (4.2)'  rho * side * eps_B + slack + mu*(...) <= mu*A*nu.

So the separator may run at eps_B = eps_tol / rho, where eps_tol is the old tolerance.  Fringe
conditions (4.4), (4.5), the fringe floor and (5.1) m >= (A k)^2 are unchanged.

Cost per stage = sorts * T(lg m) + G; slope = cost * stages-per-bit (x+y)/(x z).

Run:  python -I lateral_gate.py
"""
import os
import sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
import exchange_rate as E  # noqa: E402


def evaluate(eps_sep, rho, G, x, y, z, P):
    """Separator bulk error eps_sep, lateral residual fraction rho, lateral depth G per stage."""
    lgm, ideal, win, det = E.evaluate(rho * eps_sep, x, y, z, P)
    # E.evaluate sized m for bulk error rho*eps_sep; the separator only has to reach eps_sep.
    lgm_B = E.lgm_for(np.broadcast_to(eps_sep, np.shape(lgm)), P["rounds"])
    lgm = np.maximum(np.maximum(det["lgm_F"], lgm_B), 2 * (x + y))
    sorts = 2 if P["rounds"] == 1 else 3
    spb = det["spb"]
    ok = np.isfinite(ideal)
    ideal = np.where(ok, (sorts * lgm * (lgm + 1) / 2 + G) * spb, np.inf)
    Lw = np.ceil(lgm - 1e-9) + 1
    win = np.where(ok, (sorts * Lw * (Lw + 1) / 2 + G) * spb, np.inf)
    return lgm, ideal, win, dict(det, lgm_B=lgm_B)


def best(rho, G, P, step=0.5, wstep=1.0, integer=False):
    """Optimise jointly over (x, y, z) and the separator error eps_sep = 2^-w (one vectorised grid)."""
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    ws = np.arange(4, 40.01, wstep)
    X, Z, D, W = np.meshgrid(xs, zs, ds, ws, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(2.0 ** -W, rho, G, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return dict(obj=float(obj[i]), w=float(W[i]), x=float(X[i]), y=float(Y[i]), z=float(Z[i]),
                lgm=float(lgm[i]), lgm_B=float(det["lgm_B"][i]), lgm_F=float(det["lgm_F"][i]),
                spb=float(det["spb"][i]), ideal=float(ideal[i]), win=float(win[i]))


VARIANTS = [
    ("V0  Chvatal as is", {}),
    ("S   slack removed (UB-12)", dict(slack=0.0)),
    ("L4  locality + dF=1/2 + no (4.3) + no slack", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False, slack=0.0)),
]
RHOS = [1.0, 1e-1, 1e-2, 1e-3, 1e-4, 1e-6]
FLOORS = [92160.0, 1024.0, 64.0]


def main():
    for f_floor in FLOORS:
        for G in (0.0, 60.0):
            print(f"\n===== f_floor = {f_floor:.0f} rows, lateral depth G = {G:.0f} per stage (2-round separator) =====")
            print(" variant                                       rho    | best ideal (win)  eps_sep  (x,y,z)          lg m [B, F]   spb")
            for name, kn in VARIANTS:
                P = dict(E.DEFAULT); P.update(kn); P["f_floor"] = f_floor
                for rho in RHOS:
                    b = best(rho, G, P)
                    bi = best(rho, G, P, integer=True)
                    if b is None:
                        print(f" {name:44s} {rho:7.0e} | infeasible")
                        continue
                    wi = f"{bi['win']:5.0f}" if bi else "   - "
                    print(f" {name:44s} {rho:7.0e} | {b['ideal']:5.0f} ({wi})      2^-{b['w']:<4.1f} "
                          f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f}]  {b['spb']:.3f}")


if __name__ == "__main__":
    main()
