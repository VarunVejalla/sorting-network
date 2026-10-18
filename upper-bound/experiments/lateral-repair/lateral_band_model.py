#!/usr/bin/env python3
"""UB-20 combined model: lateral bulk repair plus band balancing on the fringe.

Parameter model only (heuristic, not a proof).  Builds on lateral_selfconsistent.py.

Bulk: R lateral rounds, residual rho = (2 sqrt(C/(pi lam)))^R with lam = side*eps_B*m/(A nu);
      cost 2R(lg m + 1) layers (full-column merges in two phases: even, then odd boundaries).
Fringe: the two-round fringe law eps_F(f) = 1/(cF f) is improved by RF band-balancing rounds on the
      fringe bands (height h = 4f), each after the first dividing misses by gF (measured 3-6 in
      sim_band_fringe.out; default 3).  Cost RF*lg(8 f) layers, f = m * f_over_m(k, A, nu) rows.
      f must still exceed f_floor (the proof-route floor; 64 models a redone proof).

Run:  python -I lateral_band_model.py [f_floor]
"""
import os
import sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
import exchange_rate as E  # noqa: E402


def evaluate(eps_sep, C, R, RF, gF, x, y, z, P):
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    shape = np.broadcast_shapes(np.shape(eps_sep), np.shape(x))
    gain = np.where(RF > 0, gF ** max(RF - 1, 0), 1.0)
    P2 = dict(P); P2["cF"] = P["cF"] * gain
    _, _, _, det0 = E.evaluate(np.zeros(shape), x, y, z, P2)
    lgm_B = E.lgm_for(np.broadcast_to(eps_sep, shape), P["rounds"])
    lgm = np.maximum(np.maximum(det0["lgm_F"], lgm_B), 2 * (x + y))
    m = 2.0 ** lgm
    lam = P["side"] * eps_sep * m / (A * nu)
    rho = np.minimum(1.0, 2.0 * np.sqrt(C / (np.pi * np.maximum(lam, 1e-300)))) ** R
    _, ideal, _, det = E.evaluate(rho * eps_sep, x, y, z, P2)
    sorts = 2 if P["rounds"] == 1 else 3
    with np.errstate(all="ignore"):
        f_rows = m * E.f_over_m(k, A, nu)
        GF = RF * np.log2(np.maximum(8 * f_rows, 2))
        G = 2 * R * (lgm + 1) + GF   # two phases (even, odd boundaries) per lateral round
        ok = np.isfinite(ideal)
        spb = det["spb"]
        ideal = np.where(ok, (sorts * lgm * (lgm + 1) / 2 + G) * spb, np.inf)
        Lw = np.ceil(lgm - 1e-9) + 1
        GFw = RF * np.ceil(np.log2(np.maximum(8 * f_rows, 2)))
        win = np.where(ok, (sorts * Lw * (Lw + 1) / 2 + 2 * R * Lw + GFw) * spb, np.inf)
    return lgm, ideal, win, dict(lgm_B=lgm_B, lgm_F=det0["lgm_F"], spb=spb, rho=rho, f=f_rows, G=G)


def best(C, R, RF, gF, P, step=0.5, wstep=1.0, integer=False):
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    ws = np.arange(3, 34.01, wstep)
    X, Z, D, W = np.meshgrid(xs, zs, ds, ws, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(2.0 ** -W, C, R, RF, gF, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return dict(w=float(W[i]), x=float(X[i]), y=float(Y[i]), z=float(Z[i]), lgm=float(lgm[i]),
                lgm_B=float(det["lgm_B"][i]), lgm_F=float(det["lgm_F"][i]), spb=float(det["spb"][i]),
                rho=float(det["rho"][i]), f=float(det["f"][i]), G=float(det["G"][i]),
                ideal=float(ideal[i]), win=float(win[i]))


VARIANTS = [
    ("S   slack removed (UB-12)", dict(slack=0.0)),
    ("L4  locality + dF=1/2 + no (4.3) + no slack", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False, slack=0.0)),
]
CASES = [(1, 1, 0), (1, 1, 2), (1, 1, 4), (1, 1, 6), (8, 1, 4), (1, 2, 4), (8, 2, 6)]


def main():
    f_floor = float(sys.argv[1]) if len(sys.argv) > 1 else 64.0
    gF = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    print(f"===== f_floor = {f_floor:.0f} rows, fringe gain per extra band round gF = {gF} (2-round separator) =====")
    print(" variant                                       C  R RF | ideal (win)  eps_sep   rho      f rows   G    (x,y,z)          lg m [B, F]   spb")
    for name, kn in VARIANTS:
        P = dict(E.DEFAULT); P.update(kn); P["f_floor"] = f_floor
        for C, R, RF in CASES:
            b = best(C, R, RF, gF, P)
            bi = best(C, R, RF, gF, P, integer=True)
            if b is None:
                print(f" {name:44s} {C:2d} {R:2d} {RF:2d} | infeasible", flush=True)
                continue
            wi = f"{bi['win']:5.0f}" if bi else "   - "
            print(f" {name:44s} {C:2d} {R:2d} {RF:2d} | {b['ideal']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['rho']:.2e} {b['f']:9.0f} {b['G']:5.0f} "
                  f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f}]  {b['spb']:.3f}", flush=True)


if __name__ == "__main__":
    main()
