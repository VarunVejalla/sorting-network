#!/usr/bin/env python3
"""UB-20 model with the fringe height tied to the precision each design needs.

Parameter model only.  Replaces the fixed f_floor of ../tapered/exchange_rate.py by the smallest
fringe height that the F2ROUND two-round proof route certifies at precision eps_F = 1/J, fitted to
fringe_general_screen.py (fgen_J*.out; a float screen, to be re-certified):

    f_floor(J, delta) = A_delta * J^p_delta
    delta = 128/4095 : A = 6.41, p = 0.518   (J = 2^10 .. 2^16: 234, 474, 979, 2016 rows)
    delta = 1/16     : A = 7.43, p = 0.523   (2^12 .. 2^16: 576, 1192, 2457)
    delta = 1/8      : A = 14.79, p = 0.494  (2^12 .. 2^16: 875, 1915, 3447)
    delta = 1/5      : A = 36.91, p = 0.454  (2^12 .. 2^16: 1662, 2836, 5851)

The route cannot give delta = 1/2 (its R1a Chernoff step needs Delta + 1 > e*delta*f), so the L4
variants below use delta_F in {128/4095, 1/16, 1/8} instead of the tapered study's 1/2.

Lateral repair: one round, two merge phases (cost 2(lg m + 1)), residual
rho = min(1, 2 sqrt(C/(pi lam))); C = 25.3 is the provable constant (LATERAL-LEMMA.md),
C = 0.5 the worst simulated adversary.

Run:  python -I lateral_certfloor_model.py
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
import exchange_rate as E  # noqa: E402

FLOOR = {128 / 4095: (6.41, 0.518), 1 / 16: (7.43, 0.523), 1 / 8: (14.79, 0.494), 1 / 5: (36.91, 0.454)}


def evaluate(eps_sep, C, R, x, y, z, P):
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    shape = np.broadcast_shapes(np.shape(eps_sep), np.shape(x))
    P0 = dict(P); P0["f_floor"] = 1.0; P0["cF"] = 1e300          # take eps_F only from the model
    # eps_F from the largest delta that (4.2) allows at the design's separator precision.  (Until
    # 2026-10-18 this used eps_B = 0 here, which overstated eps_F; see walk-bound/FRINGE-CERT.md sec. 1.)  With
    # lateral repair (R = 1) the true intrusion is rho * eps_sep <= eps_sep: conservative, and biased
    # against the lateral rows (their eps_F would rise at rho * eps_sep).
    _, _, _, det0 = E.evaluate(np.broadcast_to(eps_sep, shape) * np.ones(shape), x, y, z, P0)
    Af, pf = FLOOR[P["dF"]]
    with np.errstate(all="ignore"):
        f_need = Af * (1.0 / det0["epsF"]) ** pf
        lgm_F = np.log2(f_need / E.f_over_m(k, A, nu))
    lgm_B = E.lgm_for(np.broadcast_to(eps_sep, shape), P["rounds"])
    lgm = np.maximum(np.maximum(lgm_F, lgm_B), 2 * (x + y))
    m = 2.0 ** lgm
    lam = P["side"] * eps_sep * m / (A * nu)
    rho = np.minimum(1.0, 2.0 * np.sqrt(C / (np.pi * np.maximum(lam, 1e-300)))) ** R
    _, ideal, _, det = E.evaluate(rho * eps_sep, x, y, z, P0)    # feasibility of (4.2)'-(4.5)
    sorts = 2 if P["rounds"] == 1 else 3
    with np.errstate(all="ignore"):
        ok = np.isfinite(ideal) & np.isfinite(lgm_F)
        spb = det["spb"]
        ideal = np.where(ok, (sorts * lgm * (lgm + 1) / 2 + 2 * R * (lgm + 1)) * spb, np.inf)
        Lw = np.ceil(lgm - 1e-9) + 1
        win = np.where(ok, (sorts * Lw * (Lw + 1) / 2 + 2 * R * Lw) * spb, np.inf)
    return lgm, ideal, win, dict(lgm_B=lgm_B, lgm_F=lgm_F, spb=spb, rho=rho, f=f_need, epsF=det0["epsF"])


def best(C, R, P, step=0.5, wstep=1.0, integer=False):
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    ws = np.arange(3, 34.01, wstep)
    X, Z, D, W = np.meshgrid(xs, zs, ds, ws, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(2.0 ** -W, C, R, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return {k: float(v[i]) for k, v in dict(w=W, x=X, y=Y, z=Z, lgm=lgm, ideal=ideal, win=win, **det).items()}


L4 = dict(side=0.5, sibmult=2.0, use43=False, slack=0.0)
VARIANTS = [
    ("V0  Chvatal as is", dict(dF=128 / 4095)),
    ("S   slack removed", dict(dF=128 / 4095, slack=0.0)),
    ("L4' dF=128/4095", dict(L4, dF=128 / 4095)),
    ("L4' dF=1/16", dict(L4, dF=1 / 16)),
    ("L4' dF=1/8", dict(L4, dF=1 / 8)),
    ("L4' dF=1/5", dict(L4, dF=1 / 5)),
]
CASES = [("no lateral", 1.0, 0), ("lateral C=25.3 (proved)", 25.3, 1), ("lateral C=0.5 (sims)", 0.5, 1)]


def main():
    names = sys.argv[1:]
    print(" variant            case                      | ideal (win)  eps_sep  eps_F    f rows  rho      (x,y,z)          lg m [B, F]   spb")
    for name, kn in VARIANTS:
        if names and not any(nm in name for nm in names):
            continue
        P = dict(E.DEFAULT); P.update(kn)
        for cname, C, R in CASES:
            b = best(C, R, P)
            bi = best(C, R, P, integer=True)
            if b is None:
                print(f" {name:18s} {cname:25s} | infeasible", flush=True)
                continue
            wi = f"{bi['win']:5.0f}" if bi else "   - "
            print(f" {name:18s} {cname:25s} | {b['ideal']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['epsF']:.1e} {b['f']:7.0f} {b['rho']:.2e} "
                  f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f}]  {b['spb']:.3f}", flush=True)


if __name__ == "__main__":
    main()
