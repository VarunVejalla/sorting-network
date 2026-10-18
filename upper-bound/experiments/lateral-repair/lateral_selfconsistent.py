#!/usr/bin/env python3
"""UB-20 self-consistent screen: one cross-sibling column-merge round with a statistically derived residual.

Parameter model only (heuristic, not a proof).  See lateral_gate.py for the base model.

Mechanism.  At parent u the separator spills P = side*eps_B*a(u) keys across each cut each way.
At the next stage each sibling's own separator places those keys, which are extreme for that
sibling, in the top (resp. bottom) band of its columns.  Pairing column c of v_j's top band with
column c of v_{j+1}'s bottom band and merging the two sorted segments (depth lg(2h) <= lg m + 1)
cancels min(p_c, q_c) misplaced pairs.  Residual sum_c |p_c - q_c|.

Heuristic residual.  The per-column mean is lam = P / n_v with n_v = a(v)/m columns and
a(v) ~ A*nu*a(u), so lam ~ side*eps_B*m/(A*nu).  If deviations of p_c and q_c from lam behave like
independent counts inflated by an entropy/adversary factor C (C=1: Poisson-like; larger C models
union-bound losses), the residual fraction is

    rho ~ min(1, sqrt(2*C/(pi*lam)) * sqrt(2)),   i.e. E|p-q| / lam for p, q ~ lam +/- sqrt(C lam).

rho*eps_B then enters (4.2) in place of eps_B.  Cost G = R*(lg m + 1) for R independent rounds
(each later round re-pairs columns; residual multiplies by the same factor, an optimistic model).

Run:  python -I lateral_selfconsistent.py
"""
import os
import sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
import exchange_rate as E  # noqa: E402


def evaluate(eps_sep, C, R, x, y, z, P):
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    # separator column height needed for eps_sep
    lgm_B = E.lgm_for(np.broadcast_to(eps_sep, np.broadcast_shapes(np.shape(eps_sep), np.shape(x))), P["rounds"])
    # fringe / (5.1) needs do not depend on eps; compute them with a dummy tiny eps
    _, _, _, det0 = E.evaluate(np.zeros(np.broadcast_shapes(np.shape(eps_sep), np.shape(x))), x, y, z, P)
    lgm = np.maximum(np.maximum(det0["lgm_F"], lgm_B), 2 * (x + y))
    m = 2.0 ** lgm
    lam = P["side"] * eps_sep * m / (A * nu)
    rho1 = np.minimum(1.0, 2.0 * np.sqrt(C / (np.pi * np.maximum(lam, 1e-300))))
    rho = rho1 ** R
    lg2, ideal, win, det = E.evaluate(rho * eps_sep, x, y, z, P)   # feasibility of (4.2)' etc.
    sorts = 2 if P["rounds"] == 1 else 3
    G = R * (lgm + 1)
    spb = det["spb"]
    ok = np.isfinite(ideal)
    ideal = np.where(ok, (sorts * lgm * (lgm + 1) / 2 + G) * spb, np.inf)
    Lw = np.ceil(lgm - 1e-9) + 1
    win = np.where(ok, (sorts * Lw * (Lw + 1) / 2 + R * Lw) * spb, np.inf)
    return lgm, ideal, win, dict(lgm_B=lgm_B, lgm_F=det0["lgm_F"], spb=spb, rho=rho, lam=lam)


def best(C, R, P, step=0.5, wstep=0.5, integer=False):
    if integer:
        xs, zs, ds = np.arange(1, 13), np.arange(1, 13), np.arange(1, 17)
    else:
        xs, zs, ds = np.arange(1, 12.01, step), np.arange(0.5, 12.01, step), np.arange(step, 16.01, step)
    ws = np.arange(3, 40.01, wstep)
    X, Z, D, W = np.meshgrid(xs, zs, ds, ws, indexing="ij")
    Y = Z + D
    lgm, ideal, win, det = evaluate(2.0 ** -W, C, R, X, Y, Z, P)
    obj = win if integer else ideal
    i = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[i]):
        return None
    return dict(w=float(W[i]), x=float(X[i]), y=float(Y[i]), z=float(Z[i]), lgm=float(lgm[i]),
                lgm_B=float(det["lgm_B"][i]), lgm_F=float(det["lgm_F"][i]), spb=float(det["spb"][i]),
                rho=float(det["rho"][i]), lam=float(det["lam"][i]), ideal=float(ideal[i]), win=float(win[i]))


# V0 (Chvatal as is) is omitted: at f_floor = 92160 its fringe need pins lg m at 41 for every lateral
# setting (best win 1419 without lateral, 1427 with), recorded in README.md.
VARIANTS = [
    ("S   slack removed (UB-12)", dict(slack=0.0)),
    ("L4  locality + dF=1/2 + no (4.3) + no slack", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False, slack=0.0)),
]


def main():
    # usage: lateral_selfconsistent.py [f_floor ...]   (defaults: 92160 and 1024)
    floors = [float(a) for a in sys.argv[1:]] or [92160.0, 1024.0]
    for f_floor in floors:
        print(f"\n===== f_floor = {f_floor:.0f} rows (2-round separator) =====")
        print(" variant                                      C    R | ideal (win)  eps_sep   rho      lam     (x,y,z)          lg m [B, F]   spb")
        for name, kn in VARIANTS:
            P = dict(E.DEFAULT); P.update(kn); P["f_floor"] = f_floor
            for C, R in ((1, 0), (1, 1), (8, 1), (8, 2)):
                b = best(C, R, P, wstep=1.0)
                bi = best(C, R, P, wstep=1.0, integer=True)
                if b is None:
                    print(f" {name:44s} {C:3d} {R:3d} | infeasible")
                    continue
                wi = f"{bi['win']:5.0f}" if bi else "   - "
                print(f" {name:44s} {C:3d} {R:3d} | {b['ideal']:5.0f} ({wi})  2^-{b['w']:<5.1f} {b['rho']:.2e} {b['lam']:9.1f} "
                      f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f}]  {b['spb']:.3f}", flush=True)


if __name__ == "__main__":
    main()
