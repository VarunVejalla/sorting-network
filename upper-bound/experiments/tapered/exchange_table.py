#!/usr/bin/env python3
"""Detailed exchange-rate tables (best continuous and best integer (x,y,z) per tolerated eps_B)
for selected variants of exchange_rate.py.  Run:  python -I exchange_table.py"""
import os
import sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exchange_rate as E  # noqa: E402

SEL = [
    ("V0  Chvatal as is", {}),
    ("L1  locality: per-side B + adjacent-only sibling (mult 2)", dict(side=0.5, sibmult=2.0)),
    ("L2  L1 + dF=1/2", dict(side=0.5, sibmult=2.0, dF=0.5)),
    ("L3  L2 + drop (4.3)", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False)),
    ("L4  L3 + non-uniform blocks (slack 0)", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False, slack=0.0)),
    ("S   V0 + non-uniform blocks only (slack 0)", dict(slack=0.0)),
    ("S'  V0 + slack halved", dict(slack=0.5)),
]
TARGETS = [26, 20, 16, 12, 8]


def show(P, label):
    print(f"\n--- {label} ---")
    print(" eps_B  | cont (x,y,z)      k      A       nu     lg m  [B   F ]  stage(3T)  spb    slope | int (x,y,z) lgm_win slope_win")
    for w in TARGETS:
        b = E.best(2.0 ** -w, P, step=0.1)
        bi = E.best(2.0 ** -w, P, integer=True)
        if b is None:
            print(f" 2^-{w:<3} | infeasible")
            continue
        sorts = 3 if P["rounds"] == 2 else 2
        st = sorts * b["lgm"] * (b["lgm"] + 1) / 2
        si = (f"({bi['x']:.0f},{bi['y']:.0f},{bi['z']:.0f}) {int(np.ceil(bi['lgm']-1e-9))+1:3d}  {bi['win']:6.0f}"
              if bi else "   -")
        print(f" 2^-{w:<3} | ({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  {2**b['x']:6.0f} {2**b['y']:8.0f} "
              f"{2**-b['z']:.4f} {b['lgm']:5.1f} [{b['lgm_B']:4.1f} {b['lgm_F']:4.1f}] {st:7.0f}  {b['spb']:.3f} "
              f"{b['ideal']:6.0f} | {si}")


if __name__ == "__main__":
    for rounds in (2, 1):
        for name, kn in SEL:
            P = dict(E.DEFAULT); P.update(kn); P["rounds"] = rounds
            if rounds == 1:
                P["cF"] = 2.0          # optimistic one-round fringe: the obstruction value eps_F ~ 1/(2f)
            show(P, f"{rounds}-round separator, f_floor={P['f_floor']:.0f}: {name}")
    print("\n=== hypothetical small-fringe F (f_floor = 1024), 2-round ===")
    for name, kn in SEL:
        P = dict(E.DEFAULT); P.update(kn); P["f_floor"] = 1024.0
        show(P, name)
