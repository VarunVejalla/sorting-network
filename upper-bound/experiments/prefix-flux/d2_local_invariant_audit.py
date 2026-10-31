#!/usr/bin/env python3
"""Exact finite audit of the proposed local D2 sender invariant.

Checks every distinct reachable active state in the interned FlowDAG.  This is
an exhaustive finite-state audit for the requested depth, not an all-depth
induction or a sorting proof.
"""
import argparse
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par


def ratio_text(x):
    return f"{x} ({float(x):.12g})"


def audit(depth=100, scale=8192, params=(3, 3, 2)):
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    ordinary = {"topRise", "mid", "botDesc"}
    stats = {role: {"states": 0, "max_g": F(0), "max_pi": F(0),
                    "min_end": None, "g_witness": None,
                    "pi_witness": None, "end_witness": None,
                    "fail_g": 0, "fail_pi": 0, "fail_end": 0}
             for role in ("topDesc", "topRise", "mid", "botDesc", "botRise")}
    for t, rows in enumerate(flow.rows):
        for node, (a, pi, _blocks) in rows.items():
            lev, G, _low, _high, children = flow.nodes[node]
            role = p.role(depth, lev, t)
            c = F(scale) * p.cap(depth, lev, t)
            assert c > 0
            g_ratio, pi_ratio = F(G, 1) / c, F(pi, 1) / c
            if children:
                end_deficits = (flow.nodes[children[0]][1],
                                flow.nodes[children[-1]][1])
                end_ratio = F(min(end_deficits), 1) / c
            else:
                end_deficits, end_ratio = (0, 0), F(0)
            x = stats[role]
            x["states"] += 1
            if g_ratio > x["max_g"]:
                x["max_g"] = g_ratio
                x["g_witness"] = (t, lev)
            if pi_ratio > x["max_pi"]:
                x["max_pi"] = pi_ratio
                x["pi_witness"] = (t, lev)
            if x["min_end"] is None or end_ratio < x["min_end"]:
                x["min_end"] = end_ratio
                x["end_witness"] = (t, lev)
            if role in ordinary:
                x["fail_g"] += g_ratio > F(1, 512)
                x["fail_pi"] += pi_ratio > F(1, 256)
                x["fail_end"] += end_ratio < F(1, 128)

    print(f"D2 local invariant audit: params={params}, depth={depth}, scale={scale}")
    print(f"FlowDAG: {len(flow.nodes)} interned nodes, {len(flow.rows)} stages")
    print("Ordinary-role targets: G/c <= 1/512, pi/c <= 1/256, min(end G)/c >= 1/128")
    passed = True
    for role in ("topDesc", "topRise", "mid", "botDesc", "botRise"):
        x = stats[role]
        print(f"{role}: {x['states']} distinct active states; "
              f"max G/c={ratio_text(x['max_g'])} at {x['g_witness']}; "
              f"max pi/c={ratio_text(x['max_pi'])} at {x['pi_witness']}; "
              f"min endpoint/c={ratio_text(x['min_end'])} at {x['end_witness']}")
        if role in ordinary:
            fails = (x["fail_g"], x["fail_pi"], x["fail_end"])
            print(f"  threshold failures (G, pi, endpoint): {fails}")
            passed &= fails == (0, 0, 0)
    print("FINITE PASS" if passed else "FINITE FAIL")
    print("This checks all distinct reachable active states only through the requested depth.")
    return passed


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=40)
    ap.add_argument("--scale", type=int, default=8192)
    args = ap.parse_args()
    raise SystemExit(0 if audit(args.depth, args.scale) else 1)
