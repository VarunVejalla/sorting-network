#!/usr/bin/env python3
"""Exact finite audit of the (3,3,2) D2 fringe-factor claims.

This checks schedule cases and rational inequalities through a chosen depth.
It is finite evidence only; it does not prove the schedule lemmas or geometry.
"""
from collections import Counter
from fractions import Fraction as F
import argparse

from flow_dag import FlowDAG
from oracle import Par


ORDINARY = {"mid", "botDesc", "topRise"}


def schedule_audit(last_depth, p):
    cases = Counter()
    for d in range(3, last_depth + 1):
        for t in range(1, p.tf(d) + 1):
            for i in range(1, d + 1):
                if not p.active(d, i, t) or p.role(d, i, t) not in ORDINARY:
                    continue
                if p.up(d, i, t) <= 0:
                    continue
                if t == 1:
                    assert p.role(d, i, t) == "topRise"
                    assert p.up(d, i, t) / p.cap(d, i, t) == F(1, 256)
                    cases["initial topRise t=1"] += 1
                    continue
                if (t, i) == (2, 2):
                    assert F(p.k ** (d - i), 1) / p.cap(d, i, t) == F(1, 16)
                    cases["startup (2,2)"] += 1
                    continue
                assert t >= 3
                assert p.active(d, i, t - 2), (d, t, i, "inactive at t-2")
                old_role = p.role(d, i, t - 2)
                if old_role in ORDINARY:
                    parent = (i - 1, t - 3)
                    assert parent[0] >= 0 and p.active(d, *parent), (d, t, i, "inactive parent", parent)
                    parent_role = p.role(d, *parent)
                    assert parent_role in ORDINARY | {"topDesc"}, (d, t, i, "bad parent role", parent_role)
                    cases[f"ordinary at t-2; parent {parent_role}"] += 1
                elif old_role == "topDesc":
                    cases["topDesc at t-2"] += 1
                elif old_role == "botRise":
                    assert F(p.k ** (d - i), 1) / p.cap(d, i, t) <= F(1, 16)
                    cases["botRise at t-2; native/c<=1/16"] += 1
                else:
                    raise AssertionError((d, t, i, "unexpected previous role", old_role))
    return cases


def flow_audit(depth, p, scale):
    flow = FlowDAG(depth, scale=scale, p=p).build()
    maxima = {}
    counts = Counter()
    startup_ratio = None
    for t, rows in enumerate(flow.rows):
        for node, (a, pi, _) in rows.items():
            lev, deficit, _, _, _ = flow.nodes[node]
            role = "topDesc" if t == 0 else p.role(depth, lev, t)
            c = scale * p.cap(depth, lev, t)
            g = F(deficit, 1) / c
            rho = F(pi, 1) / c
            ratio = F(a, 1) / c
            counts[role] += 1
            maxima[role] = max(maxima.get(role, (F(0), F(0), F(0))),
                               (ratio, rho, g))
            assert rho <= F(1, 256), ("rho", depth, t, lev, role, rho)
            if role in ORDINARY and pi:
                assert ratio <= F(9, 8), ("a/c", depth, t, lev, role, ratio)
                assert g <= F(1, 256), ("g", depth, t, lev, role, g)
            if (t, lev) == (2, 2):
                startup_ratio = ratio
                assert ratio <= F(1, 16)
    return flow, counts, maxima, startup_ratio


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=30)
    ap.add_argument("--scale", type=int, default=8192)
    args = ap.parse_args()
    p = Par(3, 3, 2)
    cases = schedule_audit(args.depth, p)
    flow, counts, maxima, startup = flow_audit(args.depth, p, args.scale)
    print(f"schedule depths=3..{args.depth}: {dict(cases)}")
    print(f"flow depth={args.depth}, stages={len(flow.rows)}, states={len(flow.nodes)}, scale={args.scale}")
    print(f"active rows by role: {dict(counts)}")
    for role in sorted(maxima):
        a, rho, g = maxima[role]
        print(f"{role}: max a/c={a}, max rho={rho}, max g={g}")
    print(f"startup a/c={startup}")
    print("All finite checks passed; this is not an all-depth proof.")


if __name__ == "__main__":
    main()
