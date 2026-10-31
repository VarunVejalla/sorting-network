#!/usr/bin/env python3
"""Exact finite audit of total static-hole length across active D2 senders.

The local Lean seam lemma bounds the number of keys crossing each sender-rank
cut by an absolute constant. Multiplying by the hole lengths crossed requires
the sum of actual static gaps over all sender occurrences. This script
computes that schedule quantity exactly; it is diagnostic, not an all-depth
proof.
"""
import argparse
from collections import defaultdict
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth=30, scale=8192, params=(3, 3, 2)):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    n_wires = flow.p.k ** depth * scale
    result = []
    for t, root in enumerate(flow.roots[:-1]):
        counts = {root: 1}
        total_gap = 0
        senders = 0
        for level in range(depth + 1):
            active = (level == 0 if t == 0 else flow.p.active(depth, level, t))
            if active:
                active_types = flow.rows[t]
                for node, multiplicity in counts.items():
                    if node not in active_types or flow.allocation(node) <= 0:
                        continue
                    intervals = flow.bag_intervals(node, 0)
                    gap = sum(intervals[j + 1][0] - intervals[j][1]
                              for j in range(len(intervals) - 1))
                    total_gap += multiplicity * gap
                    senders += multiplicity
            next_counts = defaultdict(int)
            for node, multiplicity in counts.items():
                for child in flow.nodes[node][4]:
                    next_counts[child] += multiplicity
            counts = next_counts
        result.append((t, senders, total_gap, Fraction(total_gap, n_wires)))
    return n_wires, result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=30)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    args = parser.parse_args()
    n_wires, rows = screen(args.depth, args.scale, tuple(args.params))
    total = sum((r[3] for r in rows), Fraction(0))
    print(f"depth={args.depth} stages={len(rows)} N={n_wires}")
    for t, senders, gap, ratio in sorted(rows, key=lambda r: r[3], reverse=True)[:8]:
        if gap:
            print(f"t={t} senders={senders} total_gap={gap} "
                  f"gap_over_N={float(ratio):.12g}")
    print(f"sum_stage_gap_over_N={float(total):.12g}")
    print(f"exact_sum_stage_gap_over_N={total}")
