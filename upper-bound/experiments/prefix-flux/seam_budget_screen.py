#!/usr/bin/env python3
"""Exact finite D2 screen for aggregate-plus-seam inversion accounting.

For each actual active sender instance, this sums allocation * excess-gap,
where excess-gap is the sum of (static-label gap - 1) over the sender's at most
eight seam ranks. Dividing by N^2 gives the coefficient multiplying a uniform
relative seam-defect cap in the global inversion transfer. The flow DAG shares
equal subtrees; occurrence multiplicities are propagated exactly.

This checks finite scheduled flows only. It does not bound local inversion
contraction or prove the alignment term contracts.
"""
import argparse
from collections import defaultdict
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth=30, scale=8192, params=(3, 3, 2)):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    N = flow.p.k ** depth * scale
    stages = []
    for t, root in enumerate(flow.roots[:-1]):
        counts = {root: 1}
        weighted = 0
        allocation_sum = 0
        active_bags = 0
        max_runs = 0
        for lev in range(depth + 1):
            active = (lev == 0 if t == 0 else flow.p.active(depth, lev, t))
            if active:
                active_types = flow.rows[t]
                for node, multiplicity in counts.items():
                    if node not in active_types:
                        continue
                    allocation = flow.allocation(node)
                    if allocation <= 0:
                        continue
                    intervals = flow.bag_intervals(node, 0)
                    assert len(intervals) <= flow.p.k + 1
                    excess_gap = sum(
                        intervals[j + 1][0] - intervals[j][1]
                        for j in range(len(intervals) - 1)
                    )
                    assert excess_gap >= 0
                    weighted += multiplicity * allocation * excess_gap
                    allocation_sum += multiplicity * allocation
                    active_bags += multiplicity
                    max_runs = max(max_runs, len(intervals))

            next_counts = defaultdict(int)
            for node, multiplicity in counts.items():
                for child in flow.nodes[node][4]:
                    next_counts[child] += multiplicity
            counts = next_counts

        assert allocation_sum == N, (depth, t, allocation_sum, N)
        stages.append(dict(stage=t, active_bags=active_bags,
                           max_runs=max_runs,
                           weighted_gap_coefficient=Fraction(weighted, N * N)))
    return stages


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=30)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    parser.add_argument("--top", type=int, default=8,
                        help="show this many stages with largest seam coefficients")
    parser.add_argument("--all-stages", action="store_true",
                        help="print every nonzero stage coefficient")
    parser.add_argument("--exact-total", action="store_true",
                        help="also print the exact rational sum")
    args = parser.parse_args()
    result = screen(args.depth, args.scale, tuple(args.params))
    total = sum((row["weighted_gap_coefficient"] for row in result), Fraction(0))
    print(f"depth={args.depth} stages={len(result)} "
          f"nonzero_stages={sum(row['weighted_gap_coefficient'] > 0 for row in result)}")
    shown = (result if args.all_stages else sorted(
        result, key=lambda row: row["weighted_gap_coefficient"], reverse=True
    )[:args.top])
    for row in shown:
        coefficient = row["weighted_gap_coefficient"]
        if coefficient:
            print(f"t={row['stage']} bags={row['active_bags']} "
                  f"runs<={row['max_runs']} seam_coeff={float(coefficient):.12g}")
    print(f"sum stage seam coefficients={float(total):.12g}")
    if args.exact_total:
        print(f"exact total={total}")
