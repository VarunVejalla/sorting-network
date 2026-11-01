#!/usr/bin/env python3
"""Finite exact screen of nested endpoint containment after parent cuts.

For every parent that overwrites child roots, verify the cut is supported only
on the first/last child, then check the two potentially nontrivial boundary
grandchild inequalities. This is model evidence only, not an all-depth proof.
"""
import argparse
from collections import defaultdict
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth: int, row_bits: int, params: tuple[int, int, int]):
    flow = FlowDAG(depth, scale=1 << row_bits, p=Par(*params)).build()
    counts = defaultdict(int)
    minima = {}
    failures = []
    misplaced_cuts = []
    for stage, rows in enumerate(flow.rows):
        transitions = flow.transitions[stage]
        for parent in rows:
            parent_level = flow.nodes[parent][0]
            role = flow.p.role(depth, parent_level, stage)
            if role == "botRise":  # It emits no child-root overwrite.
                continue
            parent_capacity = flow.scale * flow.p.cap(depth, parent_level, stage)
            parent_out = transitions[parent]
            for child_index, child in enumerate(flow.nodes[parent_out][4]):
                child_level, _, child_low, child_high, grandchildren = flow.nodes[child]
                if child_index > 0 and child_low != 0:
                    misplaced_cuts.append((stage, parent_level, child_index,
                                           role, "left", child_low))
                if child_index < 7 and child_high != 0:
                    misplaced_cuts.append((stage, parent_level, child_index,
                                           role, "right", child_high))
                if not grandchildren:
                    continue
                grandchild_width = flow.native(child_level + 1)
                edge_cases = []
                if child_index == 0:
                    edge_cases.append(("left", 0))
                if child_index == 7:
                    edge_cases.append(("right", 7))
                for edge, grandchild_index in edge_cases:
                    grandchild = flow.nodes[grandchildren[grandchild_index]]
                    counts[(role, edge)] += 1
                    if grandchild[1] == grandchild_width:
                        continue  # Its empty marker is clamped automatically.
                    margin = (grandchild[2] - child_low if edge == "left"
                              else grandchild[3] - child_high)
                    key = (role, edge)
                    if margin < 0:
                        failures.append((stage, parent_level, child_index,
                                         role, edge, margin))
                    if parent_capacity:
                        ratio = Fraction(margin, parent_capacity)
                        if key not in minima or ratio < minima[key][0]:
                            minima[key] = (ratio, stage, parent_level,
                                           child_index, margin, parent_capacity)
    return counts, minima, failures, misplaced_cuts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, nargs="+", default=[12, 20, 24, 30])
    parser.add_argument("--row-bits", type=int, default=13)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    args = parser.parse_args()
    for depth in args.depths:
        counts, minima, failures, misplaced_cuts = screen(
            depth, args.row_bits, tuple(args.params))
        short_minima = {key: value[:4] for key, value in minima.items()}
        print(f"depth={depth} endpoint_checks={sum(counts.values())} "
              f"failures={len(failures)} misplaced_cuts={len(misplaced_cuts)} "
              f"minima={short_minima}")
        if failures:
            print(f"  first_failure={failures[0]}")
        if misplaced_cuts:
            print(f"  first_misplaced_cut={misplaced_cuts[0]}")


if __name__ == "__main__":
    main()
