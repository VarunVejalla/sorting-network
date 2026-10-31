#!/usr/bin/env python3
"""Exact finite screen for the (depth +4, stage +6, same-level) D2 shift.

This compares exact radius-r rooted flow signatures from FlowDAG(d) at (t,i)
and FlowDAG(d+4) at (t+6,i), either as normalized distributions or along
identical address prefixes (`--pointwise`). It diagnoses the schedule
conjugacy in D2FlowDepthShift.lean; finite passing runs are not an all-depth
proof.
"""
import argparse
from collections import Counter
from functools import lru_cache
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def omega(t):
    if t == 0:
        return 0
    if t == 1:
        return 1
    m = (t + 4) // 3
    return m if m % 2 == t % 2 else m + 1


def signatures(flow, radius, intern):

    @lru_cache(maxsize=None)
    def signature(node_id, remaining):
        _level, deficit, low, high, children = flow.nodes[node_id]
        if remaining == 0:
            key = (deficit,)
        else:
            key = (deficit, low, high,
                   tuple(signature(child, remaining - 1)
                         for child in children))
        if key not in intern:
            intern[key] = len(intern)
        return intern[key]

    return lambda node_id: signature(node_id, radius)


def distribution(flow, stage, level, signature):
    occurrences = Counter({flow.roots[stage]: 1})
    for _ in range(level):
        children = Counter()
        for node_id, multiplicity in occurrences.items():
            for child_id in flow.nodes[node_id][4]:
                children[child_id] += multiplicity
        occurrences = children
    counts = Counter()
    for node_id, multiplicity in occurrences.items():
        counts[signature(node_id)] += multiplicity
    return {key: Fraction(count, 8 ** level)
            for key, count in counts.items()}


def audit(depth, scale=8192, radius=4, burnin_offset=24, pointwise=False,
          flows=None):
    if flows is None:
        flows = (FlowDAG(depth, scale=scale, p=Par(3, 3, 2)).build(),
                 FlowDAG(depth + 4, scale=scale, p=Par(3, 3, 2)).build())
    old, new = flows
    intern = {}
    old_sig = signatures(old, radius, intern)
    new_sig = signatures(new, radius, intern)
    start = 2 * depth + burnin_offset + 2
    stop = min(3 * depth - 14, len(new.rows) - 6)
    checked = mismatches = bad_paths = 0
    first = []
    for stage in range(start, stop):
        old_levels = {old.nodes[node][0] for node in old.rows[stage]}
        new_levels = {new.nodes[node][0] for node in new.rows[stage + 6]}
        if pointwise:
            occurrences = Counter({(old.roots[stage], new.roots[stage + 6]): 1})
            max_level = max(old_levels & new_levels, default=-1)
            for level in range(max_level + 1):
                if level in old_levels and level in new_levels and \
                        level + radius < depth and \
                        level + radius < omega(stage):
                    checked += 1
                    bad = sum(m for (a, b), m in occurrences.items()
                              if old_sig(a) != new_sig(b))
                    if bad:
                        mismatches += 1
                        bad_paths += bad
                        if len(first) < 12:
                            first.append((stage, level, bad))
                children = Counter()
                for (old_id, new_id), multiplicity in occurrences.items():
                    for old_child, new_child in zip(
                            old.nodes[old_id][4], new.nodes[new_id][4]):
                        children[(old_child, new_child)] += multiplicity
                occurrences = children
            continue
        for level in sorted(old_levels & new_levels):
            if level + radius >= depth or level + radius >= omega(stage):
                continue
            checked += 1
            if distribution(old, stage, level, old_sig) != \
                    distribution(new, stage + 6, level, new_sig):
                mismatches += 1
                if len(first) < 12:
                    first.append((stage, level))
    return {
        "depth": depth,
        "radius": radius,
        "burnin_offset": burnin_offset,
        "checked_bulk_pairs": checked,
        "mismatches": mismatches,
        "mismatching_path_prefixes": bad_paths if pointwise else None,
        "first_mismatches": first,
        "mode": "pointwise paths" if pointwise else "normalized distribution",
        "pass": mismatches == 0,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depths", type=int, nargs="+", default=[60])
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--radius", type=int, default=4)
    parser.add_argument("--radii", type=int, nargs="+",
                        help="check multiple radii while building each FlowDAG once")
    parser.add_argument("--burnin-offset", type=int, default=24)
    parser.add_argument("--pointwise", action="store_true",
                        help="compare same-address profile states, not histograms")
    args = parser.parse_args()
    for depth in args.depths:
        flows = (FlowDAG(depth, scale=args.scale, p=Par(3, 3, 2)).build(),
                 FlowDAG(depth + 4, scale=args.scale, p=Par(3, 3, 2)).build())
        for radius in args.radii or [args.radius]:
            print(audit(depth, args.scale, radius, args.burnin_offset,
                        args.pointwise, flows))
