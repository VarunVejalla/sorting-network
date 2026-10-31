#!/usr/bin/env python3
"""Finite exact-state gate for the D2 six-stage/four-level shift.

For each tested depth, compare the exact normalized frequency distributions
of actual per-wire node signatures at (stage t, level i) and
(stage t+6, level i+4). Multiplicities are computed over the shared FlowDAG,
then divided by the number 8**level of nodes. `--radius r` compares recursive
rooted signatures down r levels; radius 1 is the root `(G,low,high)` plus its
eight child deficits. After burn-in 2*d+16, the screen expects equality except
when an even-depth descendant in the observed profile reaches the moving
upper frontier. This is an empirical induction hint, not an all-depth theorem.
"""
import argparse
from collections import Counter
from functools import lru_cache
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def ceil_par(m, t):
    return m if m % 2 == t % 2 else m + 1


def omega(t):
    if t == 0:
        return 0
    if t == 1:
        return 1
    return ceil_par((t + 4) // 3, t)


def state_signatures(flow, stage, level, radius, node_signature):
    """Exact frequency distribution of node signatures at one tree level."""
    occurrences = Counter({flow.roots[stage]: 1})
    for _ in range(level):
        children = Counter()
        for node_id, multiplicity in occurrences.items():
            for child_id in flow.nodes[node_id][4]:
                children[child_id] += multiplicity
        occurrences = children
    signatures = Counter()
    for node_id, multiplicity in occurrences.items():
        signatures[node_signature(node_id, radius)] += multiplicity
    denominator = flow.p.k**level
    return Counter({signature: Fraction(count, denominator)
                    for signature, count in signatures.items()})


def audit(depth, scale=8192, burnin_offset=16, radius=1):
    flow = FlowDAG(depth, scale=scale, p=Par(3, 3, 2)).build()
    signature_ids = {}

    @lru_cache(maxsize=None)
    def node_signature(node_id, observed_radius):
        _level, deficit, low, high, children = flow.nodes[node_id]
        if observed_radius == 0:
            key = (0, deficit)
        else:
            key = (
                observed_radius,
                deficit,
                low,
                high,
                tuple(node_signature(child, observed_radius - 1)
                      for child in children),
            )
        if key not in signature_ids:
            signature_ids[key] = len(signature_ids)
        return signature_ids[key]

    terminal = 3 * depth - 14
    start = 2 * depth + burnin_offset
    checked = exceptions = 0
    unexpected = []
    stop = min(terminal - 5, len(flow.rows) - 6)
    for stage in range(start, stop):
        old_levels = {flow.nodes[n][0] for n in flow.rows[stage]}
        new_levels = {flow.nodes[n][0] for n in flow.rows[stage + 6]}
        for level in old_levels:
            if level + 4 not in new_levels:
                continue
            checked += 1
            mismatch = state_signatures(
                flow, stage, level, radius, node_signature
            ) != state_signatures(
                flow, stage + 6, level + 4, radius, node_signature
            )
            is_upper_edge = any(
                level + 2 * offset + 2 == omega(stage)
                for offset in range((radius - 1) // 2 + 1)
            )
            exceptions += is_upper_edge
            if mismatch != is_upper_edge:
                unexpected.append((stage, level, mismatch, is_upper_edge))
    return {
        "depth": depth,
        "burnin_offset": burnin_offset,
        "radius": radius,
        "burn_in": start,
        "checked_stage_level_pairs": checked,
        "upper_edge_exceptions": exceptions,
        "unexpected_mismatches": unexpected[:8],
        "unexpected_count": len(unexpected),
        "pass": not unexpected,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depths", type=int, nargs="+", default=[40, 50, 60, 70])
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--burnin-offset", type=int, default=16)
    parser.add_argument("--radius", type=int, default=1,
                        help="recursive node-state depth of signatures (default: 1)")
    args = parser.parse_args()
    for depth in args.depths:
        print(audit(depth, args.scale, args.burnin_offset, args.radius))
