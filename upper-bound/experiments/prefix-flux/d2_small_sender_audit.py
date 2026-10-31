#!/usr/bin/env python3
"""Count actual D2 sender occurrences below a polylogarithmic cutoff.

FlowDAG interns identical states. This audit expands their multiplicities
without enumerating all k**d addresses, then reports the number and arities
of active senders below m*(ln N)^2 at each scheduled stage.
"""
import argparse
from collections import Counter, defaultdict
from math import log

from flow_dag import FlowDAG
from oracle import Par


def stage_sender_counts(flow, stage):
    counts = {flow.roots[stage]: 1}
    by_level = defaultdict(Counter)
    for level in range(flow.d + 1):
        current = [(node, multiplicity)
                   for node, multiplicity in counts.items()
                   if flow.nodes[node][0] == level]
        assert sum(multiplicity for _, multiplicity in current) == flow.p.k ** level
        for node, multiplicity in current:
            row = flow.rows[stage].get(node)
            if row is not None:
                arity, up, _blocks = row
                # botRise sends its entire bag upward and bypasses the local
                # separator; topDesc has up=0 and is handled separately.
                if 0 < up < arity:
                    by_level[level][arity] += multiplicity
            for child in flow.nodes[node][4]:
                counts[child] = counts.get(child, 0) + multiplicity
    return by_level


def check_small(depths=(3, 4, 5)):
    """Cross-check DAG multiplicities against explicit address enumeration."""
    checked = 0
    for depth in depths:
        flow = FlowDAG(depth, scale=8, p=Par(3, 3, 2)).build()
        for stage in range(len(flow.rows)):
            compressed = stage_sender_counts(flow, stage)
            for level in range(depth + 1):
                explicit = Counter()
                for index in range(flow.p.k ** level):
                    node = flow.lookup(stage, level, index)
                    row = flow.rows[stage].get(node)
                    if row is not None and 0 < row[1] < row[0]:
                        explicit[row[0]] += 1
                assert explicit == compressed.get(level, Counter()), (
                    depth, stage, level, explicit, compressed.get(level))
                checked += 1
    print(f"explicit address cross-checks={checked}")


def audit(depths, scale=8192, params=(3, 3, 2)):
    p = Par(*params)
    for depth in depths:
        flow = FlowDAG(depth, scale=scale, p=p).build()
        n = scale * p.k ** depth
        cutoff = scale * log(n) ** 2
        rows = []
        provider_arities = []
        for stage in range(len(flow.rows)):
            by_level = stage_sender_counts(flow, stage)
            provider_arities.extend(
                arity for arities in by_level.values() for arity in arities)
            small = [(level, arity, multiplicity)
                     for level, arities in by_level.items()
                     for arity, multiplicity in arities.items()
                     if arity < cutoff]
            if small:
                total = sum(multiplicity for _, _, multiplicity in small)
                rows.append((stage, total, min(a for _, a, _ in small),
                             max(a for _, a, _ in small)))
        if rows:
            print(f"d={depth} stages={len(flow.rows)} cutoff={cutoff:.0f} "
                  f"all_provider_arity_min={min(provider_arities)} "
                  f"columns_min={((min(provider_arities)+scale-1)//scale)} "
                  f"small_window={rows[0][0]}..{rows[-1][0]} "
                  f"occupied_stages={len(rows)} "
                  f"senders_per_stage={min(x[1] for x in rows)}.."
                  f"{max(x[1] for x in rows)} "
                  f"arity_union={min(x[2] for x in rows)}.."
                  f"{max(x[3] for x in rows)}")
        else:
            print(f"d={depth} stages={len(flow.rows)} cutoff={cutoff:.0f} "
                  f"all_provider_arity_min={min(provider_arities)} "
                  f"columns_min={(min(provider_arities)+scale-1)//scale} "
                  "no small senders")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("depths", nargs="*", type=int,
                        default=[16, 24, 32, 48, 64, 96, 128])
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--check-small", action="store_true")
    args = parser.parse_args()
    if args.check_small:
        check_small()
    audit(args.depths, scale=args.scale)
