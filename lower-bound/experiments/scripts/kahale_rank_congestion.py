#!/usr/bin/env python3
"""Global suffix routing obstruction for the scalar height barrier schedule.

Every sorting completion must route all prefix zeros into the first k output
wires simultaneously. Individual reachability does not imply this matching.
Hall witnesses here are exact finite obstructions, not an asymptotic bound.
"""
import argparse
import json
import random
from itertools import combinations

from kahale_height_barrier import fib
from kahale_positional_barrier import layers, expand_layer


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low


def matching_witness(sources, reach, target):
    matched = {}
    used = 0
    def augment(source, visited):
        nonlocal used
        adjacent = reach[source] & target
        free = adjacent & ~used
        if free:
            low = free & -free
            matched[low.bit_length() - 1] = source
            used |= low
            return True
        for dest in bits(adjacent):
            if dest in visited:
                continue
            visited.add(dest)
            if dest not in matched or augment(matched[dest], visited):
                matched[dest] = source
                return True
        return False
    size = sum(augment(source, set()) for source in sources)
    if size == len(sources):
        return None
    covered = set(matched.values())
    left = set(sources) - covered
    pending, right = list(left), set()
    while pending:
        source = pending.pop()
        for dest in bits(reach[source] & target):
            if dest not in right:
                right.add(dest)
                if dest in matched and matched[dest] not in left:
                    left.add(matched[dest])
                    pending.append(matched[dest])
    if len(left) <= len(right):
        raise RuntimeError("invalid Hall witness")
    return {"prefix_wires": sorted(left), "available_output_wires": sorted(right),
            "deficiency": len(left) - len(right), "maximum_matching_size": size}


def coalition_diagnostics(entry, reach, n):
    sources = entry["hall_witness"]["prefix_wires"]
    color = entry["color"]
    full = (1 << n) - 1
    def target(count):
        return (1 << count) - 1 if color == 0 else full ^ ((1 << (n - count)) - 1)
    def required(group):
        lo, hi = 0, n
        while lo < hi:
            mid = (lo + hi) // 2
            if matching_witness(group, reach, target(mid)) is None:
                hi = mid
            else:
                lo = mid + 1
        return lo
    count = entry["zero_count"] if color == 0 else n - entry["zero_count"]
    result = {"singleton_required_color_count": max(required([i]) for i in sources),
              "coalition_required_color_count": required(sources)}
    if len(sources) <= 14:
        result["pair_required_color_count"] = max(required(list(pair))
            for pair in combinations(sources, 2)) if len(sources) > 1 else required(sources)
        result["minimum_deficient_subcoalition_size_within_witness"] = next(
            m for m in range(1, len(sources) + 1) for group in combinations(sources, m)
            if matching_witness(list(group), reach, target(count)) is not None)
    return result


def probe(depth, trials, seed, zero_count=None):
    n = (1 << depth) // ((depth + 1) * fib(depth + 1))
    if not 2 <= n <= 1000:
        raise ValueError("choose a depth giving between 2 and 1000 wires")
    if zero_count is not None and not 0 <= zero_count <= n:
        raise ValueError("zero count must lie between zero and the wire count")
    schedule = [list(expand_layer(block)) for block in layers(n, depth)]
    reach_by_cut = [None] * (depth + 1)
    reach = [1 << i for i in range(n)]
    reach_by_cut[-1] = reach
    for cut in range(depth - 1, -1, -1):
        reach = reach[:]
        for i, j in schedule[cut]:
            reach[i] = reach[j] = reach[i] | reach[j]
        reach_by_cut[cut] = reach
    components_by_cut = []
    for cut in range(depth + 1):
        parent = list(range(n))
        def root(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i
        for layer in schedule[cut:]:
            for i, j in layer:
                parent[root(j)] = root(i)
        groups = {}
        for i in range(n):
            groups.setdefault(root(i), []).append(i)
        components_by_cut.append(list(groups.values()))
    rng, best, stronger, counts, stronger_counts = random.Random(seed), None, None, {}, {}
    for trial in range(trials):
        if zero_count is None:
            original = [rng.randrange(2) for _ in range(n)]
        else:
            support = set(rng.sample(range(n), zero_count))
            original = [0 if i in support else 1 for i in range(n)]
        k, values = original.count(0), original[:]
        target_zero = (1 << k) - 1
        target_one = ((1 << n) - 1) ^ target_zero
        for cut in range(depth + 1):
            reach = reach_by_cut[cut]
            zero = [i for i, value in enumerate(values) if value == 0]
            one = [i for i, value in enumerate(values) if value == 1]
            individually_possible = all(reach[i] & target_zero for i in zero) and all(
                reach[i] & target_one for i in one)
            if individually_possible:
                witness = matching_witness(zero, reach, target_zero)
                color = 0
                if witness is None:
                    witness = matching_witness(one, reach, target_one)
                    color = 1
                if witness is not None:
                    remaining = depth - cut
                    counts[remaining] = counts.get(remaining, 0) + 1
                    component_balanced = all(sum(values[i] == 0 for i in group) ==
                        sum(i < k for i in group) for group in components_by_cut[cut])
                    entry = {"trial": trial, "cut": cut, "remaining_layers": remaining,
                            "zero_count": k, "color": color, "input": original,
                            "prefix_values": values[:], "all_singleton_routes_possible": True,
                            "suffix_component_capacities_match": component_balanced,
                            "hall_witness": witness}
                    if best is None or remaining > best["remaining_layers"]:
                        best = entry
                    if component_balanced:
                        stronger_counts[remaining] = stronger_counts.get(remaining, 0) + 1
                        if stronger is None or remaining > stronger["remaining_layers"]:
                            stronger = entry
            if cut < depth:
                for i, j in schedule[cut]:
                    values[i], values[j] = min(values[i], values[j]), max(values[i], values[j])
    for entry in (best, stronger):
        if entry is not None and "coalition_diagnostics" not in entry:
            entry["coalition_diagnostics"] = coalition_diagnostics(entry, reach_by_cut[entry["cut"]], n)
    return {"depth": depth, "wires": n, "trials": trials, "seed": seed,
            "prescribed_zero_count": zero_count,
            "collective_obstruction_counts_by_remaining_depth": counts,
            "earliest_collective_obstruction": best,
            "obstructions_passing_component_capacities_by_remaining_depth": stronger_counts,
            "earliest_obstruction_passing_component_capacities": stronger,
            "scope": "exact Hall witnesses on seeded inputs; no asymptotic improvement"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, nargs="+", default=[40])
    parser.add_argument("--trials", type=int, default=64)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--zeros", type=int, nargs="+",
                        help="sample fixed-rank slices instead of independent input bits")
    parser.add_argument("--output")
    args = parser.parse_args()
    data = json.dumps([probe(d, args.trials, args.seed, k)
        for d in args.depth for k in (args.zeros or [None])], indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(data)
    print(data)


if __name__ == "__main__":
    main()
