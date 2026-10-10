#!/usr/bin/env python3
"""Finite Bellman potential on rank-indexed exact certificate minima.

Transitions come from actual Boolean comparator-network states. Quotienting
by certificate statistics permits splicing different representatives: this is
a relaxation, not a sorting construction or an asymptotic lower bound.
"""
import argparse
import json
from collections import deque
from itertools import product

from kahale_joint_potential import minimum_sizes, parallel_layers


def probe(n, state_limit):
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    target = tuple(sum((x.bit_count() >= n - i) << x for x in range(1 << n)) for i in range(n))
    actions = parallel_layers(n)
    states = [initial]
    parents = [None]
    index = {initial: 0}
    signatures = []
    stat_cache = {}
    edges = []
    cursor = 0
    while cursor < len(states):
        state = states[cursor]
        for f in state:
            if f not in stat_cache:
                stat_cache[f] = minimum_sizes(f, n)
        signature = tuple(stat_cache[f] for f in state)
        signatures.append(signature)
        row = []
        for layer in actions:
            out = list(state)
            width = 0
            for i, j in layer:
                a, b = state[i], state[j]
                out[i], out[j] = a & b, a | b
                if out[i] != a:  # Boolean inversion exists: active comparator.
                    width = max(width, j - i)
            out = tuple(out)
            if out not in index:
                if len(states) >= state_limit:
                    return {"wires": n, "complete": False, "state_limit": state_limit}
                index[out] = len(states)
                states.append(out)
                parents.append((cursor, layer))
            row.append((index[out], width))
        edges.append(row)
        cursor += 1

    def distances(rows, goal):
        reverse = [[] for _ in rows]
        for source, row in enumerate(rows):
            for dest, _ in row:
                reverse[dest].append(source)
        distance = {goal: 0}
        queue = deque([goal])
        while queue:
            dest = queue.popleft()
            for source in reverse[dest]:
                if source not in distance:
                    distance[source] = distance[dest] + 1
                    queue.append(source)
        return distance

    sig_index = {sig: i for i, sig in enumerate(dict.fromkeys(signatures))}
    quotient = [set() for _ in sig_index]
    for source, row in enumerate(edges):
        for dest, width in row:
            quotient[sig_index[signatures[source]]].add((sig_index[signatures[dest]], width))
    goal = index[target]
    qgoal = sig_index[signatures[goal]]
    exact = distances(edges, goal)
    relaxed = distances(quotient, qgoal)

    # V_s(signature)=1 iff no relaxed completion in s layers. Enforce the
    # necessary width bound on the first layer of an s-layer completion.
    viable = {qgoal}
    width_depth = None
    viability_counts = [1]
    for budget in range(1, n + 2):
        cap = (1 << budget) - 1
        viable = {source for source, row in enumerate(quotient)
                  if any(dest in viable and width <= cap for dest, width in row)}
        viability_counts.append(len(viable))
        if sig_index[signatures[0]] in viable:
            width_depth = budget
            break
    gaps = [(exact[i] - relaxed[sig_index[sig]], i) for i, sig in enumerate(signatures)]
    gap, witness = max(gaps)
    def prefix_path(i):
        path = []
        while parents[i] is not None:
            i, layer = parents[i]
            path.append(layer)
        return list(reversed(path))

    same_signature = [i for i, sig in enumerate(signatures) if sig == signatures[witness]]
    best_representative = min(same_signature, key=lambda i: exact[i])
    distinguishing_union_cost = None
    for i in range(n):
        for j in range(i + 1, n):
            def costs(state):
                a, b = state[i], state[j]
                return (minimum_sizes(a | b, n)[0], minimum_sizes(a & b, n)[1])
            first, second = costs(states[witness]), costs(states[best_representative])
            if first != second and distinguishing_union_cost is None:
                distinguishing_union_cost = {"wires": (i, j), "slow_state_costs": first,
                                             "fast_state_costs": second}

    # Strong finite numerical relaxation: even require every intermediate
    # signature to be reachable by some actual network. Gate representatives
    # need not agree. Identity transitions allow redundant comparators.
    numeric = {False: [set() for _ in sig_index], True: [set() for _ in sig_index]}
    for sig, source in sig_index.items():
        for layer in actions:
            options = []
            for i, j in layer:
                a, b = sig[i]
                c, d = sig[j]
                gate = [(sig[i], sig[j], False)]
                for u in range(max(a, c), min(n, a + c) + 1):
                    for v in range(max(b, d), min(n, b + d) + 1):
                        if min(a, c) + v <= n + 1 and u + min(b, d) <= n + 1:
                            gate.append(((min(a, c), v), (u, min(b, d)), True))
                options.append(gate)
            for choices in product(*options):
                output = list(sig)
                width = 0
                coupled = True
                for (i, j), (lo, hi, active) in zip(layer, choices):
                    output[i], output[j] = lo, hi
                    if active:
                        width = max(width, j - i)
                        coupled = coupled and hi[0] + lo[1] <= n + 2
                dest = sig_index.get(tuple(output))
                if dest is not None:
                    numeric[False][source].add((dest, width))
                    if coupled:
                        numeric[True][source].add((dest, width))

    numeric_results = []
    for coupling, rows in numeric.items():
        for width_filter in (False, True):
            viable = {qgoal}
            counts = [1]
            depth = None
            for budget in range(1, n + 2):
                cap = (1 << budget) - 1 if width_filter else n
                viable = {source for source, row in enumerate(rows)
                          if any(dest in viable and width <= cap for dest, width in row)}
                counts.append(len(viable))
                if sig_index[signatures[0]] in viable:
                    depth = budget
                    break
            numeric_results.append({"union_coupling": coupling, "suffix_width": width_filter,
                                    "initial_depth": depth, "viable_counts": counts})

    enriched_index = {}
    enriched_ids = []
    for state, sig in zip(states, signatures):
        unions = []
        for i in range(n):
            for j in range(i + 1, n):
                lo, hi = state[i] & state[j], state[i] | state[j]
                for f in (lo, hi):
                    if f not in stat_cache:
                        stat_cache[f] = minimum_sizes(f, n)
                unions.append((stat_cache[hi][0], stat_cache[lo][1]))
        key = (sig, tuple(unions))
        if key not in enriched_index:
            enriched_index[key] = len(enriched_index)
        enriched_ids.append(enriched_index[key])
    enriched_rows = [set() for _ in enriched_index]
    for source, row in enumerate(edges):
        for dest, width in row:
            enriched_rows[enriched_ids[source]].add((enriched_ids[dest], width))
    enriched_distance = distances(enriched_rows, enriched_ids[goal])
    enriched_gap = max(exact[i] - enriched_distance[enriched_ids[i]] for i in range(len(states)))
    return {"wires": n, "complete": True, "actual_states": len(states),
            "rank_statistic_signatures": len(sig_index),
            "exact_initial_depth": exact[0], "quotient_initial_depth": relaxed[sig_index[signatures[0]]],
            "width_filtered_initial_depth": width_depth,
            "viable_signature_counts_by_suffix_depth": viability_counts,
            "largest_quotient_depth_underestimate": gap,
            "numerical_relaxations": numeric_results,
            "pairwise_union_enrichment": {"signatures": len(enriched_index),
                "initial_depth": enriched_distance[enriched_ids[0]],
                "largest_remaining_depth_underestimate": enriched_gap},
            "gap_witness": {"functions": states[witness], "signature": signatures[witness],
                            "prefix_layers": prefix_path(witness),
                            "actual_remaining_depth": exact[witness],
                            "relaxed_remaining_depth": relaxed[sig_index[signatures[witness]]],
                            "fast_representative_functions": states[best_representative],
                            "fast_representative_prefix": prefix_path(best_representative),
                            "fast_representative_depth": exact[best_representative],
                            "distinguishing_union_cost": distinguishing_union_cost},
            "scope": "exhaustive finite computation; no asymptotic or Lean claim"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, nargs="+", default=[3, 4])
    parser.add_argument("--state-limit", type=int, default=100000)
    parser.add_argument("--output")
    args = parser.parse_args()
    result = [probe(n, args.state_limit) for n in args.wires]
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(data)
    print(data)


if __name__ == "__main__":
    main()
