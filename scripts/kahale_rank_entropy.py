#!/usr/bin/env python3
"""Exact rank-fiber counts and numerical entropy loss at actual comparators.

Uniform input rank permutations induce nonuniform prefix rank distributions.
Counts are exact; reported entropy values use floating point. This is finite
research, not an asymptotic lower-bound proof.
"""
import argparse
from collections import Counter
import itertools
import json
import math

from kahale_joint_potential import minimum_sizes, parallel_layers


def probe(n):
    perms = list(itertools.permutations(range(n)))
    perm_index = {p: i for i, p in enumerate(perms)}
    total = math.factorial(n)
    gates = [(i, j) for i in range(n) for j in range(i + 1, n)]
    transports = []
    for i, j in gates:
        row = []
        for p in perms:
            q = list(p)
            q[i], q[j] = min(p[i], p[j]), max(p[i], p[j])
            row.append(perm_index[tuple(q)])
        transports.append(row)
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    states, index, distributions, parents, edges = [initial], {initial: 0}, [(1,) * total], [None], []
    for source, state in enumerate(states):
        row = []
        for action, (i, j) in enumerate(gates):
            output = list(state)
            output[i], output[j] = state[i] & state[j], state[i] | state[j]
            output = tuple(output)
            if output not in index:
                index[output] = len(states)
                states.append(output)
                counts = [0] * total
                for p, count in enumerate(distributions[source]):
                    counts[transports[action][p]] += count
                distributions.append(tuple(counts))
                parents.append((source, (i, j)))
            row.append(index[output])
        edges.append(row)
    def entropy(counts):
        return math.log2(total) - sum(c * math.log2(c) for c in counts if c) / total
    entropies = [entropy(counts) for counts in distributions]
    cache, records = {}, {}
    def stats(f):
        if f not in cache:
            cache[f] = minimum_sizes(f, n)
        return cache[f]
    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return list(reversed(result))
    for source, state in enumerate(states):
        for action, (i, j) in enumerate(gates):
            signature = (stats(state[i]), stats(state[j]))
            loss = entropies[source] - entropies[edges[source][action]]
            prev = records.get(signature)
            if prev is None or loss > prev[0] + 1e-12:
                records[signature] = (loss, source, action)
    equal_zero = []
    for k in range(1, n + 1):
        choices = [(record, sig) for sig, record in records.items() if sig[0][0] == sig[1][0] == k]
        if not choices:
            continue
        (loss, source, action), sig = max(choices)
        dest = edges[source][action]
        equal_zero.append({"zero_minimum": k, "largest_entropy_loss": loss,
            "independent_sorted_maxima_prediction": k / (2 * k - 1),
            "input_certificate_pairs": sig, "prefix": path(source), "comparator": gates[action],
            "before_rank_fiber_histogram": dict(Counter(distributions[source])),
            "after_rank_fiber_histogram": dict(Counter(distributions[dest]))})
    late_layer = None
    for source, state in enumerate(states):
        pairs = [stats(f) for f in state]
        if min(z + o for z, o in pairs) < n:
            continue
        for layer in parallel_layers(n):
            output = list(state)
            for i, j in layer:
                output[i], output[j] = state[i] & state[j], state[i] | state[j]
            dest = index[tuple(output)]
            loss = entropies[source] - entropies[dest]
            if late_layer is None or loss > late_layer["entropy_loss"] + 1e-12:
                late_layer = {"entropy_loss": loss, "prefix": path(source), "layer": layer,
                    "input_certificate_pairs": pairs,
                    "before_rank_fiber_histogram": dict(Counter(distributions[source])),
                    "after_rank_fiber_histogram": dict(Counter(distributions[dest]))}
    return {"wires": n, "rank_inputs": total, "reachable_boolean_states": len(states),
            "largest_entropy_loss": max(r[0] for r in records.values()),
            "equal_zero_certificate_results": equal_zero,
            "largest_layer_loss_with_all_certificate_sums_at_least_n": late_layer,
            "scope": "exhaustive finite rank counts; entropy computed numerically; no universal claim"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, nargs="+", choices=(3, 4, 5), default=[3, 4, 5])
    parser.add_argument("--output")
    args = parser.parse_args()
    data = json.dumps([probe(n) for n in args.wires], indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(data)
    print(data)


if __name__ == "__main__":
    main()
