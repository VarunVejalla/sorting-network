#!/usr/bin/env python3
"""Exact finite investigation of weighted pairwise union-cost potentials.

The closed upper recurrence is a mathematical certificate-union bound, not
an exact update rule. Computed multipliers are finite observations only.
"""
import argparse
from collections import deque
from fractions import Fraction
import json
from math import lcm
import random

from kahale_joint_potential import minimum_sizes, parallel_layers


def probe(n):
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    target = tuple(sum((x.bit_count() >= n - i) << x for x in range(1 << n)) for i in range(n))
    states, index, parents, edges = [initial], {initial: 0}, [None], []
    actions = parallel_layers(n)
    for source, state in enumerate(states):
        row = []
        for layer in actions:
            out = list(state)
            width = 0
            for i, j in layer:
                a, b = state[i], state[j]
                out[i], out[j] = a & b, a | b
                if out[i] != a:
                    width = max(width, j - i)
            out = tuple(out)
            if out not in index:
                index[out] = len(states)
                states.append(out)
                parents.append((source, layer))
            row.append((index[out], width))
        edges.append(row)
    reverse = [[] for _ in states]
    for source, row in enumerate(edges):
        for dest, _ in row:
            reverse[dest].append(source)
    distances, queue = {index[target]: 0}, deque([index[target]])
    while queue:
        dest = queue.popleft()
        for source in reverse[dest]:
            if source not in distances:
                distances[source] = distances[dest] + 1
                queue.append(source)

    cache = {}
    def size(f):
        if f not in cache:
            cache[f] = minimum_sizes(f, n)
        return cache[f]

    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    matrices = []
    for state in states:
        z, o = [[0] * n for _ in range(n)], [[0] * n for _ in range(n)]
        for i in range(n):
            z[i][i], o[i][i] = size(state[i])
        for i, j in pairs:
            z[i][j] = z[j][i] = size(state[i] | state[j])[0]
            o[i][j] = o[j][i] = size(state[i] & state[j])[1]
        matrices.append((z, o))

    def signature(matrix):
        return tuple(tuple(row) for mat in matrix for row in mat)

    def closure(matrix, layer):
        z, o = ([row[:] for row in mat] for mat in matrix)
        for i, j in layer:
            oldz, oldo = [row[:] for row in z], [row[:] for row in o]
            z[i][i], z[j][j] = min(oldz[i][i], oldz[j][j]), oldz[i][j]
            o[i][i], o[j][j] = oldo[i][j], min(oldo[i][i], oldo[j][j])
            for k in range(n):
                if k in (i, j):
                    continue
                z[i][k] = z[k][i] = min(oldz[i][k], oldz[j][k])
                z[j][k] = z[k][j] = min(n, oldz[i][k] + oldz[j][j],
                    oldz[j][k] + oldz[i][i], oldz[i][j] + oldz[k][k])
                o[j][k] = o[k][j] = min(oldo[i][k], oldo[j][k])
                o[i][k] = o[k][i] = min(n, oldo[i][k] + oldo[j][j],
                    oldo[j][k] + oldo[i][i], oldo[i][j] + oldo[k][k])
            # OR and AND of the two gate outputs equal those of its inputs.
            z[i][j] = z[j][i] = oldz[i][j]
            o[i][j] = o[j][i] = oldo[i][j]
        return z, o

    denominator_scale = lcm(*range(1, n))
    weights = {}
    for mode in ("uniform", "inverse_distance", "suffix_capped_distance"):
        for suffix in range(n + 1):
            weights[mode, suffix] = [denominator_scale if mode == "uniform" else
                denominator_scale // (j - i) * (1 if mode == "inverse_distance" else
                    min(1 << suffix, j - i)) for i, j in pairs]

    def potential(matrix, mode, suffix):
        z, o = matrix
        return sum(w * (z[i][j] + o[i][j]) for (i, j), w in zip(pairs, weights[mode, suffix]))

    signatures = [signature(m) for m in matrices]
    recorded = {}
    measured = set()
    nonclosed = None
    maxima = {}
    closure_slack = 0
    def path(source):
        result = []
        while parents[source] is not None:
            source, layer = parents[source]
            result.append(layer)
        return list(reversed(result))

    for source, row in enumerate(edges):
        for action, ((dest, width), layer) in enumerate(zip(row, actions)):
            key = (signatures[source], layer)
            previous = recorded.get(key)
            if previous is None:
                recorded[key] = (signatures[dest], source, dest)
            elif previous[0] != signatures[dest] and nonclosed is None:
                psource, pdest = previous[1:]
                changes = [(kind, i, j, matrices[pdest][kind][i][j], matrices[dest][kind][i][j])
                    for kind in (0, 1) for i in range(n) for j in range(i, n)
                    if matrices[pdest][kind][i][j] != matrices[dest][kind][i][j]]
                nonclosed = {"first_prefix": path(psource), "second_prefix": path(source),
                    "layer": layer, "changed_costs_kind_0_zero_1_one": changes,
                    "common_input_matrices": matrices[source]}
            measurement_key = (signatures[source], action, signatures[dest], width, distances[dest])
            if measurement_key in measured:
                continue
            measured.add(measurement_key)
            bound = closure(matrices[source], layer)
            # Count violations explicitly; never rely on disabled assertions.
            for kind in (0, 1):
                for i in range(n):
                    for j in range(n):
                        if matrices[dest][kind][i][j] > bound[kind][i][j]:
                            raise RuntimeError("proposed upper recurrence failed")
            closure_slack = max(closure_slack, sum(bound[k][i][j] - matrices[dest][k][i][j]
                for k in (0, 1) for i, j in pairs))
            for mode in ("uniform", "inverse_distance", "suffix_capped_distance"):
                for suffix in range(1, n + 1):
                    # Only transitions with a real sorting completion within
                    # the budget enter suffix experiments (strong finite oracle).
                    if distances[dest] > suffix - 1 or width > (1 << suffix) - 1:
                        continue
                    denominator = potential(matrices[source], mode, suffix)
                    actual = Fraction(potential(matrices[dest], mode, suffix - 1), denominator)
                    upper = Fraction(potential(bound, mode, suffix - 1), denominator)
                    key = (mode, suffix)
                    prev = maxima.get(key, (Fraction(0), Fraction(0)))
                    maxima[key] = (max(prev[0], actual), max(prev[1], upper))
    return {"wires": n, "states": len(states), "pair_matrix_signatures": len(set(signatures)),
        "distinct_measured_transition_summaries": len(measured),
        "exact_initial_depth": distances[0], "nonclosed_pair_matrix_witness": nonclosed,
        "largest_unweighted_closure_slack": closure_slack,
        "suffix_potential_maxima": [{"weight": mode, "remaining_layers_before_gate": suffix,
            "actual_multiplier": str(values[0]), "closed_upper_multiplier": str(values[1])}
            for (mode, suffix), values in sorted(maxima.items())],
        "scope": "exact finite computation; maxima use a finite completion oracle, not universal constants"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, nargs="+", choices=(3, 4, 5), default=[3, 4])
    parser.add_argument("--output")
    parser.add_argument("--sample-six", type=int, default=0,
                        help="additional seeded six-wire prefixes; not exhaustive")
    args = parser.parse_args()
    results = [probe(n) for n in args.wires]
    if args.sample_six:
        results.append(sample_six(args.sample_six))
    data = json.dumps(results, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(data)
    print(data)


def sample_six(trials):
    n, rng = 6, random.Random(20261004)
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    actions, cache, seen, matrices = parallel_layers(n), {}, {}, {}
    def size(f):
        if f not in cache:
            cache[f] = minimum_sizes(f, n)
        return cache[f]
    def matrix(state):
        if state not in matrices:
            diagonal = tuple(size(f) for f in state)
            pairs = tuple((size(state[i] | state[j])[0], size(state[i] & state[j])[1])
                          for i in range(n) for j in range(i + 1, n))
            matrices[state] = diagonal + pairs
        return matrices[state]
    for trial in range(trials):
        state, path = initial, []
        for _ in range(rng.randrange(1, 18)):
            layer = rng.choice(actions)
            out = list(state)
            for i, j in layer:
                out[i], out[j] = state[i] & state[j], state[i] | state[j]
            state = tuple(out)
            path.append(layer)
        signature = matrix(state)
        for i in range(n):
            for j in range(i + 1, n):
                out = list(state)
                out[i], out[j] = state[i] & state[j], state[i] | state[j]
                output = matrix(tuple(out))
                key = (signature, i, j)
                prev = seen.get(key)
                if prev is not None and prev[0] != output:
                    return {"wires": n, "sampling": True, "seed": 20261004,
                        "prefixes_examined": trial + 1,
                        "nonclosed_pair_matrix_witness": {"first_prefix": prev[1],
                            "second_prefix": path, "comparator": (i, j),
                            "common_signature_diagonal_then_pairs": signature,
                            "first_output_signature": prev[0], "second_output_signature": output},
                        "scope": "exact evaluated counterexample from seeded sampling; not exhaustive"}
                if prev is None:
                    seen[key] = (output, path)
    return {"wires": n, "sampling": True, "seed": 20261004,
            "prefixes_examined": trials, "nonclosed_pair_matrix_witness": None,
            "sampled_pair_matrix_signatures": len({matrix(s) for s in matrices}),
            "scope": "seeded finite sampling; absence of counterexamples proves nothing general"}


if __name__ == "__main__":
    main()
