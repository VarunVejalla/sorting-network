"""Centered relative-order entropy banks on exact rank-fiber witnesses.

Counts are exact, entropy is numerical. No local bank inequality is asserted.
"""
import argparse
from collections import Counter
from itertools import combinations, permutations
import json
from math import factorial, log2


def entropy(counts):
    total = sum(counts)
    return log2(total) - sum(q * log2(q) for q in counts if q) / total


def advance(distribution, gates):
    result = Counter()
    for state, weight in distribution.items():
        out = list(state)
        for i, j in gates:
            out[i], out[j] = sorted((out[i], out[j]))
        result[tuple(out)] += weight
    return result


def features(distribution, n):
    initial_entropy = log2(factorial(n))
    gained = initial_entropy - entropy(distribution.values())
    result = []
    for k in range(2, n):
        subsets = list(combinations(range(n), k))
        conditional = []
        for subset in subsets:
            vectors, rank_sets = Counter(), Counter()
            for state, weight in distribution.items():
                vector = tuple(state[i] for i in subset)
                vectors[vector] += weight
                rank_sets[tuple(sorted(vector))] += weight
            conditional.append(entropy(vectors.values()) - entropy(rank_sets.values()))
        completion = n / k * (log2(factorial(k)) - sum(conditional) / len(subsets))
        terminal_completion = n / k * log2(factorial(k))
        alpha = terminal_completion / initial_entropy
        result.append({"subset_size": k, "completion": completion, "alpha": alpha,
                       "centered_bank": completion - alpha * gained})
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witnesses", default="docs/kahale-layer-bank-results.json")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    with open(args.witnesses, encoding="utf-8") as handle:
        witnesses = json.load(handle)
    result = []
    for entry in witnesses:
        n = entry["wires"]
        initial = Counter(permutations(range(n)))
        final = Counter({tuple(range(n)): factorial(n)})
        rows = []
        for direction, witness in entry["boundary_unchanged_witnesses"].items():
            before = advance(initial, witness["prefix"])
            after = advance(before, witness["layer"])
            bf, af = features(before, n), features(after, n)
            rows.append({"witness": direction, "prefix": witness["prefix"],
                         "layer": witness["layer"], "gain": entropy(before.values()) - entropy(after.values()),
                         "before": bf, "after": af,
                         "bank_changes": [{"subset_size": b["subset_size"],
                             "change": a["centered_bank"] - b["centered_bank"]}
                             for b, a in zip(bf, af)]})
        result.append({"wires": n, "initial": features(initial, n), "final": features(final, n),
                       "transitions": rows,
                       "scope": "Exact rank counts; numerical entropy; no charging theorem"})
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    for entry in result:
        for row in entry["transitions"]:
            print(entry["wires"], row["witness"], row["bank_changes"])
