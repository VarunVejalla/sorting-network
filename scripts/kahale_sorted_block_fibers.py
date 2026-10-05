"""Exact interleaving counts for two sorted blocks; research diagnostic."""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from math import comb, log2


def probe(k):
    states = []
    for chosen in combinations(range(2 * k), k):
        selected = set(chosen)
        states.append(chosen + tuple(x for x in range(2 * k) if x not in selected))
    total = len(states)
    single = []
    for r in range(k):
        counts = Counter()
        for state in states:
            out = list(state)
            out[r], out[k + r] = sorted((out[r], out[k + r]))
            counts[tuple(out)] += 1
        gain = sum(q * log2(q) for q in counts.values()) / total
        formula = Fraction(2 * comb(2 * r, r) * comb(2 * k - 2 * r - 2, k - r - 1), total)
        single.append({"rank": r + 1, "gain": gain, "predicted_gain": str(formula),
                       "fiber_size_histogram": dict(Counter(counts.values()))})
    counts = Counter()
    for state in states:
        out = list(state)
        for r in range(k):
            out[r], out[k + r] = sorted((out[r], out[k + r]))
        counts[tuple(out)] += 1
    return {"block_size": k, "interleavings": total, "single_gate": single,
            "parallel_layer_gain": sum(q * log2(q) for q in counts.values()) / total,
            "predicted_layer_gain": str(Fraction(4 ** k, total) - 1),
            "sum_initial_single_gate_gains": sum(row["gain"] for row in single),
            "layer_fiber_size_histogram": dict(Counter(counts.values()))}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-block-size", type=int, default=8)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = {"status": "Exact counts; numerical entropy; no asymptotic improvement proved",
              "families": [probe(k) for k in range(1, args.max_block_size + 1)]}
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    for row in result["families"]:
        print(row["block_size"], row["parallel_layer_gain"], row["sum_initial_single_gate_gains"])
