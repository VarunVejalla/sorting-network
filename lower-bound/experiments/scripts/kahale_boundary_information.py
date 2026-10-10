"""Conditional boundary information from exact rank-fiber weights.

All counts are exact; entropy arithmetic is floating point. Neither a local
charging theorem nor an asymptotic coefficient is asserted.
"""
import argparse
from collections import Counter
from itertools import combinations, permutations
import json

from kahale_layer_bank import entropy
from kahale_relative_order_bank import advance


def projected_entropy(distribution, projection):
    counts = Counter()
    for p, q in distribution.items():
        counts[projection(p)] += q
    return entropy(counts.values())


def relative_entropy(distribution, subset):
    return projected_entropy(distribution, lambda p: tuple(p[i] for i in subset)) - \
        projected_entropy(distribution, lambda p: tuple(sorted(p[i] for i in subset)))


def boundary_information(distribution, subset, outside):
    return boundary_block_information(distribution, subset, (outside,))


def boundary_block_information(distribution, subset, outside):
    vector = lambda p: tuple(p[i] for i in subset)
    rank_set = lambda p: tuple(sorted(vector(p)))
    external = lambda p: tuple(p[i] for i in outside)
    return projected_entropy(distribution, vector) + \
        projected_entropy(distribution, lambda p: (rank_set(p), external(p))) - \
        projected_entropy(distribution, rank_set) - \
        projected_entropy(distribution, lambda p: (vector(p), external(p)))


def insertion_entropy(distribution, rest, moving):
    def rank_set(p):
        return tuple(sorted([p[i] for i in rest] + [p[moving]]))
    def code(p):
        return rank_set(p), sum(p[i] < p[moving] for i in rest)
    return projected_entropy(distribution, code) - projected_entropy(distribution, rank_set)


def joint_features(distribution, n):
    result = []
    for k in range(2, n):
        terms = [boundary_information(distribution, subset, b)
                 for subset in combinations(range(n), k)
                 for b in range(n) if b not in subset]
        result.append({"subset_size": k, "boundary_bank": n / k * sum(terms) / len(terms),
                       "maximum_term": max(terms)})
    return result


def boundary_block_scales(n):
    return [(k, size) for k in range(2, n - 1) for size in range(2, n - k + 1)
            if k + size < n or k <= size]


def joint_block_features(distribution, n):
    result = []
    for k, size in boundary_block_scales(n):
        terms = []
        for subset in combinations(range(n), k):
            remaining = [i for i in range(n) if i not in subset]
            for outside in combinations(remaining, size):
                terms.append(boundary_block_information(distribution, subset, outside))
        result.append({"subset_size": k, "outside_size": size,
                       "boundary_bank": n / k * sum(terms) / len(terms),
                       "maximum_term": max(terms)})
    return result


def transfer_rows(before, gate, n):
    after = advance(before, [gate])
    rows = []
    for moving in gate:
        remaining = [i for i in range(n) if i not in gate]
        for k in range(2, len(remaining) + 1):
            for rest in combinations(remaining, k):
                subset = tuple(rest) + (moving,)
                relative_change = relative_entropy(after, subset) - relative_entropy(before, subset)
                insertion_change = insertion_entropy(after, rest, moving) - insertion_entropy(before, rest, moving)
                information_change = boundary_information(after, rest, moving) - boundary_information(before, rest, moving)
                row = {"gate": gate, "rest": rest, "moving": moving,
                    "relative_entropy_change": relative_change,
                    "insertion_entropy_change": insertion_change,
                    "boundary_information_change": information_change,
                    "identity_residual": relative_change - insertion_change + information_change}
                if k == n - 2 and moving == gate[0]:
                    rank_set = lambda p: tuple(sorted(p[i] for i in rest))
                    bias_entropy = projected_entropy(before, lambda p: (rank_set(p), p[moving])) - \
                        projected_entropy(before, rank_set)
                    information = boundary_information(before, rest, moving)
                    gain = entropy(before.values()) - entropy(after.values())
                    row["single_gate_information"] = {"gain": gain,
                        "orientation_entropy_given_missing_pair": bias_entropy,
                        "relative_order_coupling": information,
                        "identity_residual": gain - bias_entropy + information}
                rows.append(row)
    return after, rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witnesses", default="docs/kahale-relative-order-challenge.json")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    with open(args.witnesses, encoding="utf-8") as handle:
        challenge = json.load(handle)
    n = challenge["wires"]
    initial = Counter(permutations(range(n)))
    final = Counter({tuple(range(n)): sum(initial.values())})
    records, transfers = [], []
    for witness in challenge["numerical_dual_obstruction"]["transitions"]:
        before = advance(initial, witness["prefix"])
        after = advance(before, witness["layer"])
        bf, af = joint_features(before, n), joint_features(after, n)
        records.append({"weight": witness["weight"], "prefix": witness["prefix"],
            "layer": witness["layer"], "before": bf, "after": af,
            "changes": [{"subset_size": b["subset_size"],
                         "change": a["boundary_bank"] - b["boundary_bank"]}
                        for b, a in zip(bf, af)]})
        state = before
        for gate in witness["layer"]:
            state, rows = transfer_rows(state, gate, n)
            transfers.extend(rows)
    data = {"wires": n, "initial": joint_features(initial, n), "final": joint_features(final, n),
        "dual_transitions": records,
        "old_dual_drift": [{"subset_size": k,
            "weighted_change": sum(row["weight"] * row["changes"][k - 2]["change"] for row in records)}
            for k in range(2, n)],
        "transfer_identity": {"instances": len(transfers),
            "maximum_absolute_residual": max(abs(row["identity_residual"]) for row in transfers),
            "largest_information_changes": sorted(transfers, key=lambda r: abs(r["boundary_information_change"]), reverse=True)[:8]},
        "single_gate_information_identity": [row["single_gate_information"]
                                             for row in transfers if "single_gate_information" in row],
        "status": "Exact projection counts; numerical entropy; no improved coefficient"}
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)
        handle.write("\n")
    print(data["old_dual_drift"])
    print(data["transfer_identity"]["maximum_absolute_residual"])
