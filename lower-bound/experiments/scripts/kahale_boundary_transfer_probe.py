"""Embed finite witnesses on more wires and challenge fixed fitted banks.

This deliberately performs no refitting. Counts are exact; entropy is numerical.
"""
import argparse
from collections import Counter
from itertools import combinations, permutations
import json

from kahale_boundary_information import boundary_block_information
from kahale_layer_bank import entropy
from kahale_relative_order_bank import advance, features


def probe(fits, witnesses, n):
    initial = Counter(permutations(range(n)))
    total = sum(initial.values())
    required = {name for fit in fits for name, weight in fit["scale_weights"].items()
                if name.startswith("boundary_") and abs(weight) > 1e-10}
    cache = {}
    def snapshot(distribution):
        key = tuple(sorted(distribution.items()))
        if key in cache:
            return cache[key]
        values = {str(row["subset_size"]): row["centered_bank"] for row in features(distribution, n)}
        for name in required:
            parts = list(map(int, name.split("_")[1:]))
            k, size = parts if len(parts) == 2 else (parts[0], 1)
            terms = []
            for subset in combinations(range(n), k):
                remaining = [i for i in range(n) if i not in subset]
                for outside in combinations(remaining, size):
                    terms.append(boundary_block_information(distribution, subset, outside))
            values[name] = n / k * sum(terms) / len(terms)
        marginals = [[0] * n for _ in range(n)]
        for p, q in distribution.items():
            for i, rank in enumerate(p):
                marginals[i][rank] += q
        values["uniform"] = sum(all(q * n == total for q in m) for m in marginals)
        values["fixed"] = sum(max(m) == total for m in marginals)
        values["entropy"] = entropy(distribution.values())
        cache[key] = values
        return values
    def bank(values, fit):
        return sum(weight * values.get(name, 0) for name, weight in fit["scale_weights"].items()) + \
            fit["kappa"] * values["uniform"] - fit["lambda_"] * values["fixed"]
    records = []
    seen = set()
    for witness in witnesses:
        prefix = tuple(map(tuple, witness["prefix"]))
        layer = tuple(map(tuple, witness["layer"]))
        variants = [layer]
        unused = [i for i in range(n) if all(i not in gate for gate in layer)]
        if len(unused) == 2:
            variants.append(layer + (tuple(unused),))
        for action in variants:
            if (prefix, action) in seen:
                continue
            seen.add((prefix, action))
            before = advance(initial, prefix)
            after = advance(before, action)
            bf, af = snapshot(before), snapshot(after)
            gain = bf["entropy"] - af["entropy"]
            records.append({"prefix": prefix, "layer": action, "gain": gain,
                "charges": [{"bank": fit["probe_name"],
                    "charge": gain + bank(af, fit) - bank(bf, fit),
                    "charge_fraction": (gain + bank(af, fit) - bank(bf, fit)) / (n // 2),
                    "fitted_five_wire_fraction": fit["worst_charge_fraction"]} for fit in fits]})
    return {"wires": n, "transitions": records, "distinct_snapshots": len(cache),
            "maximum_charge_fractions": {fit["probe_name"]: max(
                charge["charge_fraction"] for row in records for charge in row["charges"]
                if charge["bank"] == fit["probe_name"]) for fit in fits},
            "status": "Exact rank counts; numerical fixed-coefficient probe; not exhaustive"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(6, 7), default=6)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    fits, witnesses = [], []
    for label, path in [("single_outside", "docs/kahale-joint-boundary-challenge.json"),
                        ("outside_block", "docs/kahale-joint-block-challenge.json")]:
        with open(path, encoding="utf-8") as handle:
            fit = json.load(handle)
        fit["probe_name"] = label
        fits.append(fit)
        witnesses.extend(fit["worst_transitions"])
    with open("docs/kahale-relative-order-challenge.json", encoding="utf-8") as handle:
        witnesses.extend(json.load(handle)["numerical_dual_obstruction"]["transitions"])
    result = probe(fits, witnesses, args.wires)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(result["maximum_charge_fractions"])
