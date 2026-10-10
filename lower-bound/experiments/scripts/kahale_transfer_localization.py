"""Exhaustive finite probe of where whole-complement coupling can increase.

Exact rank counts, numerical entropies. This is not a formal information
inequality or an asymptotic depth improvement.
"""
import argparse
from collections import Counter
from itertools import combinations
import json

from kahale_layer_bank import catalogue, entropy


def projection_entropy(ranks, support, projection):
    counts = Counter()
    for p, q in support:
        counts[projection(ranks[p])] += q
    return entropy(counts.values())


def probe(n):
    ranks, rank_index, states, index, parents = catalogue(n)
    subsets = [s for k in range(2, n - 1) for s in combinations(range(n), k)]
    gates = [(i, j) for i in range(n) for j in range(i + 1, n)]
    profiles, singles, entropies, touched = [], [], [], []
    for state_id, counts in enumerate(states):
        support = [(p, q) for p, q in enumerate(counts) if q]
        full_entropy = entropy(counts)
        entropies.append(full_entropy)
        if parents[state_id] is None:
            touched.append(0)
        else:
            parent, (i, j) = parents[state_id]
            touched.append(touched[parent] | (1 << i) | (1 << j))
        vectors = {}
        for subset in subsets:
            vectors[subset] = projection_entropy(ranks, support, lambda p, s=subset: tuple(p[i] for i in s))
        block_rows, single_rows = [], []
        for subset in subsets:
            outside = tuple(i for i in range(n) if i not in subset)
            rank_set = lambda p, s=subset: tuple(sorted(p[i] for i in s))
            set_entropy = projection_entropy(ranks, support, rank_set)
            block_rows.append(vectors[subset] + vectors[outside] - set_entropy - full_entropy)
            values = {}
            for b in outside:
                union = tuple(sorted(subset + (b,)))
                # The largest union has n-1 ranks and reconstructs the last.
                joint = vectors[union] if union in vectors else full_entropy
                mixed = projection_entropy(ranks, support, lambda p, b=b, r=rank_set: (r(p), p[b]))
                values[b] = vectors[subset] + mixed - set_entropy - joint
            single_rows.append(values)
        profiles.append(block_rows)
        singles.append(single_rows)
    transports = []
    for i, j in gates:
        row = []
        for p in ranks:
            out = list(p)
            out[i], out[j] = sorted((out[i], out[j]))
            row.append(rank_index[tuple(out)])
        transports.append(row)
    maxima = {kind: (-float("inf"), None) for kind in ("inside", "outside", "crossing")}
    single_max = (-float("inf"), None)
    checked = {kind: 0 for kind in maxima}
    efficient = {"any_prefix": (-float("inf"), None), "all_wires_touched": (-float("inf"), None)}
    for source, counts in enumerate(states):
        support = [(p, q) for p, q in enumerate(counts) if q]
        for gate, transport in zip(gates, transports):
            out = [0] * len(ranks)
            groups = {}
            for p, q in support:
                out[transport[p]] += q
                groups.setdefault(transport[p], []).append(q)
            dest = index[tuple(out)]
            gain = entropies[source] - entropies[dest]
            balanced = all(len(weights) == 2 and weights[0] == weights[1]
                           for weights in groups.values())
            for a, subset in enumerate(subsets):
                inside = sum(i in subset for i in gate)
                kind = "inside" if inside == 2 else "outside" if inside == 0 else "crossing"
                change = profiles[dest][a] - profiles[source][a]
                checked[kind] += 1
                if change > maxima[kind][0]:
                    maxima[kind] = (change, (source, dest, gate, a))
                if kind == "crossing" and balanced:
                    for label in efficient:
                        if label == "all_wires_touched" and touched[source] != (1 << n) - 1:
                            continue
                        if change > efficient[label][0]:
                            efficient[label] = (change, (source, dest, gate, a))
                if kind == "outside":
                    for b, before in singles[source][a].items():
                        rise = singles[dest][a][b] - before
                        if rise > single_max[0]:
                            single_max = (rise, (source, dest, gate, a, b))
    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return list(reversed(result))
    def witness(item):
        change, (source, dest, gate, a) = item
        return {"change": change, "prefix": path(source), "gate": gate, "subset": subsets[a],
                "whole_before": profiles[source][a], "whole_after": profiles[dest][a],
                "gate_gain": entropies[source] - entropies[dest]}
    rise, (source, dest, gate, a, b) = single_max
    return {"wires": n, "reachable_rank_distributions": len(states), "instances": checked,
            "largest_whole_coupling_changes": {kind: witness(item) for kind, item in maxima.items()},
            "coupling_creation_at_one_bit_gain": {label: {**witness(item),
                "exact_count_certificate": "Every output has two equal-weight predecessors"}
                for label, item in efficient.items()
                                                 if item[1] is not None},
            "single_outside_increase": {"increase": rise, "prefix": path(source), "gate": gate,
                "subset": subsets[a], "observed_wire": b,
                "single_before": singles[source][a][b], "single_after": singles[dest][a][b],
                "whole_before": profiles[source][a], "whole_after": profiles[dest][a]},
            "status": "Exhaustive integer rank counts; numerical entropy; no new coefficient"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5), default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print({k: v["change"] for k, v in result["largest_whole_coupling_changes"].items()})
    print(result["single_outside_increase"])
