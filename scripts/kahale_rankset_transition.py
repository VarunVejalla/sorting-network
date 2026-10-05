"""Exact-count, numerical-entropy probe of crossing rank-set innovations.

All reachable distributions and single comparators at four/five wires.
The path bound allows sequential gates, so it is not a depth theorem.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import comb, log2

from kahale_layer_bank import catalogue, entropy


def probe(n):
    ranks, rank_index, states, index, parents = catalogue(n)
    subsets = list(combinations(range(n), n // 2))
    codes = [[tuple(sorted(p[i] for i in block)) for p in ranks]
             for block in subsets]
    supports = [[(p, q) for p, q in enumerate(state) if q] for state in states]
    whole = [entropy(state) for state in states]
    rank_entropies = []
    for support in supports:
        rank_entropies.append([
            entropy(_counts(support, code).values()) for code in codes])
    gates = list(combinations(range(n), 2))
    transports = []
    for i, j in gates:
        transport = []
        for p in ranks:
            out = list(p)
            out[i], out[j] = sorted((out[i], out[j]))
            transport.append(rank_index[tuple(out)])
        transports.append(transport)
    # The integer positional moment strictly increases on any changed state.
    moment = [sum(q * sum(i * r for i, r in enumerate(ranks[p]))
                  for p, q in support) for support in supports]
    best = [-float("inf")] * len(states)
    best[0] = 0.0
    predecessor = [None] * len(states)
    max_creation = (-float("inf"), None)
    max_zero_gain = (-float("inf"), None)
    max_residual = (-float("inf"), None)
    residual_min = float("inf")
    identity_error = 0.0
    instances = 0
    for source in sorted(range(len(states)), key=moment.__getitem__):
        for gate, transport in zip(gates, transports):
            out = [0] * len(ranks)
            groups = {}
            for p, q in supports[source]:
                dest_p = transport[p]
                out[dest_p] += q
                groups.setdefault(dest_p, []).append(q)
            dest = index[tuple(out)]
            if source == dest:
                continue
            if moment[dest] <= moment[source]:
                raise ValueError("Nontrivial transition failed the moment order")
            gain = whole[source] - whole[dest]
            zero_gain = all(len(weights) == 1 for weights in groups.values())
            innovation_average = 0.0
            for a, (block, code) in enumerate(zip(subsets, codes)):
                if sum(i in block for i in gate) != 1:
                    continue
                joint = Counter()
                old_output = Counter()
                for p, q in supports[source]:
                    joint[code[p], code[transport[p]]] += q
                    old_output[code[p], transport[p]] += q
                joint_h = entropy(joint.values())
                innovation = joint_h - rank_entropies[source][a]
                residual = (joint_h + whole[dest] - rank_entropies[dest][a]
                            - entropy(old_output.values()))
                delta_rank = rank_entropies[dest][a] - rank_entropies[source][a]
                identity_error = max(identity_error, abs(gain + delta_rank - innovation + residual))
                residual_min = min(residual_min, residual)
                instances += 1
                innovation_average += innovation / len(subsets)
                item = (source, dest, gate, block, gain, innovation, residual, delta_rank)
                if innovation > max_creation[0]:
                    max_creation = innovation, item
                if zero_gain and innovation > max_zero_gain[0]:
                    max_zero_gain = innovation, item
                if residual > max_residual[0]:
                    max_residual = residual, item
            if best[source] + innovation_average > best[dest]:
                best[dest] = best[source] + innovation_average
                predecessor[dest] = source, gate
    # Lexicographic permutation order puts the identity first, not last.
    sorted_counts = [0] * len(ranks)
    sorted_counts[rank_index[tuple(range(n))]] = sum(states[0])
    sorted_id = index[tuple(sorted_counts)]

    def path(state, parent_map):
        result = []
        while parent_map[state] is not None:
            state, gate = parent_map[state]
            result.append(gate)
        return result[::-1]

    def witness(record):
        if record[1] is None:
            return None
        _, (source, dest, gate, block, gain, innovation, residual, delta) = record
        return {"prefix": path(source, parents), "gate": gate, "block": block,
                "gain": gain, "innovation": innovation, "residual": residual,
                "rank_entropy_change": delta}

    maximizing_path = path(sorted_id, predecessor)
    current = list(range(len(ranks)))
    histories = [[(code[p],) for p in current] for code in codes]
    gate_transport = dict(zip(gates, transports))
    for gate in maximizing_path:
        current = [gate_transport[gate][p] for p in current]
        for code, block_histories in zip(codes, histories):
            for p, image in enumerate(current):
                block_histories[p] += (code[image],)
    fresh_average = (sum(entropy(Counter(h).values()) for h in histories) /
                     len(subsets) - sum(rank_entropies[0]) / len(subsets))
    return {"wires": n, "states": len(states), "crossing_instances": instances,
            "maximum_identity_roundoff": identity_error,
            "minimum_residual": residual_min,
            "maximum_innovation": witness(max_creation),
            "maximum_residual": witness(max_residual),
            "innovation_at_exact_zero_gain": witness(max_zero_gain),
            "maximum_cumulative_averaged_innovation_to_sort": best[sorted_id],
            "initial_averaged_rank_entropy": sum(rank_entropies[0]) / len(subsets),
            "whole_input_entropy": whole[0],
            "fresh_history_innovation_on_maximizing_path": fresh_average,
            "fresh_history_innovation_upper_bound": whole[0] -
                sum(rank_entropies[0]) / len(subsets),
            "maximizing_sequential_path": maximizing_path,
            "status": "Exact integer distributions; numerical entropy; no new coefficient"}


def _counts(support, code):
    counts = Counter()
    for p, q in support:
        counts[code[p]] += q
    return counts


def uniform_scaling(n):
    """First crossing gate on uniform permutations, without enumerating n!.

    For a fixed k-set S, m(S) inversion pairs each give a distinct new set;
    all other endpoint pairs leave S unchanged. Integer rank-set counts give
    the output entropy, and the conditional entropy has a closed formula.
    """
    k = n // 2
    v = k * (n - k)
    count = comb(n, k)
    innovation_sum = 0.0
    output_weights = []
    for subset in combinations(range(n), k):
        m = sum(subset) - k * (k - 1) // 2
        unchanged = 1 - m / v
        innovation_sum += (m / v * log2(v) -
                           (unchanged * log2(unchanged) if unchanged else 0))
        output_weights.append(2 * (v - m))
    innovation = innovation_sum / count
    delta = entropy(output_weights) - log2(count)
    return {"wires": n, "block_size": k, "innovation": innovation,
            "innovation_lower_bound": log2(v) / 2,
            "rank_entropy_change": delta, "gain": 1,
            "residual": innovation - 1 - delta}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5), default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    result["uniform_first_crossing_scaling"] = [
        uniform_scaling(n) for n in (4, 6, 8, 12, 16, 20)]
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
