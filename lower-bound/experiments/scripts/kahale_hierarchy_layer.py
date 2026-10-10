"""Joint parallel-layer rank-set ledger and hierarchy refinement probe.

Exact prefix multiplicities, numerical entropies. No asymptotic coefficient.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import factorial, log2

from kahale_layer_bank import catalogue, entropy
from kahale_joint_potential import parallel_layers


def partition_code(p, blocks):
    return tuple(tuple(sorted(p[i] for i in block)) for block in blocks)


def probe(n):
    ranks, rank_index, states, _, parents = catalogue(n)
    split = n // 2
    blocks = (tuple(range(split)), tuple(range(split, n)))
    membership = {i: b for b, block in enumerate(blocks) for i in block}
    rank_codes = [partition_code(p, blocks) for p in ranks]
    fine_blocks = tuple(tuple(range(start, end))
                        for start, end in ((0, 1), (1, split), (split, split + 1),
                                           (split + 1, n)) if start < end)
    fine_membership = {i: b for b, block in enumerate(fine_blocks) for i in block}
    fine_codes = [partition_code(p, fine_blocks) for p in ranks]
    layers = parallel_layers(n)
    whole = [entropy(state) for state in states]
    supports = [[(p, q) for p, q in enumerate(state) if q] for state in states]
    rank_h = []
    for support in supports:
        counts = Counter()
        for p, q in support:
            counts[rank_codes[p]] += q
        rank_h.append(entropy(counts.values()))
    maximum_error = 0.0
    maximum_conditional_loss_excess = -float("inf")
    maximum_fresh_excess = (-float("inf"), None)
    maximum_loss = (-float("inf"), None)
    maximum_joint_saving = (-float("inf"), None)
    pure_cross_error = 0.0
    maximum_gain = (-float("inf"), None)
    efficient_saving = (-float("inf"), None)
    maximum_orientation_dependence = (-float("inf"), None)
    hierarchy_identity_error = 0.0
    maximum_level_slot_excess = -float("inf")
    minimum_level_information = float("inf")
    checked = 0
    for layer in layers:
        internal = sum(membership[i] == membership[j] for i, j in layer)
        gate_levels = [0 if membership[i] != membership[j] else
                       1 if fine_membership[i] != fine_membership[j] else 2
                       for i, j in layer]
        level_slots = [gate_levels.count(level) for level in range(3)]
        transport = []
        masks = []
        for p in ranks:
            out = list(p)
            mask = 0
            for bit, (i, j) in enumerate(layer):
                if out[i] > out[j]:
                    mask |= 1 << bit
                out[i], out[j] = sorted((out[i], out[j]))
            transport.append(rank_index[tuple(out)])
            masks.append(mask)
        # Individual crossing-gate innovation, conditioned only on current
        # partition, to compare against the actual joint layer innovation.
        singles = []
        for i, j in layer:
            if membership[i] == membership[j]:
                continue
            row = []
            for p in ranks:
                out = list(p)
                out[i], out[j] = sorted((out[i], out[j]))
                row.append(partition_code(out, blocks))
            singles.append(row)
        for source, support in enumerate(supports):
            out_counts = Counter()
            output_sets = Counter()
            old_new = Counter()
            old_output = Counter()
            single_counts = [Counter() for _ in singles]
            joint_single = Counter()
            orientation_counts = [Counter() for _ in layer]
            groups = {}
            fine_output = Counter()
            cumulative_orientation = [Counter() for _ in range(3)]
            for p, q in support:
                dest = transport[p]
                out_counts[dest] += q
                output_sets[rank_codes[dest]] += q
                old_new[rank_codes[p], rank_codes[dest]] += q
                old_output[rank_codes[p], dest] += q
                fine_output[fine_codes[p], dest] += q
                for level, counts in enumerate(cumulative_orientation):
                    mask = masks[p] & sum(1 << bit for bit, assigned in enumerate(gate_levels)
                                          if assigned <= level)
                    counts[dest, mask] += q
                groups.setdefault(dest, []).append(q)
                joint_single[rank_codes[p], tuple(code[p] for code in singles)] += q
                for bit, counts in enumerate(orientation_counts):
                    counts[dest, (masks[p] >> bit) & 1] += q
                for code, counts in zip(singles, single_counts):
                    counts[rank_codes[p], code[p]] += q
            output_h = entropy(out_counts.values())
            new_h = entropy(output_sets.values())
            joint_h = entropy(old_new.values())
            old_output_h = entropy(old_output.values())
            gain = whole[source] - output_h
            fresh = joint_h - rank_h[source]
            residual = joint_h + output_h - new_h - old_output_h
            conditional_loss = whole[source] - old_output_h
            fine_loss = whole[source] - entropy(fine_output.values())
            level_information = [gain - conditional_loss, conditional_loss - fine_loss, fine_loss]
            previous_h = output_h
            for info, slots, counts in zip(level_information, level_slots, cumulative_orientation):
                next_h = entropy(counts.values())
                hierarchy_identity_error = max(hierarchy_identity_error,
                                               abs(info - next_h + previous_h))
                maximum_level_slot_excess = max(maximum_level_slot_excess, info - slots)
                minimum_level_information = min(minimum_level_information, info)
                previous_h = next_h
            error = abs(gain + new_h - rank_h[source] - fresh + residual - conditional_loss)
            maximum_error = max(maximum_error, error)
            maximum_conditional_loss_excess = max(maximum_conditional_loss_excess,
                                                  conditional_loss - internal)
            if internal == 0:
                pure_cross_error = max(pure_cross_error, abs(conditional_loss))
            single_sum = sum(entropy(c.values()) - rank_h[source] for c in single_counts)
            saving = single_sum - fresh
            tuple_h = entropy(joint_single.values()) - rank_h[source]
            rank_dependence = single_sum - tuple_h
            pairing = tuple_h - fresh
            orientation_dependence = sum(entropy(c.values()) - output_h
                                         for c in orientation_counts) - gain
            balanced = all(len(qs) == 2 ** len(layer) and len(set(qs)) == 1
                           for qs in groups.values())
            item = (source, layer, gain, fresh, residual, conditional_loss, internal,
                    saving, rank_dependence, pairing, orientation_dependence, balanced,
                    level_slots, level_information)
            if balanced and saving > efficient_saving[0]:
                efficient_saving = saving, item
            if orientation_dependence > maximum_orientation_dependence[0]:
                maximum_orientation_dependence = orientation_dependence, item
            for label, score in (("fresh", fresh - (len(layer) - internal)),
                                 ("loss", conditional_loss), ("saving", saving),
                                 ("gain", gain)):
                current = {"fresh": maximum_fresh_excess, "loss": maximum_loss,
                           "saving": maximum_joint_saving, "gain": maximum_gain}[label]
                if score > current[0]:
                    if label == "fresh": maximum_fresh_excess = score, item
                    if label == "loss": maximum_loss = score, item
                    if label == "saving": maximum_joint_saving = score, item
                    if label == "gain": maximum_gain = score, item
            checked += 1

    def witness(record):
        value, (source, layer, gain, fresh, residual, loss, internal, saving,
                rank_dependence, pairing, orientation_dependence, balanced,
                level_slots, level_information) = record
        prefix = []
        while parents[source] is not None:
            source, gate = parents[source]
            prefix.append(gate)
        return {"value": value, "prefix": prefix[::-1], "layer": layer,
                "gain": gain, "joint_innovation": fresh, "residual": residual,
                "conditional_internal_loss": loss, "internal_gates": internal,
                "single_minus_joint_innovation": saving,
                "rank_update_conditional_total_correlation": rank_dependence,
                "hidden_gate_assignment_entropy": pairing,
                "orientation_conditional_total_correlation": orientation_dependence,
                "exact_full_slot_gain_certificate": balanced,
                "hierarchy_level_slots": level_slots,
                "hierarchy_level_information": level_information}

    return {"wires": n, "blocks": blocks, "states": len(states),
            "layers": len(layers), "instances": checked,
            "maximum_identity_roundoff": maximum_error,
            "maximum_conditional_loss_minus_internal_gate_count": maximum_conditional_loss_excess,
            "pure_crossing_reconstruction_roundoff": pure_cross_error,
            "joint_innovation_exceeds_crossing_slots": witness(maximum_fresh_excess),
            "maximum_conditional_internal_loss": witness(maximum_loss),
            "maximum_parallel_dependence_saving": witness(maximum_joint_saving),
            "maximum_layer_gain": witness(maximum_gain),
            "rank_update_saving_at_exact_full_slot_gain": witness(efficient_saving),
            "maximum_orientation_dependence": witness(maximum_orientation_dependence),
            "fine_blocks": fine_blocks,
            "hierarchy_group_orientation_identity_roundoff": hierarchy_identity_error,
            "maximum_hierarchy_level_information_minus_slots": maximum_level_slot_excess,
            "minimum_hierarchy_level_information": minimum_level_information,
            "status": "Exact integer distributions; numerical entropy; no new coefficient"}


def endpoint_scaling(n):
    sizes, results = [n], []
    whole = log2(factorial(n))
    previous = 0.0
    while True:
        rank_entropy = whole - sum(log2(factorial(s)) for s in sizes)
        results.append({"block_sizes": sizes, "initial_partition_entropy": rank_entropy,
                        "increment_over_parent": rank_entropy - previous})
        if all(s == 1 for s in sizes):
            break
        previous = rank_entropy
        sizes = [t for s in sizes for t in ((s // 2, s - s // 2) if s > 1 else (1,))]
    return {"wires": n, "levels": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5), default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    result["hierarchy_endpoint_scaling"] = [endpoint_scaling(n) for n in (8, 32, 128)]
    result["fully_efficient_matching_obstruction"] = [
        {"wires": n, "crossing_comparisons": n // 2,
         "exact_joint_gain": n // 2,
         "single_innovation_sum_lower_bound": n // 2 * log2(n // 2),
         "joint_partition_innovation_upper_bound": n,
         "single_minus_joint_lower_bound": n // 2 * log2(n // 2) - n,
         "orientation_conditional_total_correlation": 0}
        for n in (16, 32, 64, 128, 256)]
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "hierarchy_endpoint_scaling"}, indent=2))
