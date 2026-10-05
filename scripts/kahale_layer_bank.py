"""Exhaustive small rank distributions for a whole-layer correlation bank.

Integer fiber weights are exact; entropies and LP fitting are numerical.
This investigates a candidate, not an asymptotic theorem.
"""
import argparse
from collections import defaultdict
from itertools import permutations
import json
from math import factorial, log2
from scipy.optimize import linprog

from kahale_joint_potential import parallel_layers


def entropy(weights):
    total = sum(weights)
    return log2(total) - sum(q * log2(q) for q in weights if q) / total


def catalogue(n):
    ranks = list(permutations(range(n)))
    rank_index = {p: i for i, p in enumerate(ranks)}
    gates = [(i, j) for i in range(n) for j in range(i + 1, n)]
    transports = []
    for i, j in gates:
        row = []
        for p in ranks:
            out = list(p)
            out[i], out[j] = sorted((out[i], out[j]))
            row.append(rank_index[tuple(out)])
        transports.append(row)
    initial = (1,) * len(ranks)
    states, index, parents = [initial], {initial: 0}, [None]
    for source, counts in enumerate(states):
        for gate, transport in zip(gates, transports):
            out = [0] * len(ranks)
            for p, q in enumerate(counts):
                out[transport[p]] += q
            out = tuple(out)
            if out not in index:
                index[out] = len(states)
                states.append(out)
                parents.append((source, gate))
    return ranks, rank_index, states, index, parents


def probe(n):
    ranks, rank_index, states, index, parents = catalogue(n)
    layers = parallel_layers(n)
    total = factorial(n)
    rows, qbank, uniform_wires, fixed_wires = [], [], [], []
    for counts in states:
        marginals = [[0] * n for _ in range(n)]
        for p, weight in enumerate(counts):
            for i, rank in enumerate(ranks[p]):
                marginals[i][rank] += weight
        uniform_wires.append(sum(all(q * n == total for q in m) for m in marginals))
        fixed_wires.append(sum(max(m) == total for m in marginals))
        state_rows = []
        for layer in layers:
            groups = defaultdict(dict)
            output_counts = [0] * total
            for p, weight in enumerate(counts):
                if not weight:
                    continue
                out = list(ranks[p])
                mask = 0
                for bit, (i, j) in enumerate(layer):
                    if out[i] > out[j]:
                        mask |= 1 << bit
                    out[i], out[j] = sorted((out[i], out[j]))
                dest = rank_index[tuple(out)]
                groups[dest][mask] = weight
                output_counts[dest] += weight
            joint, marginal = 0.0, 0.0
            for orientations in groups.values():
                mass = sum(orientations.values())
                joint += mass / total * entropy(orientations.values())
                for bit in range(len(layer)):
                    ones = sum(q for mask, q in orientations.items() if mask >> bit & 1)
                    marginal += mass / total * entropy((ones, mass - ones))
            state_rows.append({"destination": index[tuple(output_counts)], "gain": joint,
                               "marginal_entropy": marginal,
                               "conditional_total_correlation": marginal - joint})
        rows.append(state_rows)
        qbank.append(max(row["conditional_total_correlation"] for row in state_rows))
    capacity = n // 2
    constraints, rhs, edges = [], [], []
    for source, state_rows in enumerate(rows):
        for action, row in enumerate(state_rows):
            # B=-beta*Q: gain + delta B <= r*capacity.
            constraints.append([qbank[source] - qbank[row["destination"]], -capacity])
            rhs.append(-row["gain"])
            edges.append((source, action))
    fit = linprog([0, 1], A_ub=constraints, b_ub=rhs,
                  bounds=[(0, None), (0, None)], method="highs")
    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return list(reversed(result))
    summary = {"wires": n, "reachable_rank_distributions": len(states),
               "layers": len(layers), "bank": "B=-beta*max_layer conditional_TC",
               "initial_Q": qbank[0], "sorted_Q": qbank[index[(total,) + (0,) * (total - 1)]],
               "maximum_Q": max(qbank), "fit_status": fit.message}
    if fit.success:
        beta, rate = fit.x
        ranked = []
        for source, action in edges:
            row = rows[source][action]
            charge = row["gain"] + beta * (qbank[source] - qbank[row["destination"]])
            ranked.append((charge, source, action))
        summary.update(beta=float(beta), worst_charge_fraction=float(rate),
                       coefficient_if_universal=2 / float(rate),
                       worst_transitions=[{"prefix": path(source), "layer": layers[action],
                           "charge": charge, "Q_before": qbank[source],
                           "Q_after": qbank[rows[source][action]["destination"]],
                           **rows[source][action]}
                           for charge, source, action in sorted(ranked, reverse=True)[:5]])
    summary["scope"] = "Exhaustive small distributions; numerical LP; no universal bound"
    boundary_constraints = []
    for source, action in edges:
        dest = rows[source][action]["destination"]
        boundary_constraints.append([qbank[source] - qbank[dest],
            uniform_wires[dest] - uniform_wires[source],
            fixed_wires[source] - fixed_wires[dest], -capacity])
    boundary_fit = linprog([0, 0, 0, 1], A_ub=boundary_constraints, b_ub=rhs,
                          bounds=[(0, None)] * 4, method="highs")
    if boundary_fit.success:
        beta, first, last, rate = map(float, boundary_fit.x)
        boundary_edges = []
        for source, action in edges:
            row = rows[source][action]
            dest = row["destination"]
            charge = row["gain"] + beta * (qbank[source] - qbank[dest]) + \
                first * (uniform_wires[dest] - uniform_wires[source]) + \
                last * (fixed_wires[source] - fixed_wires[dest])
            boundary_edges.append((charge, source, action))
        summary["boundary_bank_fit"] = {
            "bank": "B=kappa*uniform_wires-lambda*fixed_wires-beta*Q",
            "beta": beta, "kappa": first, "lambda": last,
            "endpoint_cost_per_wire": first + last, "worst_charge_fraction": rate,
            "worst_transitions": [{"prefix": path(source), "layer": layers[action],
                "charge": charge, "uniform_before": uniform_wires[source],
                "uniform_after": uniform_wires[rows[source][action]["destination"]],
                "fixed_before": fixed_wires[source],
                "fixed_after": fixed_wires[rows[source][action]["destination"]],
                "Q_before": qbank[source],
                "Q_after": qbank[rows[source][action]["destination"]],
                **rows[source][action]}
                for charge, source, action in sorted(boundary_edges, reverse=True)[:5]]}
    signed_fit = linprog([0, 0, 0, 1], A_ub=boundary_constraints, b_ub=rhs,
                        bounds=[(None, None)] + [(0, None)] * 3, method="highs")
    if signed_fit.success:
        beta, first, last, rate = map(float, signed_fit.x)
        summary["signed_boundary_bank_fit"] = {
            "beta": beta, "kappa": first, "lambda": last,
            "endpoint_cost_per_wire": first + last,
            "worst_charge_fraction": rate,
            "scope": "Allows either sign of beta; still only a finite numerical fit"}
    blockers = {}
    for source, action in edges:
        row = rows[source][action]
        dest = row["destination"]
        if uniform_wires[source] != uniform_wires[dest] or fixed_wires[source] != fixed_wires[dest]:
            continue
        change = qbank[dest] - qbank[source]
        direction = "increase" if change > 1e-10 else "decrease" if change < -1e-10 else "unchanged"
        if direction not in blockers or row["gain"] > blockers[direction][0]:
            blockers[direction] = (row["gain"], source, action)
    summary["boundary_unchanged_witnesses"] = {
        direction: {"prefix": path(source), "layer": layers[action],
                    "Q_change": qbank[rows[source][action]["destination"]] - qbank[source],
                    "Q_before": qbank[source],
                    "Q_after": qbank[rows[source][action]["destination"]],
                    "uniform_wires": uniform_wires[source], "fixed_wires": fixed_wires[source],
                    **rows[source][action]}
        for direction, (_, source, action) in blockers.items()}
    if "increase" in blockers and "decrease" in blockers:
        ga, sa, aa = blockers["increase"]
        gb, sb, ab = blockers["decrease"]
        qa = qbank[rows[sa][aa]["destination"]] - qbank[sa]
        qb = qbank[sb] - qbank[rows[sb][ab]["destination"]]
        summary["two_witness_lower_bound_on_charge_fraction"] = (qb * ga + qa * gb) / (qa + qb) / capacity
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", nargs="+", type=int, choices=(3, 4, 5), default=[3, 4])
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = [probe(n) for n in args.wires]
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    for row in result:
        print(row["wires"], row.get("beta"), row.get("worst_charge_fraction"),
              row.get("boundary_bank_fit", {}).get("worst_charge_fraction"))
