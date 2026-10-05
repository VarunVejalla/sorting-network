"""Challenge a linear relative-order bank on all small reachable distributions.

This is a numerical finite obstruction search, not a coefficient proof.
"""
import argparse
from collections import Counter
import json
from math import factorial
from scipy.optimize import linprog

from kahale_joint_potential import parallel_layers
from kahale_layer_bank import catalogue, entropy
from kahale_relative_order_bank import features
from kahale_boundary_information import joint_features, joint_block_features, boundary_block_scales


def probe(n, endpoint_cap, joint_boundary=False, joint_blocks=False):
    ranks, rank_index, states, index, parents = catalogue(n)
    total = factorial(n)
    banks, uniform, fixed, entropies = [], [], [], []
    feature_names = [str(k) for k in range(2, n)]
    if joint_boundary:
        feature_names += [f"boundary_{k}" for k in range(2, n - 1)]
    if joint_blocks:
        feature_names += [f"boundary_{k}_{size}" for k, size in boundary_block_scales(n)]
    feature_count = len(feature_names)
    for counts in states:
        distribution = Counter({p: q for p, q in zip(ranks, counts) if q})
        values = [row["centered_bank"] for row in features(distribution, n)]
        if joint_boundary:
            values += [row["boundary_bank"] for row in joint_features(distribution, n)
                       if row["subset_size"] < n - 1]
        if joint_blocks:
            values += [row["boundary_bank"] for row in joint_block_features(distribution, n)]
        banks.append(values)
        entropies.append(entropy(counts))
        marginals = [[0] * n for _ in range(n)]
        for p, q in distribution.items():
            for i, rank in enumerate(p):
                marginals[i][rank] += q
        uniform.append(sum(all(q * n == total for q in m) for m in marginals))
        fixed.append(sum(max(m) == total for m in marginals))
    print("Computed", len(states), "relative-order snapshots", flush=True)
    layers = parallel_layers(n)
    transports = []
    for layer in layers:
        row = []
        for p in ranks:
            out = list(p)
            for i, j in layer:
                out[i], out[j] = sorted((out[i], out[j]))
            row.append(rank_index[tuple(out)])
        transports.append(row)
    constraints, rhs, edges = [], [], []
    for source, counts in enumerate(states):
        support = [(p, q) for p, q in enumerate(counts) if q]
        for action, transport in enumerate(transports):
            out = [0] * total
            for p, q in support:
                out[transport[p]] += q
            dest = index[tuple(out)]
            constraints.append([b - a for a, b in zip(banks[source], banks[dest])] +
                [uniform[dest] - uniform[source], fixed[source] - fixed[dest], -(n // 2)])
            rhs.append(entropies[dest] - entropies[source])
            edges.append((source, action, dest))
    # Keep boundary credit fixed at an O(n) cost; never infer an asymptotic
    # coefficient from the resulting fit on one finite size.
    if endpoint_cap is not None:
        constraints.append([0] * feature_count + [1, 1, 0])
        rhs.append(endpoint_cap)
    fit = linprog([0] * (feature_count + 2) + [1], A_ub=constraints, b_ub=rhs,
                  bounds=[(None, None)] * feature_count + [(0, None)] * 3, method="highs")
    result = {"wires": n, "reachable_rank_distributions": len(states), "layers": len(layers),
              "boundary_credit_cap_per_wire": endpoint_cap, "fit_status": fit.message,
              "joint_boundary_features": joint_boundary, "feature_names": feature_names,
              "joint_block_features": joint_blocks,
              "scope": "Exhaustive finite counts; numerical entropies and LP; no universal claim"}
    if fit.success:
        weights = fit.x[:feature_count]
        kappa, lam, rate = map(float, fit.x[feature_count:])
        result.update(scale_weights={k: float(w) for k, w in zip(feature_names, weights)},
                      kappa=kappa, lambda_=lam, worst_charge_fraction=rate)
        def path(source):
            result = []
            while parents[source] is not None:
                source, gate = parents[source]
                result.append(gate)
            return list(reversed(result))
        critical = []
        for source, action, dest in edges:
            gain = entropies[source] - entropies[dest]
            change = sum(w * (b - a) for w, a, b in zip(weights, banks[source], banks[dest])) + \
                kappa * (uniform[dest] - uniform[source]) - lam * (fixed[dest] - fixed[source])
            critical.append((gain + change, source, action, dest))
        result["worst_transitions"] = [{"prefix": path(source), "layer": layers[action],
            "charge": charge, "gain": entropies[source] - entropies[dest],
            "relative_banks_before": banks[source], "relative_banks_after": banks[dest],
            "uniform_before": uniform[source], "uniform_after": uniform[dest],
            "fixed_before": fixed[source], "fixed_after": fixed[dest]}
            for charge, source, action, dest in sorted(critical, reverse=True)[:5]]
        edge_marginals = fit.ineqlin.marginals[:len(edges)]
        dual = [-float(q) for q in edge_marginals]
        active = [(q, edge) for q, edge in zip(dual, edges) if q > 1e-8]
        result["numerical_dual_obstruction"] = {
            "weighted_capacity": sum(dual) * (n // 2),
            "weighted_gain": sum(q * (entropies[s] - entropies[d])
                                 for q, (s, _, d) in zip(dual, edges)),
            "relative_bank_drift": [sum(q * (banks[d][k] - banks[s][k])
                for q, (s, _, d) in zip(dual, edges)) for k in range(feature_count)],
            "uniform_drift": sum(q * (uniform[d] - uniform[s]) for q, (s, _, d) in zip(dual, edges)),
            "fixed_drift": sum(q * (fixed[d] - fixed[s]) for q, (s, _, d) in zip(dual, edges)),
            "endpoint_cap_multiplier": -float(fit.ineqlin.marginals[-1]) if endpoint_cap is not None else 0.0,
            "support_size": len(active),
            "transitions": [{"weight": q, "prefix": path(s), "layer": layers[a],
                "gain": entropies[s] - entropies[d],
                "relative_bank_change": [b - c for c, b in zip(banks[s], banks[d])],
                "uniform_change": uniform[d] - uniform[s], "fixed_change": fixed[d] - fixed[s]}
                for q, (s, a, d) in active],
            "status": "Floating-point dual certificate; not a kernel-checked obstruction"}
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(3, 4, 5), default=5)
    parser.add_argument("--endpoint-cap", type=float, default=2)
    parser.add_argument("--joint-boundary", action="store_true")
    parser.add_argument("--joint-blocks", action="store_true")
    parser.add_argument("--unbounded-boundary", action="store_true")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires, None if args.unbounded_boundary else args.endpoint_cap,
                   args.joint_boundary, args.joint_blocks)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(result.get("worst_charge_fraction"), result.get("scale_weights"), flush=True)
