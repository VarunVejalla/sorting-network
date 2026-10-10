#!/usr/bin/env python3
"""Search all Boolean inputs symbolically for a coalition routing deficit.

SAT witnesses are re-evaluated as integer/Boolean circuits. UNSAT reports
depend on Z3 and are not Lean proofs. Unknown is never treated as UNSAT.
"""
import argparse
import json
import z3

from kahale_height_barrier import fib
from kahale_positional_barrier import layers, expand_layer
from kahale_rank_congestion import bits, matching_witness, coalition_diagnostics


def search(depth, suffix_depth, zeros, timeout_ms, mode="symbolic"):
    n = (1 << depth) // ((depth + 1) * fib(depth + 1))
    if not 1 <= n <= 1000 or not 0 <= suffix_depth <= depth or not 0 <= zeros <= n:
        raise ValueError("unsupported arity, suffix depth, or zero count")
    cut = depth - suffix_depth
    schedule = [list(expand_layer(block)) for block in layers(n, depth)]
    reach = [1 << i for i in range(n)]
    for layer in reversed(schedule[cut:]):
        for i, j in layer:
            reach[i] = reach[j] = reach[i] | reach[j]
    target = (1 << zeros) - 1
    full = (1 << n) - 1
    solver = z3.Solver()
    solver.set(timeout=timeout_ms, random_seed=0)
    inputs = [z3.Bool(f"input_zero_{i}") for i in range(n)]
    values = inputs[:]
    for t, layer in enumerate(schedule[:cut]):
        for i, j in layer:
            lo, hi = z3.Bool(f"gate_{t}_{i}_lo"), z3.Bool(f"gate_{t}_{i}_hi")
            solver.add(lo == z3.Or(values[i], values[j]), hi == z3.And(values[i], values[j]))
            values[i], values[j] = lo, hi
    solver.add(z3.PbEq([(v, 1) for v in inputs], zeros))
    for i in range(n):
        if not reach[i] & target:
            solver.add(z3.Not(values[i]))
        if not reach[i] & (full ^ target):
            solver.add(values[i])
    parent = list(range(n))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for layer in schedule[cut:]:
        for i, j in layer:
            parent[root(j)] = root(i)
    groups = {}
    for i in range(n):
        groups.setdefault(root(i), []).append(i)
    for group in groups.values():
        solver.add(z3.PbEq([(values[i], 1) for i in group], sum(i < zeros for i in group)))

    cut_count = None
    if mode == "symbolic":
        chosen = [z3.Bool(f"source_{i}") for i in range(n)]
        destinations = [z3.Bool(f"destination_{j}") for j in range(zeros)]
        for i in range(n):
            solver.add(z3.Implies(chosen[i], values[i]))
            for j in bits(reach[i] & target):
                solver.add(z3.Implies(chosen[i], destinations[j]))
        solver.add(z3.Sum([z3.If(a, 1, 0) for a in chosen]) >
                   z3.Sum([z3.If(b, 1, 0) for b in destinations]))
    else:
        # Restricted destination-cut family: unions of one/two neighborhoods
        # and neighborhoods of contiguous source intervals. UNSAT in this
        # mode excludes only this family, not every possible Hall witness.
        masks = list({mask & target for mask in reach if mask & target})
        pool = set(masks)
        pool.update(a | b for a in masks for b in masks)
        for start in range(n):
            union = 0
            for end in range(start, n):
                union |= reach[end] & target
                if union.bit_count() >= zeros:
                    break
                pool.add(union)
        cuts = set()
        for mask in pool:
            if not mask or mask.bit_count() >= zeros:
                continue
            cohort = tuple(i for i in range(n) if reach[i] & target and
                           not (reach[i] & target & ~mask))
            if len(cohort) > mask.bit_count():
                cuts.add((cohort, mask.bit_count()))
        cut_count = len(cuts)
        solver.add(z3.Or([z3.PbGe([(values[i], 1) for i in cohort], capacity + 1)
                          for cohort, capacity in sorted(cuts)]))
    status = solver.check()
    result = {"depth": depth, "wires": n, "remaining_layers": suffix_depth,
              "zero_count": zeros, "timeout_ms": timeout_ms, "solver_result": str(status),
              "search_mode": mode, "destination_cut_count": cut_count,
              "z3_version": z3.get_version_string(),
              "scope": "symbolic finite search; solver UNSAT is not a kernel proof"}
    if status == z3.unknown:
        result["reason_unknown"] = solver.reason_unknown()
    if status == z3.sat:
        model = solver.model()
        original = [0 if z3.is_true(model.eval(v, model_completion=True)) else 1 for v in inputs]
        prefix = original[:]
        for layer in schedule[:cut]:
            for i, j in layer:
                prefix[i], prefix[j] = min(prefix[i], prefix[j]), max(prefix[i], prefix[j])
        if original.count(0) != zeros:
            raise RuntimeError("incorrect support size")
        if not all(reach[i] & (target if prefix[i] == 0 else full ^ target) for i in range(n)):
            raise RuntimeError("singleton condition failed")
        if not all(sum(prefix[i] == 0 for i in group) == sum(i < zeros for i in group)
                   for group in groups.values()):
            raise RuntimeError("component capacity failed")
        witness = matching_witness([i for i in range(n) if prefix[i] == 0], reach, target)
        if witness is None:
            raise RuntimeError("no exact Hall witness")
        entry = {"cut": cut, "color": 0, "zero_count": zeros, "input": original,
                 "prefix_values": prefix, "all_singleton_routes_possible": True,
                 "suffix_component_capacities_match": True, "hall_witness": witness}
        entry["coalition_diagnostics"] = coalition_diagnostics(entry, reach, n)
        result["witness"] = entry
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=40)
    parser.add_argument("--suffix", type=int, nargs="+", default=[5, 6, 7])
    parser.add_argument("--zeros", type=int, default=88)
    parser.add_argument("--timeout-ms", type=int, default=15000)
    parser.add_argument("--mode", choices=("symbolic", "cuts"), default="symbolic")
    parser.add_argument("--output")
    args = parser.parse_args()
    data = json.dumps([search(args.depth, s, args.zeros, args.timeout_ms, args.mode)
                      for s in args.suffix], indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(data)
    print(data)


if __name__ == "__main__":
    main()
