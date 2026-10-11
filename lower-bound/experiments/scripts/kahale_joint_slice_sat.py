"""SMT feasibility of one shared network sorting specified weight slices.

SAT witnesses are independently executed. UNSAT/UNKNOWN are solver reports,
not Lean proofs. No first-layer or other unproved symmetry restriction.
"""
import argparse
from itertools import combinations
import json
from time import monotonic

import z3


def query(n, weights, depth, timeout):
    inputs = [x for x in range(1 << n) if x.bit_count() in weights]
    width = len(inputs)
    gates = list(combinations(range(n), 2))
    solver = z3.Solver()
    solver.set(timeout=timeout, random_seed=0)
    current = [z3.BitVecVal(sum(((x >> i) & 1) << r for r, x in enumerate(inputs)), width)
               for i in range(n)]
    choices = []
    for t in range(depth):
        selected = [z3.Bool(f"g_{t}_{a}_{b}") for a, b in gates]
        choices.append(selected)
        out = [z3.BitVec(f"v_{t}_{i}", width) for i in range(n)]
        for i in range(n):
            incident = [g for g, pair in zip(selected, gates) if i in pair]
            solver.add(z3.AtMost(*incident, 1))
            solver.add(z3.Implies(z3.Not(z3.Or(*incident)), out[i] == current[i]))
        for g, (a, b) in zip(selected, gates):
            solver.add(z3.Implies(g, out[a] == current[a] & current[b]))
            solver.add(z3.Implies(g, out[b] == current[a] | current[b]))
        current = out
    for i in range(n):
        desired = sum(int(i >= n - x.bit_count()) << r for r, x in enumerate(inputs))
        solver.add(current[i] == z3.BitVecVal(desired, width))
    start = monotonic()
    status = solver.check()
    elapsed = monotonic() - start
    result = dict(wires=n, weights=weights, depth_at_most=depth,
                  status=str(status), solve_seconds=round(elapsed, 3),
                  input_count=width, timeout_ms=timeout)
    if status == z3.unknown:
        result["reason"] = solver.reason_unknown()
    if status == z3.sat:
        model = solver.model()
        layers = [[pair for g, pair in zip(selected, gates)
                   if z3.is_true(model.eval(g, model_completion=True))] for selected in choices]
        heights = [0] * n
        equal_gates, gate_count = 0, 0
        output = list(range(1 << n))
        for layer in layers:
            assert len({i for pair in layer for i in pair}) == 2 * len(layer)
            for a, b in layer:
                gate_count += 1
                equal_gates += heights[a] == heights[b]
                heights[a], heights[b] = min(heights[a], heights[b]), max(heights[a], heights[b]) + 1
                for x, v in enumerate(output):
                    if v & (1 << a) and not v & (1 << b):
                        output[x] = v ^ (1 << a) ^ (1 << b)
        completed = []
        for w in range(1, n):
            desired = ((1 << w) - 1) << (n - w)
            if all(output[x] == desired for x in range(1 << n) if x.bit_count() == w):
                completed.append(w)
        assert set(weights) <= set(completed)
        result.update(layers=layers, all_completed_middle_weights=completed,
                      equal_height_comparators=equal_gates, total_comparators=gate_count,
                      witness_checked_on_all_target_inputs=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=6)
    parser.add_argument("--timeout-ms", type=int, default=5000)
    parser.add_argument("--depths", type=int, nargs="+", default=[3, 4, 5])
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    center = args.wires // 2
    targets = [[center], [center, center + 1] if args.wires % 2 else [center - 1, center]]
    queries = []
    for weights in targets:
        for depth in args.depths:
            result = query(args.wires, weights, depth, args.timeout_ms)
            queries.append(result)
            print(json.dumps({k: v for k, v in result.items() if k != "layers"}), flush=True)
            if result["status"] == "sat":
                break
    result = dict(solver="z3", solver_version=z3.get_version_string(), random_seed=0,
                  unproved_symmetry_restrictions=False, queries=queries,
                  status="SMT feasibility only; UNKNOWN is inconclusive and UNSAT is not kernel-checked")
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
