"""Bounded Z3 search for a suffix on an exact lifted-prefix image.

All states are evaluated simultaneously using bit vectors. A SAT suffix is
rechecked by direct Boolean execution. UNKNOWN gives no existence conclusion.
Requires NumPy and z3-solver. No Lean or native trust extension is used.
"""
import argparse
import json
import time
import z3
from sorter_repair_interface_probe import image


def search(seed, tail_depth, timeout_ms):
    n = 16
    prefix_depth, states = image(8, 2, 1, seed)
    states = sorted(states)
    width = len(states)
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    values = [z3.BitVecVal(sum(((x >> i) & 1) << r for r, x in enumerate(states)), width)
              for i in range(n)]
    selected = []
    for layer in range(tail_depth):
        # Every active gate has span <= 2^(remaining layers + 1)-1.
        span = (1 << (tail_depth-layer))-1
        gates = {(i, j): z3.Bool(f'gate_{layer}_{i}_{j}')
                 for i in range(n) for j in range(i+1, n) if j-i <= span}
        selected.append(gates)
        following = []
        for i in range(n):
            incident = [(edge, use) for edge, use in gates.items() if i in edge]
            solver.add(z3.PbLe([(use, 1) for _, use in incident], 1))
            expr = values[i]
            for (a, b), use in incident:
                operation = values[a] & values[b] if i == a else values[a] | values[b]
                expr = z3.If(use, operation, expr)
            value = z3.BitVec(f'value_{layer+1}_{i}', width)
            solver.add(value == expr)
            following.append(value)
        values = following
    for i in range(n):
        target = sum(int(x.bit_count() >= n-i) << r for r, x in enumerate(states))
        solver.add(values[i] == z3.BitVecVal(target, width))
    start = time.monotonic()
    result = solver.check()
    record = dict(seed=seed, prefix_depth=prefix_depth, tail_depth=tail_depth,
                  states=width, timeout_ms=timeout_ms, result=str(result),
                  solve_seconds=round(time.monotonic()-start, 3))
    if result == z3.sat:
        model = solver.model()
        layers = [[edge for edge, use in gates.items() if z3.is_true(model.eval(use))]
                  for gates in selected]
        for original in states:
            x = original
            for layer in layers:
                for a, b in layer:
                    if (x >> a) & 1 and not (x >> b) & 1:
                        x ^= (1 << a) | (1 << b)
            expected = ((1 << original.bit_count())-1) << (n-original.bit_count())
            if x != expected:
                raise RuntimeError(f'Invalid SAT model on state {original}')
        record.update(layers=layers, direct_check='every reachable state passed')
    elif result == z3.unknown:
        record['reason'] = solver.reason_unknown()
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--identity', action='store_true')
    parser.add_argument('--tail-depth', type=int, default=4)
    parser.add_argument('--timeout-ms', type=int, default=60000)
    args = parser.parse_args()
    print(json.dumps(search(None if args.identity else args.seed,
                            args.tail_depth, args.timeout_ms), indent=2))
