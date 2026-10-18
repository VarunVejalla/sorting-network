#!/usr/bin/env python3
"""SAT-check whether one finite dyadic comparator schedule sorts."""

from __future__ import annotations

import argparse
import random

from z3 import And, Bool, Not, Or, Solver, Tactic, is_true, sat


def make_layers(
    n: int, rounds: int, seed: int, nested: bool = False
) -> list[list[tuple[int, int]]]:
    if n < 2 or n & (n - 1):
        raise ValueError("n must be a power of two >= 2")
    rng = random.Random(seed)
    layers: list[list[tuple[int, int]]] = []
    for k in reversed(range(n.bit_length() - 1)):
        half = 1 << k
        for offset in (0, 1):
            for round_index in range(rounds):
                layer: list[tuple[int, int]] = []
                for left in range(offset * half, n - 2 * half + 1, 2 * half):
                    right = list(range(left + half, left + 2 * half))
                    if nested:
                        # Keep each local matching stable as n or rounds grow.
                        local_rng = random.Random(
                            f"{seed}:{k}:{offset}:{round_index}:{left}"
                        )
                        local_rng.shuffle(right)
                    else:
                        rng.shuffle(right)
                    layer.extend(zip(range(left, left + half), right))
                layers.append(layer)
    return layers


def check(
    n: int,
    rounds: int,
    seed: int,
    timeout_ms: int = 30_000,
    engine: str = "smt",
    nested: bool = False,
    solver_seed: int | None = None,
) -> tuple[bool | None, str | None, int]:
    wires = [Bool(f"x_{i}") for i in range(n)]
    original = wires[:]
    layers = make_layers(n, rounds, seed, nested)
    solver = Tactic("sat").solver() if engine == "sat" else Solver()
    if engine == "cnf":
        # Materialize each comparator output once and constrain its truth table
        # directly, avoiding deeply nested And/Or formulas in the SAT miter.
        for layer_index, layer in enumerate(layers):
            before = wires[:]
            after = before[:]
            for gate_index, (a, b) in enumerate(layer):
                lo = Bool(f"lo_{layer_index}_{gate_index}")
                hi = Bool(f"hi_{layer_index}_{gate_index}")
                x, y = before[a], before[b]
                solver.add(Or(Not(lo), x), Or(Not(lo), y), Or(lo, Not(x), Not(y)))
                solver.add(Or(hi, Not(x)), Or(hi, Not(y)), Or(Not(hi), x, y))
                after[a], after[b] = lo, hi
            wires = after
    else:
        for layer in layers:
            before = wires[:]
            for a, b in layer:
                wires[a], wires[b] = And(before[a], before[b]), Or(before[a], before[b])
    solver.set(timeout=timeout_ms)
    if solver_seed is not None:
        solver.set(random_seed=solver_seed)
    solver.add(Or(*(And(wires[i], Not(wires[i + 1])) for i in range(n - 1))))
    result = solver.check()
    if result == sat:
        model = solver.model()
        witness = "".join(
            "1" if is_true(model.eval(bit, model_completion=True)) else "0"
            for bit in original
        )
        return False, witness, len(layers)
    if str(result) != "unsat":
        return None, None, len(layers)
    return True, None, len(layers)


def evaluate(bits: list[bool], layers: list[list[tuple[int, int]]]) -> list[bool]:
    wires = bits[:]
    for layer in layers:
        before = wires[:]
        for a, b in layer:
            wires[a], wires[b] = before[a] and before[b], before[a] or before[b]
    return wires


def shrink_witness(
    bits: list[bool], layers: list[list[tuple[int, int]]]
) -> tuple[int, list[int], list[int]]:
    output = evaluate(bits, layers)
    pair = next(i for i in range(len(bits) - 1) if output[i] and not output[i + 1])
    one_set = {i for i, bit in enumerate(bits) if bit}
    for i in sorted(one_set):
        candidate = one_set - {i}
        forced = [j in candidate for j in range(len(bits))]
        if evaluate(forced, layers)[pair]:
            one_set = candidate
    zero_set = {i for i, bit in enumerate(bits) if not bit}
    for i in sorted(zero_set):
        candidate = zero_set - {i}
        forced = [j not in candidate for j in range(len(bits))]
        if not evaluate(forced, layers)[pair + 1]:
            zero_set = candidate
    return pair, sorted(one_set), sorted(zero_set)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--seed", type=int, default=500001)
    parser.add_argument("--timeout-ms", type=int, default=30_000)
    parser.add_argument("--engine", choices=("smt", "sat", "cnf"), default="smt")
    parser.add_argument("--nested", action="store_true")
    parser.add_argument("--solver-seed", type=int)
    args = parser.parse_args()
    sorts, witness, layer_count = check(
        args.n,
        args.rounds,
        args.seed,
        args.timeout_ms,
        args.engine,
        args.nested,
        args.solver_seed,
    )
    print(
        f"n={args.n} rounds={args.rounds} seed={args.seed} nested={args.nested} layers={layer_count} "
        f"status={'sorts' if sorts is True else 'fails' if sorts is False else 'unknown'} "
        f"witness={witness}"
    )
    if witness is not None:
        layers = make_layers(args.n, args.rounds, args.seed, args.nested)
        bits = [bit == "1" for bit in witness]
        ones = sum(bits)
        misplaced = sum(bits[: args.n - ones])
        runs = 1 + sum(a != b for a, b in zip(bits, bits[1:]))
        pair, one_set, zero_set = shrink_witness(
            bits, layers
        )
        print(
            f"bad_pair=({pair},{pair + 1}) one_certificate={one_set} "
            f"zero_certificate={zero_set}"
        )
        print(f"ones={ones} displaced_ones={misplaced} input_runs={runs}")


if __name__ == "__main__":
    main()
