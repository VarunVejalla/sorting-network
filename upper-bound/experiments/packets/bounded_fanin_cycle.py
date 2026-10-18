#!/usr/bin/env python3
"""Exact finite screen for bounded-fanin matching cycles, c <= 130.

The product is represented by integer numerators over 2**rounds. For each c,
the script deterministically searches seeds and certifies an exact
Frobenius-norm bound; it is a computational artifact, not Lean.
"""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path


MAX_C = 130
TARGET_RHO = Fraction(1, 16)


def product_numerator(c: int, seed: int, rounds: int) -> tuple[list[list[int]], list[list[list[int]]]]:
    rng = random.Random(seed)
    matrix = [[int(i == j) for j in range(c)] for i in range(c)]
    matchings: list[list[list[int]]] = []
    for _ in range(rounds):
        order = list(range(c))
        rng.shuffle(order)
        edges = [[order[k], order[k + 1]] for k in range(0, c - 1, 2)]
        matchings.append(edges)
        updated = [[2 * x for x in row] for row in matrix]
        for left, right in edges:
            average_row = [a + b for a, b in zip(matrix[left], matrix[right])]
            updated[left] = average_row
            updated[right] = average_row.copy()
        matrix = updated
    return matrix, matchings


def frobenius_certificate(matrix: list[list[int]], c: int, rounds: int) -> tuple[int, int]:
    scale = 1 << rounds
    denominator = c * c * scale * scale
    numerator = sum(
        (c * entry - scale) ** 2
        for row in matrix
        for entry in row
    )
    return numerator, denominator


def find_cycle(c: int, rounds: int, attempts: int) -> dict[str, object]:
    best: tuple[Fraction, int, int, list[list[list[int]]]] | None = None
    for attempt in range(attempts):
        seed = 0x0B25 + c * 1009 + attempt * 9973
        matrix, matchings = product_numerator(c, seed, rounds)
        numerator, denominator = frobenius_certificate(matrix, c, rounds)
        rho2 = Fraction(numerator, denominator)
        if best is None or rho2 < best[0]:
            best = (rho2, seed, numerator, matchings)
    assert best is not None
    rho2, seed, numerator, _matchings = best
    denominator = c * c * (1 << (2 * rounds))
    threshold = TARGET_RHO.denominator ** 2
    return {
        "c": c,
        "seed": seed,
        "frobenius_sq_numerator": numerator,
        "frobenius_sq_denominator": denominator,
        "rho_le_1_over_16": threshold * numerator <= denominator,
    }


def verify_cycle(row: dict[str, object], rounds: int) -> None:
    c = int(row["c"])
    matrix, _matchings = product_numerator(c, int(row["seed"]), rounds)
    numerator, denominator = frobenius_certificate(matrix, c, rounds)
    assert numerator == int(row["frobenius_sq_numerator"])
    assert denominator == int(row["frobenius_sq_denominator"])
    assert TARGET_RHO.denominator ** 2 * numerator <= denominator


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--rounds", type=int, default=15)
    parser.add_argument("--attempts", type=int, default=16)
    parser.add_argument("--max-c", type=int, default=MAX_C)
    args = parser.parse_args()
    rows = [find_cycle(c, args.rounds, args.attempts) for c in range(1, args.max_c + 1)]
    for row in rows:
        verify_cycle(row, args.rounds)
    result = {
        "status": "exact integer/Frobenius certificate; not Lean-checked",
        "schedule_generator": "Python random.Random; see bounded_fanin_cycle.py",
        "rounds": args.rounds,
        "seed_attempts_per_size": args.attempts,
        "max_packet_count": args.max_c,
        "per_round_matching_cost_layers": 13,
        "cycle_cost_layers": args.rounds * 13,
        "frobenius_bound": f"rho <= 1/16 for every c in 1..{args.max_c}",
        "matching_cycles": rows,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    worst = max(
        Fraction(int(row["frobenius_sq_numerator"]), int(row["frobenius_sq_denominator"]))
        for row in rows
    )
    print(f"verified_sizes=1..{args.max_c} rounds={args.rounds} depth={args.rounds * 13}")
    print(f"all_exact_Frobenius_bounds_le_1/16={all(bool(row['rho_le_1_over_16']) for row in rows)}")
    print(f"worst_frobenius_sq={worst.numerator}/{worst.denominator}")
    print(f"conditional_energy_factor_65rho2_le={65}/256={65/256:.8g}")


if __name__ == "__main__":
    main()
