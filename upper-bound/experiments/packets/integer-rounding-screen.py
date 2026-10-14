#!/usr/bin/env python3
"""Exact integer merge-and-deal dynamics on selected threshold profiles.

Finite exploratory screen only. It reuses the reproducible matching cycles
from matching_cycle_screen.py and applies the exact ceil/floor packet update.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from matching_cycle_screen import cycle_matrix  # noqa: E402


def evolve(profile: list[int], matchings: list[list[list[int]]]) -> list[int]:
    state = np.asarray(profile, dtype=np.int64)
    for matching in matchings:
        following = state.copy()
        for left, right in matching:
            total = int(state[left]) + int(state[right])
            following[left] = (total + 1) // 2
            following[right] = total // 2
        state = following
    return [int(x) for x in state]


def profiles(c: int, seed: int) -> dict[str, list[int]]:
    rng = np.random.default_rng(seed)
    return {
        "singleton": [64] + [0] * (c - 1),
        "half_extremes": [64 if j < c // 2 else 0 for j in range(c)],
        "alternating_extremes": [64 if j % 2 == 0 else 0 for j in range(c)],
        "uniform_random": [int(x) for x in rng.integers(0, 65, size=c)],
        "bernoulli_extremes": [64 * int(x) for x in rng.integers(0, 2, size=c)],
        "near_half": [31 + j % 3 for j in range(c)],
        "ramp": [round(64 * j / (c - 1)) for j in range(c)],
    }


def measure(initial: list[int], final: list[int]) -> dict[str, float | int]:
    mean = sum(initial) / len(initial)
    denom = 64 * len(initial)
    return {
        "spill_fraction_of_packet_mass": sum(max(x - mean, 0) for x in final) / denom,
        "l1_fraction_of_packet_mass": sum(abs(x - mean) for x in final) / denom,
        "max_abs_deviation": max(abs(x - mean) for x in final),
        "final_range": max(final) - min(final),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+", default=[64, 128, 256, 512, 1024])
    parser.add_argument("--rounds", type=int, default=26)
    parser.add_argument("--save", help="optional JSON output path")
    args = parser.parse_args()
    rows = []
    for c in args.packets:
        seed = 25_000 + args.rounds * 1_000 + c
        _, matchings = cycle_matrix(c, args.rounds, seed)
        for name, initial in profiles(c, 98_765 + c).items():
            final = evolve(initial, matchings)
            rows.append({
                "packets": c,
                "rounds": args.rounds,
                "schedule_seed": seed,
                "profile": name,
                **measure(initial, final),
            })
    result = {
        "status": "exact finite integer screen only; no universal rounding bound",
        "update": "(a,b) -> (ceil((a+b)/2), floor((a+b)/2))",
        "results": rows,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.save:
        Path(args.save).write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
