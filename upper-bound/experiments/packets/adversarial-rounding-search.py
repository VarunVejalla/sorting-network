#!/usr/bin/env python3
"""Heuristic search for high-spill profiles under fixed integer cycles.

This is an adversarial finite search, not a maximum certificate. It runs
simulated annealing over binary and unrestricted integer threshold profiles.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from matching_cycle_screen import cycle_matrix  # noqa: E402


def schedule(packet_count: int, rounds: int, seed: int) -> list[tuple[np.ndarray, np.ndarray]]:
    _, matchings = cycle_matrix(packet_count, rounds, seed)
    return [
        (np.asarray([edge[0] for edge in matching]), np.asarray([edge[1] for edge in matching]))
        for matching in matchings
    ]


def evaluate(profile: np.ndarray, cycle: list[tuple[np.ndarray, np.ndarray]]) -> tuple[float, np.ndarray]:
    state = profile.copy()
    for left, right in cycle:
        total = state[left] + state[right]
        state[left] = (total + 1) // 2
        state[right] = total // 2
    mean = float(profile.mean())
    spill = float(np.maximum(state - mean, 0).sum())
    return spill, state


def search(
    packet_count: int,
    rounds: int,
    cycle_seed: int,
    mode: str,
    rng_seed: int,
    steps: int,
) -> dict[str, object]:
    rng = np.random.default_rng(rng_seed)
    cycle = schedule(packet_count, rounds, cycle_seed)
    if mode == "binary":
        current = 64 * rng.integers(0, 2, size=packet_count)
    else:
        current = rng.integers(0, 65, size=packet_count)
    score, _ = evaluate(current, cycle)
    best_score, best_profile = score, current.copy()

    initial_score = score
    for step in range(steps):
        candidate = current.copy()
        index = int(rng.integers(packet_count))
        if mode == "binary":
            candidate[index] = 64 - candidate[index]
            temperature = 4.0
        elif rng.random() < 0.6:
            candidate[index] = int(rng.integers(65))
            temperature = 8.0
        else:
            candidate[index] = int(np.clip(candidate[index] + rng.integers(-12, 13), 0, 64))
            temperature = 8.0

        candidate_score, _ = evaluate(candidate, cycle)
        temperature = temperature * (1 - step / steps) + 0.05
        if candidate_score >= score or rng.random() < np.exp((candidate_score - score) / temperature):
            current, score = candidate, candidate_score
        if candidate_score > best_score:
            best_score, best_profile = candidate_score, candidate.copy()

    _, final = evaluate(best_profile, cycle)
    mean = float(best_profile.mean())
    return {
        "mode": mode,
        "search_seed": rng_seed,
        "initial_spill_fraction": initial_score / (64 * packet_count),
        "best_spill_fraction": best_score / (64 * packet_count),
        "best_raw_spill": best_score,
        "final_range": int(final.max() - final.min()),
        "profile": [int(x) for x in best_profile],
        "final_profile": [int(x) for x in final],
        "mean": mean,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--rounds", type=int, default=26)
    parser.add_argument("--restarts", type=int, default=5)
    parser.add_argument("--steps", type=int, default=6000)
    parser.add_argument("--save", help="optional JSON output path")
    args = parser.parse_args()

    rows = []
    for c in args.packets:
        cycle_seed = 25_000 + args.rounds * 1_000 + c
        for mode in ("binary", "integer"):
            for restart in range(args.restarts):
                rng_seed = 700 + restart
                result = search(c, args.rounds, cycle_seed, mode, rng_seed, args.steps)
                rows.append({
                    "packets": c,
                    "rounds": args.rounds,
                    "cycle_seed": cycle_seed,
                    **result,
                })
    result = {
        "status": "heuristic finite search only; not a maximum or universal bound",
        "search": "single-coordinate simulated annealing; binary {0,64} and integer [0,64] profiles",
        "results": rows,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.save:
        Path(args.save).write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
