#!/usr/bin/env python3
"""Exact integer packet-count screen for a fixed merge-and-deal schedule.

For one binary threshold, a sorted packet is determined by its number of ones.
Merging two packets and dealing alternating ranks maps their counts x,y to
floor((x+y)/2), ceil((x+y)/2). This screen applies that exact integer update
through a reproducible sequence of perfect matchings. It isolates matching
rounds; it does not model WireFlow routing, changing cohorts, or frontiers.
"""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction


def schedule(packet_count: int, rounds: int, seed: int) -> list[list[tuple[int, int]]]:
    if packet_count % 2:
        raise ValueError("packet_count must be even")
    rng = random.Random(seed)
    result = []
    for _ in range(rounds):
        order = list(range(packet_count))
        rng.shuffle(order)
        result.append(list(zip(order[::2], order[1::2])))
    return result


def l1_from_mean(counts: list[int]) -> Fraction:
    mean = Fraction(sum(counts), len(counts))
    return sum((abs(Fraction(x) - mean) for x in counts), Fraction(0))


def evolve(counts: list[int], matchings: list[list[tuple[int, int]]]) -> tuple[list[int], list[Fraction]]:
    state = counts[:]
    history = [l1_from_mean(state)]
    total = sum(state)
    for matching in matchings:
        nxt = state[:]
        for i, j in matching:
            lo = (state[i] + state[j]) // 2
            nxt[i], nxt[j] = lo, state[i] + state[j] - lo
        assert sum(nxt) == total
        state = nxt
        history.append(l1_from_mean(state))
    return state, history


def scenarios(c: int, m: int, seed: int) -> dict[str, list[int]]:
    rng = random.Random(seed)
    half = c // 2
    return {
        "single_one": [1] + [0] * (c - 1),
        "single_full_packet": [m] + [0] * (c - 1),
        "half_full": [m] * half + [0] * (c - half),
        "alternating_empty_full": [m if i % 2 else 0 for i in range(c)],
        "random_counts": [rng.randrange(m + 1) for _ in range(c)],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, default=16)
    parser.add_argument("--packet-size", type=int, default=16)
    parser.add_argument("--rounds", type=int, default=15)
    parser.add_argument("--seed", type=int, default=20261018)
    parser.add_argument("--save")
    args = parser.parse_args()
    matchings = schedule(args.packets, args.rounds, args.seed)
    results = {}
    for name, initial in scenarios(args.packets, args.packet_size, args.seed + 1).items():
        final, history = evolve(initial, matchings)
        results[name] = {
            "initial_counts": initial,
            "final_counts": final,
            "initial_l1_from_mean": str(history[0]),
            "final_l1_from_mean": str(history[-1]),
        }
    output = {
        "status": "exact finite integer simulation; matching rounds only, not the WireFlow scheduler",
        "packets": args.packets,
        "packet_size": args.packet_size,
        "rounds": args.rounds,
        "seed": args.seed,
        "update": "matched counts x,y become floor((x+y)/2), ceil((x+y)/2)",
        "scenarios": results,
    }
    encoded = json.dumps(output, indent=2)
    if args.save:
        with open(args.save, "w", encoding="utf-8") as out:
            out.write(encoded + "\n")
    print(encoded)


if __name__ == "__main__":
    main()
