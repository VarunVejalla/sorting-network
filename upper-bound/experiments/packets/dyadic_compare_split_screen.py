#!/usr/bin/env python3
"""Exact small-size screen for random dyadic compare-split schedules.

This is an exploratory 0-1-principle test, not a proof for arbitrary sizes.
Each scheduled packet comparator is represented as min/max on one Boolean
wire. Exhaustive sorting at n therefore verifies the corresponding scalar
comparator network at that finite n.
"""

from __future__ import annotations

import argparse
import itertools
import random


def make_layers(n: int, rounds: int, seed: int) -> list[list[tuple[int, int]]]:
    if n < 2 or n & (n - 1):
        raise ValueError("n must be a power of two >= 2")
    rng = random.Random(seed)
    layers: list[list[tuple[int, int]]] = []
    for k in reversed(range(n.bit_length() - 1)):
        half = 1 << k
        for offset in (0, 1):
            for _ in range(rounds):
                layer: list[tuple[int, int]] = []
                for left in range(offset * half, n - 2 * half + 1, 2 * half):
                    right = list(range(left + half, left + 2 * half))
                    rng.shuffle(right)
                    layer.extend(zip(range(left, left + half), right))
                layers.append(layer)
    return layers


def first_bad_profile(
    n: int, capacity: int, layers: list[list[tuple[int, int]]]
) -> tuple[int, ...] | None:
    for profile in itertools.product(range(capacity + 1), repeat=n):
        wires = list(profile)
        for layer in layers:
            for a, b in layer:
                total = wires[a] + wires[b]
                wires[a], wires[b] = min(capacity, total), max(0, total - capacity)
        if any(wires[i] < wires[i + 1] for i in range(n - 1)):
            return profile
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--rounds", type=int, default=6)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--packet-capacity", type=int, default=1)
    parser.add_argument("--max-profiles", type=int, default=1_000_000)
    args = parser.parse_args()
    profiles = (args.packet_capacity + 1) ** args.n
    if profiles > args.max_profiles:
        parser.error(f"{profiles} profiles exceed --max-profiles={args.max_profiles}")
    layers = make_layers(args.n, args.rounds, args.seed)
    bad = first_bad_profile(args.n, args.packet_capacity, layers)
    print(
        f"n={args.n} capacity={args.packet_capacity} rounds={args.rounds} seed={args.seed} "
        f"layers={len(layers)} comparators={sum(map(len, layers))} "
        f"profiles={profiles} sorts={bad is None} witness={bad}"
    )


if __name__ == "__main__":
    main()
