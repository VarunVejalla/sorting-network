#!/usr/bin/env python3
"""Exhaustively screen single-swap inputs using bit-parallel simulation.

These are necessary test cases for sorting, not a sufficient test for an
arbitrary comparator network.
"""

from __future__ import annotations

import argparse
import random


def make_layers(n: int, rounds: int, seed: int) -> list[list[tuple[int, int]]]:
    if n < 2 or n & (n - 1):
        raise ValueError("n must be a power of two >= 2")
    rng = random.Random(seed)
    layers = []
    for k in reversed(range(n.bit_length() - 1)):
        half = 1 << k
        for offset in (0, 1):
            for _ in range(rounds):
                layer = []
                for left in range(offset * half, n - 2 * half + 1, 2 * half):
                    right = list(range(left + half, left + 2 * half))
                    rng.shuffle(right)
                    layer.extend(zip(range(left, left + half), right))
                layers.append(layer)
    return layers


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    # Start from every sorted threshold profile, then swap one 1 left of the
    # cut with one 0 right of it.
    profiles = []
    for cut in range(args.n):
        base = sum(1 << i for i in range(cut + 1, args.n))
        for p in range(cut + 1):
            for q in range(cut + 1, args.n):
                profiles.append((p, cut, q, (base | (1 << p)) & ~(1 << q)))

    wires = [0] * args.n
    for profile_id, (_, _, _, bits) in enumerate(profiles):
        for wire in range(args.n):
            if bits >> wire & 1:
                wires[wire] |= 1 << profile_id
    full = (1 << len(profiles)) - 1
    for layer in make_layers(args.n, args.rounds, args.seed):
        before = wires[:]
        for a, b in layer:
            wires[a], wires[b] = before[a] & before[b], before[a] | before[b]

    for i in range(args.n - 1):
        bad = wires[i] & (full ^ wires[i + 1])
        if bad:
            profile = profiles[(bad & -bad).bit_length() - 1]
            print(
                f"n={args.n} rounds={args.rounds} seed={args.seed} "
                f"profiles={len(profiles)} sorts_single_swap=False "
                f"witness=(p,cut,q)={profile[:3]} bad_pair=({i},{i + 1})"
            )
            return
    print(
        f"n={args.n} rounds={args.rounds} seed={args.seed} "
        f"profiles={len(profiles)} sorts_single_swap=True"
    )


if __name__ == "__main__":
    main()
