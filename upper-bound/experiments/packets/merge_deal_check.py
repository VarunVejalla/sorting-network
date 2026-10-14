#!/usr/bin/env python3
"""Exhaustively screen Boolean merge-and-deal on sorted packet inputs.

This mirrors AKS.Bitonic.bitonicMerge's recursive half-cleaner: compare each
wire in the lower half with the corresponding upper-half wire, then recurse
on both halves. It checks the candidate primitive, not the Lean implementation
or its all-width proof (those are covered by the source theorem plus a future
adapter theorem).
"""

from itertools import product
import argparse


def bitonic_merge(xs):
    if len(xs) <= 1:
        return xs
    half = len(xs) // 2
    low = [min(xs[i], xs[i + half]) for i in range(half)]
    high = [max(xs[i], xs[i + half]) for i in range(half)]
    return bitonic_merge(low) + bitonic_merge(high)


def check(max_q):
    checked = 0
    for q in range(max_q + 1):
        m = 1 << q
        for x, y in product(range(m + 1), repeat=2):
            left = [False] * x + [True] * (m - x)
            right = [False] * y + [True] * (m - y)
            merged = bitonic_merge(left + list(reversed(right)))
            assert merged == sorted(merged), (q, x, y, merged)

            even, odd = merged[::2], merged[1::2]
            assert even == sorted(even), (q, x, y, even)
            assert odd == sorted(odd), (q, x, y, odd)
            assert even.count(False) == (x + y + 1) // 2, (q, x, y, even)
            assert odd.count(False) == (x + y) // 2, (q, x, y, odd)
            checked += 1
    return checked


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-q", type=int, default=8)
    args = parser.parse_args()
    print(f"checked {check(args.max_q)} sorted-Boolean packet pairs through q={args.max_q}")
