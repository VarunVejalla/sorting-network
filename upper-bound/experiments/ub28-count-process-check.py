#!/usr/bin/env python3
"""Exhaustively check the UB-28 count recurrence at n=8, one round/pass.

Enumerates all 192 independent-matching schedules and all 256 Boolean inputs,
then compares the exact block-count distribution at every pass/split against
the rational recurrence in ub28-count-process.py.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
from math import prod
from pathlib import Path
import importlib.util


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_count_process", HERE / "ub28-count-process.py")
CP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CP)


def profile(bits, n, width):
    return tuple(sum((bits >> i) & 1 for i in range(start, start + width))
                 for start in range(0, n, width))


def run_input(bits, n, choices, factors):
    state = [(bits >> i) & 1 for i in range(n)]
    hist = {}
    q = 0
    for width in (4, 2):
        for offset in (0, 1):
            for block in range(offset, n // width - 1, 2):
                _, start, _ = factors[q]
                perm = choices[q]
                q += 1
                left = [start + i for i in range(width)]
                right = [start + width + i for i in range(width)]
                for i, j in enumerate(perm):
                    a, b = state[left[i]], state[right[j]]
                    state[left[i]], state[right[j]] = min(a, b), max(a, b)
            hist[(width, offset)] = profile_from_state(state, n, width)
        if width > 1:
            hist[(width // 2, "split")] = profile_from_state(state, n, width // 2)
    for offset in (0, 1):
        for i in range(offset, n - 1, 2):
            state[i], state[i + 1] = min(state[i], state[i + 1]), max(
                state[i], state[i + 1])
        hist[(1, offset)] = tuple(state)
    return hist


def profile_from_state(state, n, width):
    return tuple(sum(state[start:start + width])
                 for start in range(0, n, width))


def recurrence_histograms(n=8):
    h = n // 2
    dist = {(a, b): Fraction(CP.comb(h, a) * CP.comb(h, b), 2**n)
            for a in range(h + 1) for b in range(h + 1)}
    expected = {("start", h): dist.copy()}
    while True:
        for offset in (0, 1):
            dist = CP.apply_pass(dist, h, offset, 1, 0)
            expected[(h, offset)] = dist.copy()
        if h == 1:
            return expected
        dist = CP.split_blocks(dist, h)
        h //= 2
        expected[(h, "split")] = dist.copy()


def main():
    n = 8
    perms = {h: tuple(permutations(range(h))) for h in (2, 4)}
    factors = []
    for h in (4, 2):
        for offset in (0, 1):
            for block in range(offset, n // h - 1, 2):
                factors.append((h, block * h, perms[h]))
    schedule_count = prod(len(options) for _, _, options in factors)
    checkpoints = recurrence_histograms(n)
    observed = {key: Counter() for key in checkpoints}
    bad_inputs = 0
    for choices in product(*(options for _, _, options in factors)):
        for bits in range(1 << n):
            hist = run_input(bits, n, choices, factors)
            observed[("start", n // 2)][profile(bits, n, n // 2)] += 1
            for key, value in hist.items():
                observed[key][value] += 1
            if any(hist[(1, 1)][i] > hist[(1, 1)][i + 1]
                   for i in range(n - 1)):
                bad_inputs += 1

    denominator = schedule_count * (1 << n)
    for key, expected in checkpoints.items():
        actual = {state: Fraction(count, denominator)
                  for state, count in observed[key].items()}
        expected = {state: p for state, p in expected.items() if p}
        assert actual == expected, f"distribution mismatch at {key}"
        print(f"{key}: {len(expected)} states, exact match")
    efail = Fraction(bad_inputs, schedule_count)
    print(f"schedules={schedule_count}; E[failing inputs]={efail}")


if __name__ == "__main__":
    main()
