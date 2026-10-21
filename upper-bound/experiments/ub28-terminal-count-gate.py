#!/usr/bin/env python3
"""Exact failure mass through the UB-28 randomized prefix and exact tail.

Unlike ub28-terminal-gate-mass.py, this applies the actual deterministic
count transformation of the width-4, width-2, and width-1 exact-split tail.
For an exact cross-block splitter, output block counts depend only on the
input pair's total. The internal arrangements therefore do not affect the
tail's final bit word: after the width-1 even pass, each width-2 block is
sorted, and the final odd pass is determined by those block counts.

This is a finite n=32 diagnostic for the randomized prefix ensemble. It does
not bound the recurrence uniformly in n.
"""

import argparse
from fractions import Fraction
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_count_process", HERE / "ub28-count-process.py"
)
count_process = importlib.util.module_from_spec(spec)
spec.loader.exec_module(count_process)


def exact_pass(state, offset, h):
    """Apply exact pair splitting to a vector of h-block one-counts."""
    result = list(state)
    for left in range(offset, len(state) - 1, 2):
        total = state[left] + state[left + 1]
        result[left] = max(total - h, 0)
        result[left + 1] = min(total, h)
    return tuple(result)


def tail_output(profile):
    """Return the final Boolean word after exact h=4,2,1 tail stages."""
    width4 = exact_pass(exact_pass(profile, 0, 4), 1, 4)
    width2 = terminal_width2_counts(width4)
    bits = [0] * (2 * len(width2))
    for j, count in enumerate(width2):
        bits[2 * j] = max(count - 1, 0)
        bits[2 * j + 1] = min(count, 1)
    return exact_pass(exact_pass(bits, 0, 1), 1, 1)


def terminal_width2_counts(width4):
    """Counts after h=4 and h=2 passes, from incoming width-4 counts."""
    width2 = [0] * (2 * len(width4))
    for j, count in enumerate(width4):
        width2[2 * j] = max(count - 2, 0)
        width2[2 * j + 1] = min(count, 2)
    return exact_pass(width2, 1, 2)


def is_sorted_from_width2_counts(counts):
    """Exact final sortedness test after width-1 even/odd comparators."""
    left = [count == 2 for count in counts]
    right = [count >= 1 for count in counts]
    for j in range(len(counts)):
        if j == 0:
            bad = left[j] and not left[j + 1]
        elif j == len(counts) - 1:
            bad = right[j - 1] and counts[j] == 0
        else:
            output_left = right[j - 1] or left[j]
            output_right = right[j] and left[j + 1]
            bad = output_left and not output_right
        if bad:
            return False
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", type=int, default=70)
    args = parser.parse_args()

    n = 32
    h = n // 2
    dist = {
        (a, b): Fraction(count_process.comb(h, a) * count_process.comb(h, b), 2**n)
        for a in range(h + 1)
        for b in range(h + 1)
    }
    for scale in (16, 8):
        h = scale
        dist = count_process.apply_pass(dist, h, 0, args.rounds, 0)
        dist = count_process.apply_pass(dist, h, 1, args.rounds, 0)
        dist = count_process.split_blocks(dist, h)

    bad_mass = Fraction(0)
    for profile, mass in dist.items():
        width4 = exact_pass(exact_pass(profile, 0, 4), 1, 4)
        width2 = terminal_width2_counts(width4)
        output = tail_output(profile)
        output_sorted = all(output[i] <= output[i + 1] for i in range(n - 1))
        assert output_sorted == is_sorted_from_width2_counts(width2)
        if not output_sorted:
            bad_mass += mass
    print(f"n={n} rounds={args.rounds} width4_profiles={len(dist)}")
    print(f"P[final unsorted]={float(bad_mass):.12g}")
    print(f"E[failing inputs]={float(bad_mass * 2**n):.12g}")
    print(f"exact_probability_digits={len(str(bad_mass.numerator))}/{len(str(bad_mass.denominator))}")


if __name__ == "__main__":
    main()
