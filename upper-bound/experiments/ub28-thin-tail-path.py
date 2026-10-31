#!/usr/bin/env python3
"""Thin-tail feasibility screen for the UB-28 top-heavy random schedule.

This follows one central count-profile path by choosing a mode of each exact
hypergeometric transition, then computes the exact conditional failure mass
of the width-8 random stage and deterministic width-4/2/1 tail. It is a
research screen, not an asymptotic theorem: the stable mode-profile pattern
still needs a paper induction in log_n.
"""

from fractions import Fraction
import argparse
import importlib.util
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


edge = load("ub28_local_edge_transfer", "ub28-local-edge-transfer.py")


def overlap_mode(left_ones, right_ones, width):
    """A mode of Hypergeom(width, right_ones, left_ones)."""
    x = ((left_ones + 1) * (right_ones + 1)) // (width + 2)
    return min(min(left_ones, right_ones),
               max(max(0, left_ones + right_ones - width), x))


def central_mode_prefix(log_n, radius=24, high=260, low=20, anchor=150):
    """Track a feasible local mode path from two top halves to width 8."""
    n = 1 << log_n
    width = n // 2
    blocks = 2
    center = 1
    counts = {0: n // 4, 1: n // 4}
    transition_counts = []
    split_counts = []
    scale_profiles = []

    while width >= 8:
        distance = (log_n - 1) - (width.bit_length() - 1)
        rounds = (high if distance % 2 == 0 else low) if width >= 32 else anchor
        if width <= 256:
            scale_profiles.append((width, tuple(
                counts.get(i, 0) for i in range(center - 4, center + 4)
            )))
        if width == 8:
            input_profile = tuple(counts.get(i, 0)
                                  for i in range(center - 2, center + 2))

        for offset in (0, 1):
            pair_updates = 0
            for left in sorted(counts):
                if left % 2 != offset or left + 1 not in counts:
                    continue
                a, b = counts[left], counts[left + 1]
                total = a + b
                for _ in range(rounds):
                    a = overlap_mode(a, b, width)
                    b = total - a
                    pair_updates += 1
                counts[left], counts[left + 1] = a, b
            transition_counts.append((width, pair_updates))

        if width == 8:
            return input_profile, transition_counts, split_counts, scale_profiles

        blocks *= 2
        center *= 2
        child_counts = {}
        for child in range(max(0, center - radius), min(blocks, center + radius)):
            parent = child // 2
            if parent not in counts:
                continue
            total = counts[parent]
            # Symmetric hypergeometric split: floor/ceil(total/2) are modes.
            left = (total + 1) // 2
            left = min(width // 2, max(0, total - width // 2, left))
            right = total - left
            child_counts[child] = left if child % 2 == 0 else right
            split_counts.append(width)
        counts = child_counts
        width //= 2

    raise AssertionError("width-8 stage was not reached")


def exact_width8_tail_probability(profile, rounds=150):
    """P[central edge bad | four width-8 counts], exactly as a Fraction."""
    support, table = edge.exact_tail_event(32, 16)
    support, table = edge.reverse_split(support, table, 4)
    for offset in (1, 0):
        support, table = edge.reverse_pass(support, table, 4, 8,
                                            offset, rounds)
    values = dict(enumerate(profile))
    return table[tuple(values[i] for i in support)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=24)
    parser.add_argument("--high", type=int, default=260)
    parser.add_argument("--low", type=int, default=20)
    parser.add_argument("--anchor", type=int, default=150)
    parser.add_argument("--trace", action="store_true",
                        help="print the central eight-block mode profile by width")
    args = parser.parse_args()
    if args.log_n < 16:
        raise ValueError("the observed stable prefix starts at log_n >= 16")

    profile, matching, splits, trace = central_mode_prefix(
        args.log_n, high=args.high, low=args.low, anchor=args.anchor
    )
    tail = exact_width8_tail_probability(profile, args.anchor)
    log_tail = math.log(tail.numerator) - math.log(tail.denominator)

    # Each selected mode has probability at least the reciprocal of the
    # number of possible counts, at most width+1. The top two central binomial
    # counts each have mass at least 1/(n/2+1). This coarse bound is enough to
    # expose a subexponential-in-n path if the profile induction is proved.
    log_prefix_lb = -2 * math.log(n := (1 << args.log_n) // 2 + 1)
    for width, updates in matching:
        log_prefix_lb -= updates * math.log(width + 1)
    for width in splits:
        log_prefix_lb -= math.log(width + 1)

    print(f"log_n={args.log_n} mode_width8_profile={profile}")
    if args.trace:
        print(f"central_mode_profiles={trace}")
    print(f"specified_matching_updates={sum(c for _, c in matching)} "
          f"split_choices={len(splits)}")
    print(f"prefix_log_probability_lower_bound={log_prefix_lb:.12g}")
    print(f"conditional_width8_tail_probability={tail}")
    print(f"conditional_tail_log_probability={log_tail:.12g}")
    print(f"combined_log_probability_lower_bound="
          f"{log_prefix_lb + log_tail:.12g}")
    print("Caveat: the prefix-profile stability for every log_n is not proved.")


if __name__ == "__main__":
    main()
