#!/usr/bin/env python3
"""Explore the integral equal-height relaxation of the Kahale depth method.

This constructs certificate-height histograms, not sorting networks. Each
round pairs equal heights, leaving one idle wire at every odd level. Checks
are exact integer arithmetic; they check counting constraints, not selection
correctness or the positions of wires. Run, for example:
    python scripts/kahale_height_barrier.py 64 128 256 512
"""

import argparse
import json
import math


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def equal_height_round(counts):
    result = [0] * (len(counts) + 1)
    for height, count in enumerate(counts):
        pairs, idle = divmod(count, 2)
        result[height] += pairs + idle
        result[height + 1] += pairs
    return result


def investigate(d):
    n = (1 << d) // ((d + 1) * fib(d + 1))
    counts = [n]
    # Keep all prefix histograms. Their wire total is always n.
    histograms = [counts]
    for _ in range(d):
        counts = equal_height_round(counts)
        histograms.append(counts)
    worst = (0, 1, 0)
    for t, counts in enumerate(histograms):
        if sum(counts) != n:
            raise ArithmeticError("wire total changed")
        cumulative = 0
        ideal_numerator = 0
        for s in range(d + 1):
            if s < len(counts):
                cumulative += counts[s]
            if s <= t:
                ideal_numerator += n * math.comb(t, s)
            error_numerator = (cumulative << t) - ideal_numerator
            if not 0 <= error_numerator <= ((s + 1) << t):
                raise ArithmeticError("rounding bound failed")
        s = d - t
        low_count = sum(counts[:s + 1])
        budget = 1 << (s + 1)
        if low_count > budget:
            raise ArithmeticError("prefix counting condition failed")
        if low_count * worst[1] > worst[0] * budget:
            worst = (low_count, budget, s)
    return {
        "depth": d,
        "arity_bits": n.bit_length(),
        "depth_over_log2_arity": d / math.log2(n) if n > 1 else None,
        "all_prefix_counts_pass": True,
        "rounding_bound_pass": True,
        "worst_count_over_budget": worst[0] / worst[1],
        "worst_suffix_length": worst[2],
        "scope": "height histograms; no sorting or positional claim",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depth", type=int, nargs="*", default=[64, 128, 256, 512])
    args = parser.parse_args()
    if any(d < 0 for d in args.depth):
        parser.error("depths must be nonnegative")
    for d in args.depth:
        print(json.dumps(investigate(d)))


if __name__ == "__main__":
    main()
