#!/usr/bin/env python3
"""Exact DP for the last two cyclic rounds of the 4096x64 D2 core.

The slope-35 round forces its residual output profile y to satisfy
    y[d] - y[d-35] <= 1.
This script maximizes every ordered output-column difference after applying
the slope-17 round, over all integer y in [0,64]^64 satisfying only that
necessary condition.  The DP is therefore a relaxation of the real core; a
maximum <= 19 is a valid uniform range certificate for the fixed core.
"""
import argparse

import numpy as np


def max_difference(n: int, previous_slope: int, final_slope: int,
                   delta: int) -> int:
    inv = pow(final_slope, -1, n)
    # Contribution of each residual input column to output[0]-output[delta]
    # as a function of its residual height s.
    heights = np.arange(n + 1)
    unary = np.empty((n, n + 1), dtype=np.int16)
    for c in range(n):
        at_zero = (inv * (-c)) % n
        at_delta = (inv * (delta - c)) % n
        unary[c] = (at_zero < heights).astype(np.int16) - (
            at_delta < heights).astype(np.int16)

    # The one-sided slope condition is a single directed 64-cycle.
    order = [(previous_slope * k) % n for k in range(n)]
    best = -10**9
    for first_height in range(n + 1):
        dp = np.full(n + 1, -10**9, dtype=np.int32)
        dp[first_height] = int(unary[order[0], first_height])
        for c in order[1:]:
            # next <= previous + 1; for each next value, maximize over all
            # previous values at least next-1.
            suffix_max = np.maximum.accumulate(dp[::-1])[::-1]
            lower = np.maximum(0, heights - 1)
            dp = unary[c].astype(np.int32) + suffix_max[lower]
        # Close the cycle: first_height <= last_height + 1.
        best = max(best, int(dp[max(0, first_height - 1):].max()))
    return best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--previous-slope", type=int, default=35)
    parser.add_argument("--final-slope", type=int, default=17)
    parser.add_argument("--table", action="store_true",
                        help="print the exact maximum for each separation")
    args = parser.parse_args()
    if np.gcd(args.columns, args.previous_slope) != 1:
        parser.error("previous slope must be coprime to columns")
    if np.gcd(args.columns, args.final_slope) != 1:
        parser.error("final slope must be coprime to columns")
    values = [(delta, max_difference(args.columns, args.previous_slope,
                                     args.final_slope, delta))
              for delta in range(1, args.columns)]
    print(f"max ordered output difference = {max(v for _, v in values)}")
    print(f"separations attaining max = {[d for d, v in values if v == max(x for _, x in values)]}")
    if args.table:
        print("per-separation bounds:")
        print(" ".join(f"{d}:{v}" for d, v in values))


if __name__ == "__main__":
    main()
