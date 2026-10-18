#!/usr/bin/env python3
"""Exact tail screen for uniform-random packet compare-split matchings.

A compare-split on sorted packets at IDs i<j sends a threshold singleton to
the higher ID. Under a uniform random perfect matching, its partner is uniform
among the other C-1 IDs, so it reaches the final ID in any one round with
probability at most 1/(C-1). This script checks the logarithmic-round union
bound exactly; it is not a screen of the actual WireFlow scheduler.
"""

from fractions import Fraction


def main() -> None:
    for depth in (8, 16, 32, 64, 128):
        packets = 64**depth
        rounds = 8 * depth
        hit_bound = Fraction(rounds, packets - 1)
        print({
            "hierarchy_depth": depth,
            "packet_count": packets,
            "random_compare_split_rounds": rounds,
            "singleton_reaches_last_packet_probability_upper_bound": str(hit_bound),
        })


if __name__ == "__main__":
    main()
