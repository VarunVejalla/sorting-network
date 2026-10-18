#!/usr/bin/env python3
"""Exact rank-target drift caused by one rank-agnostic packet matching.

Start with C sorted packets, packet i containing m copies of key i, with m
even. A merge-deal on a matched pair (i,j) puts m/2 copies of each endpoint
key in each output packet. Across all C-1 key thresholds, this contributes
m*|i-j| L1 error against the original rank-sorted packet targets. The script
checks the identity on small matchings and reports exact normalized costs.
"""

from __future__ import annotations

import json
from fractions import Fraction


def simulated_error(packet_count: int, packet_size: int,
                    matching: tuple[tuple[int, int], ...]) -> int:
    """Aggregate threshold L1 error after one ideal merge-deal round."""
    if packet_count % 2 or packet_size % 2:
        raise ValueError("packet count and packet size must be even")
    if len(matching) * 2 != packet_count:
        raise ValueError("matching must be perfect")
    flat = [v for edge in matching for v in edge]
    if sorted(flat) != list(range(packet_count)):
        raise ValueError("matching must cover every packet exactly once")

    error = 0
    for cut in range(packet_count - 1):
        for i, j in matching:
            # Count keys above this cut in each output lane. The sorted
            # two-run merge has m copies of each endpoint; dealing alternately
            # gives each lane exactly half of each key.
            actual_i = (packet_size // 2) * (
                int(i > cut) + int(j > cut)
            )
            actual_j = actual_i
            target_i = packet_size * int(i > cut)
            target_j = packet_size * int(j > cut)
            error += abs(actual_i - target_i) + abs(actual_j - target_j)
    return error


def main() -> None:
    c = 64
    m = 4096
    adjacent = tuple((i, i + 1) for i in range(0, c, 2))
    antipodal = tuple((i, c - 1 - i) for i in range(c // 2))
    adjacent_sum = sum(j - i for i, j in adjacent)
    antipodal_sum = sum(j - i for i, j in antipodal)
    random_expected_sum = Fraction(c * (c + 1), 6)
    normalizer = c * (c - 1)

    # Exhaust every perfect matching for C<=8, verifying the identity against
    # the explicit packet/key threshold count formula.
    def matchings(items: tuple[int, ...]):
        if not items:
            yield ()
            return
        first = items[0]
        for pos in range(1, len(items)):
            second = items[pos]
            rest = items[1:pos] + items[pos + 1:]
            for tail in matchings(rest):
                yield ((first, second),) + tail

    checked = 0
    for size in (2, 4, 6, 8):
        for matching in matchings(tuple(range(size))):
            direct = simulated_error(size, 8, matching)
            formula = 8 * sum(abs(i - j) for i, j in matching)
            assert direct == formula
            checked += 1

    print(json.dumps({
        "status": "exact single-round rank-target drift identity; not a full scheduler result",
        "identity": "aggregate L1 error over all key cuts = m * sum_edges |i-j|",
        "normalized_error": "sum_edges |i-j| / (C*(C-1))",
        "packets": c,
        "packet_size": m,
        "adjacent_matching": {
            "distance_sum": adjacent_sum,
            "normalized_error": str(Fraction(adjacent_sum, normalizer)),
        },
        "antipodal_matching": {
            "distance_sum": antipodal_sum,
            "normalized_error": str(Fraction(antipodal_sum, normalizer)),
        },
        "uniform_random_perfect_matching_expectation": {
            "distance_sum": str(random_expected_sum),
            "normalized_error": str(random_expected_sum / normalizer),
            "asymptotic": "1/6",
        },
        "mean_edge_span_allowed_for_error_1_over_50": str(Fraction(2, 50) * (c - 1)),
        "exhaustive_small_matchings_checked": checked,
    }, indent=2))


if __name__ == "__main__":
    main()
