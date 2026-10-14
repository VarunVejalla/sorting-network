#!/usr/bin/env python3
"""Exact finite perturbation bound for an integer merge-and-deal cycle.

For a fixed matching cycle this bounds every final pairwise coordinate
difference over all initial profiles in [0,64]^c. It is a finite schedule
certificate, not an unbounded family theorem.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from matching_cycle_screen import cycle_matrix  # noqa: E402


def exact_bound(packet_count: int, rounds: int) -> dict[str, object]:
    cycle_seed = 25_000 + rounds * 1_000 + packet_count
    _, matchings = cycle_matrix(packet_count, rounds, cycle_seed)

    # suffix[t] is the integer numerator for the exact-averaging product
    # from rounds t,...,rounds-1; its denominator is 2 ** (rounds-t).
    suffix: list[np.ndarray | None] = [None] * (rounds + 1)
    suffix[rounds] = np.eye(packet_count, dtype=np.int64)
    for t in range(rounds - 1, -1, -1):
        following = suffix[t + 1]
        assert following is not None
        current = np.empty_like(following)
        for left, right in matchings[t]:
            current[left] = following[left] + following[right]
            current[right] = following[left] + following[right]
        suffix[t] = current

    # Put every term over denominator 2 ** rounds. Exact averaging's
    # initial-profile contribution is 32 * ||row_i-row_j||_1 because
    # profiles lie in [0,64] and each row difference sums to zero.
    numerator = np.zeros((packet_count, packet_count), dtype=np.int64)
    full = suffix[0]
    assert full is not None
    for i in range(packet_count):
        numerator[i, :] = 32 * np.abs(full[i] - full).sum(axis=1)

    # At each update the integer result is exact averaging plus opposite
    # errors on each pair, each of magnitude at most 1/2. For output rows i,j,
    # an edge (l,r) contributes at most |(Q_i,l-Q_i,r)-(Q_j,l-Q_j,r)|/2,
    # where Q is the exact suffix product. Scaling by 2**rounds gives 2**t.
    for t, matching in enumerate(matchings):
        following = suffix[t + 1]
        assert following is not None
        left = np.asarray([edge[0] for edge in matching])
        right = np.asarray([edge[1] for edge in matching])
        edge_differences = following[:, left] - following[:, right]
        for i in range(packet_count):
            numerator[i, :] += (2**t) * np.abs(edge_differences[i] - edge_differences).sum(axis=1)

    max_numerator = int(numerator.max())
    denominator = 2**rounds
    exact = Fraction(max_numerator, denominator)
    integer_range_bound = max_numerator // denominator
    spill_fraction_bound = Fraction(integer_range_bound, 256)
    pair = np.unravel_index(int(np.argmax(numerator)), numerator.shape)
    return {
        "packets": packet_count,
        "rounds": rounds,
        "cycle_seed": cycle_seed,
        "max_pairwise_difference_bound": str(exact),
        "max_pairwise_difference_decimal": float(exact),
        "integer_final_range_bound": integer_range_bound,
        "normalized_positive_spill_bound": str(spill_fraction_bound),
        "normalized_positive_spill_bound_decimal": float(spill_fraction_bound),
        "maximizing_output_pair": [int(pair[0]), int(pair[1])],
        "certificate_arithmetic": "exact integer numerator over 2**rounds",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--rounds", type=int, default=26)
    parser.add_argument("--save", help="optional JSON output path")
    args = parser.parse_args()
    result = {
        "status": "exact finite schedule perturbation bound; not an unbounded theorem",
        "results": [exact_bound(c, args.rounds) for c in args.packets],
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.save:
        Path(args.save).write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
