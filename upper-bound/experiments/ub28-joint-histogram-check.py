#!/usr/bin/env python3
"""Small exact strong-lumpability checks for the UB-28 joint histogram idea.

Checks that a fresh uniform matching's output row-histogram law depends only
on the input row histogram, then verifies the joint two-half allocation law.
This is diagnostic finite checking; the symmetry argument and arbitrary-width
proof are separate obligations.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
from math import comb


def histogram(rows):
    return tuple(sorted(Counter(rows).items()))


def after_matching(rows, h, left_block, right_block, matching):
    out = [[(row >> block) & 1 for block in range(3)] for row in rows]
    for left_slot, right_slot in enumerate(matching):
        a = out[left_slot][left_block]
        b = out[right_slot][right_block]
        out[left_slot][left_block] = min(a, b)
        out[right_slot][right_block] = max(a, b)
    return tuple(sum(bit << block for block, bit in enumerate(row))
                 for row in out)


def matching_law(rows, matchings, left_block=0, right_block=1):
    law = Counter()
    for matching in matchings:
        out = after_matching(rows, len(rows), left_block, right_block, matching)
        law[histogram(out)] += 1
    total = len(matchings)
    return {state: Fraction(mass, total) for state, mass in law.items()}


def split_signature(rows):
    half = len(rows) // 2
    return histogram(rows[:half]), histogram(rows[half:])


def expected_split_law(state, h):
    types = [row_type for row_type, _ in state]
    counts = [count for _, count in state]
    half = h // 2
    denominator = comb(h, half)
    law = defaultdict(Fraction)

    def allocate(i, used, left_counts, mass):
        if i == len(types):
            if used == half:
                left = tuple((types[j], left_counts[j])
                             for j in range(len(types)) if left_counts[j])
                right = tuple((types[j], counts[j] - left_counts[j])
                              for j in range(len(types))
                              if counts[j] - left_counts[j])
                law[left, right] += mass / denominator
            return
        for x in range(max(0, half - used - sum(counts[i + 1:])),
                       min(counts[i], half - used) + 1):
            allocate(i + 1, used + x, left_counts + [x],
                     mass * comb(counts[i], x))

    allocate(0, 0, [], Fraction(1))
    return dict(law)


def check_width(h):
    k = 3
    matchings = tuple(permutations(range(h)))
    by_hist = defaultdict(list)
    for rows in product(range(1 << k), repeat=h):
        by_hist[histogram(rows)].append(rows)

    checked = 0
    for state, representatives in by_hist.items():
        for pair in ((0, 1), (1, 2)):
            expected = matching_law(representatives[0], matchings, *pair)
            for rows in representatives[1:]:
                if matching_law(rows, matchings, *pair) != expected:
                    raise AssertionError((h, state, rows, pair,
                                          "matching not lumpable"))

        # A common random slot permutation gives the exact conditional split
        # kernel for the exchangeable orbit represented by this histogram.
        expected_split = expected_split_law(state, h)
        for rows in representatives:
            observed = Counter(split_signature(tuple(rows[i] for i in p))
                                for p in matchings)
            observed = {key: Fraction(mass, len(matchings))
                        for key, mass in observed.items()}
            if observed != expected_split:
                raise AssertionError((h, state, rows, "joint split law mismatch"))
        checked += len(representatives)

    print(f"width={h} k={k} input_patterns={checked} histograms={len(by_hist)} "
          f"matchings={len(matchings)} phases=2 strong_lumpability=ok")


def main():
    for h in (2, 4):
        check_width(h)


if __name__ == "__main__":
    main()
