#!/usr/bin/env python3
"""Exhaustively verify the two-round expected full-row-area identity."""
from fractions import Fraction
from itertools import permutations, product


def column_sort(rows):
    m, n = len(rows), len(rows[0])
    cols = [sorted((rows[r][c] for r in range(m)), reverse=True)
            for c in range(n)]
    return [[cols[c][r] for c in range(n)] for r in range(m)]


def scramble(rows, ps):
    return [[rows[r][ps[r][c]] for c in range(len(rows[0]))]
            for r in range(len(rows))]


def aggregate(rows):
    m, n = len(rows), len(rows[0])
    total = sum(map(sum, rows))
    seen = area = 0
    for k, row in enumerate(rows, start=1):
        seen += sum(row)
        area += min(total, k * n) - seen
    return area


def conditional_mean_from_heights(heights, rows, columns):
    total = sum(heights)
    row_counts = [sum(height > r for height in heights) for r in range(rows)]
    rem = total % columns
    return Fraction(1, 2) * (
        sum(Fraction(x * (columns - x), columns) for x in row_counts)
        - Fraction(rem * (columns - rem), columns)
    )


def lazy_walk_abs_mean(steps, alpha):
    distribution = {0: Fraction(1)}
    for _ in range(steps):
        nxt = {}
        for value, probability in distribution.items():
            nxt[value] = nxt.get(value, Fraction()) + probability * (1-alpha)
            nxt[value-1] = nxt.get(value-1, Fraction()) + probability * alpha/2
            nxt[value+1] = nxt.get(value+1, Fraction()) + probability * alpha/2
        distribution = nxt
    return sum(abs(value) * probability
               for value, probability in distribution.items())


def check(rows, columns):
    row_perms = list(product(permutations(range(columns)), repeat=rows))
    checked = 0
    for xs0 in product(range(columns + 1), repeat=rows):
        if any(xs0[r] < xs0[r + 1] for r in range(rows - 1)):
            continue
        initial = [[int(c < xs0[r]) for c in range(columns)]
                   for r in range(rows)]
        first_outputs = [column_sort(scramble(initial, ps))
                         for ps in row_perms]
        predicted = sum((conditional_mean_from_heights(
            [sum(out[r][c] for r in range(rows)) for c in range(columns)],
            rows, columns) for out in first_outputs), Fraction()) / len(row_perms)

        actual = sum(aggregate(column_sort(scramble(out, ps)))
                     for out in first_outputs for ps in row_perms)
        actual = Fraction(actual, len(row_perms) ** 2)
        assert actual == predicted, (rows, columns, xs0, actual, predicted)
        assert 32 * predicted * predicted <= rows * columns * (columns - 1)
        beta = Fraction(2 * (columns // 2) * (columns - columns // 2),
                        columns * (columns - 1))
        exact_bound = Fraction(columns - 1, 4) * lazy_walk_abs_mean(rows, beta)
        assert predicted <= exact_bound, (rows, columns, xs0, predicted,
                                          exact_bound)
        checked += 1
    print(f"m={rows}, n={columns}: {checked} profiles; exact two-round means and bound passed")


if __name__ == "__main__":
    check(2, 3)
    check(3, 3)
