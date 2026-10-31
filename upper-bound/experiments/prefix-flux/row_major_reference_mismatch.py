#!/usr/bin/env python3
"""Exact audit of the row-major uniform-density / rank-prefix mismatch.

For n equal-height columns and H marked wires, compare the uniform rational
column profile (height H/n in every column) with the exact row-major rank
prefix of length H. The discrepancy at a flattened prefix boundary has one
triangular bump; its full discrete variation is at most n/2, hence so is its
l1 effect on every complete port partition.

This script checks the closed form with exact Fractions. It is an audit, not
the proof; the proof is recorded in D2-PORT-VARIANCE-TRANSFER.md.
"""

from fractions import Fraction as F


def clip_prefix(h, lo, hi):
    return min(max(h - lo, F(0)), hi - lo)


def uniform_row_major_prefix(ones, columns, boundary):
    """Uniform-height column mass in the first `boundary` row-major wires."""
    full_rows, partial = divmod(boundary, columns)
    height = F(ones, columns)
    return (columns * clip_prefix(height, F(0), F(full_rows))
            + partial * clip_prefix(height, F(full_rows, 1),
                                    F(full_rows + 1, 1)))


def mismatch(ones, columns, boundary):
    exact = min(ones, boundary)
    uniform = uniform_row_major_prefix(ones, columns, boundary)
    return F(exact) - uniform


def audit(max_columns=16, max_rows=12):
    checked = 0
    max_ratio = F(0)
    for columns in range(1, max_columns + 1):
        for rows in range(1, max_rows + 1):
            capacity = columns * rows
            for ones in range(capacity + 1):
                values = [mismatch(ones, columns, b)
                          for b in range(capacity + 1)]
                quotient, remainder = divmod(ones, columns)
                peak = F(remainder * (columns - remainder), columns)
                expected = [F(0)] * (capacity + 1)
                for s in range(columns + 1):
                    b = quotient * columns + s
                    if b <= capacity:
                        expected[b] = (min(F(remainder), F(s))
                                       - F(s * remainder, columns))
                assert values == expected, (columns, rows, ones, values, expected)
                variation = sum((abs(right - left)
                                 for left, right in zip(values, values[1:])), F(0))
                assert variation == 2 * peak, (columns, rows, ones, variation, peak)
                assert variation <= F(columns, 2), (
                    columns, rows, ones, variation, columns
                )
                if columns:
                    max_ratio = max(max_ratio, variation / columns)
                checked += 1
    return checked, max_ratio


if __name__ == "__main__":
    cases, ratio = audit()
    print(f"exact row-major boundary profiles checked={cases}")
    print(f"max total-variation / columns={ratio}")
