#!/usr/bin/env python3
"""Audit the ordered-profile one-round area-moment inequality."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import sqrt


def recurrence(area: float, columns: int) -> float:
    return sqrt((columns * columns - 1) * (2 * area + columns / 4)
                / (12 * columns))


def audit_small_profiles(max_rows: int = 6, max_columns: int = 6) -> int:
    checked = 0
    for rows in range(1, max_rows + 1):
        for columns in range(1, max_columns + 1):
            for heights in combinations_with_replacement(
                    range(rows + 1), columns):
                total = sum(heights)
                rho = F((total % columns) * (columns - total % columns),
                        columns)
                mean = F(total, columns)
                centered_square = sum((F(h) - mean) ** 2 for h in heights)
                area = (centered_square - rho) / 2
                pair_spread = sum(
                    heights[j] - heights[i]
                    for i in range(columns)
                    for j in range(i + 1, columns)
                )
                ordered_dot = sum(
                    (2 * (i + 1) - columns - 1) * h
                    for i, h in enumerate(heights)
                )
                assert pair_spread == ordered_dot

                # E[A_next | heights] = W/(2n) - rho_next/2 <= W/(2n).
                mean_area_upper = F(pair_spread, 2 * columns)
                rhs_squared = (F(columns * columns - 1, 12 * columns)
                               * (2 * area + F(columns, 4)))
                assert mean_area_upper >= 0
                assert mean_area_upper * mean_area_upper <= rhs_squared, (
                    rows, columns, heights, mean_area_upper, rhs_squared)
                checked += 1
    return checked


def report_three_round_comparison(rows: int = 4096,
                                  columns: int = 64) -> None:
    initial = columns * rows * rows / 8
    old = initial
    new = initial
    print(f"dimensions={rows}x{columns}; area normalized by rows*columns")
    for round_index in range(1, 4):
        old = sqrt((columns - 1) * (2 * old + columns / 4) / 8)
        new = recurrence(new, columns)
        scale = rows * columns
        print(f"round={round_index}: old={old / scale:.12f}, "
              f"ordered={new / scale:.12f}")


if __name__ == "__main__":
    print(f"exact small-profile checks={audit_small_profiles()}")
    report_three_round_comparison()
