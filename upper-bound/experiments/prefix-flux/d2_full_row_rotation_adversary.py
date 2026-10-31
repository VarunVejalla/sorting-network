#!/usr/bin/env python3
"""Exact monotone-profile adversary for a full-row cyclic repair.

The DP maximizes ``columns * load[c] - total_mass`` over every nonincreasing
row-width profile. It reconstructs one exact profile and evaluates the actual
balanced-column area after the top-forward/bottom-reflected cyclic maps.
This tests a proposed all-row final repair, not the edge-only repair.
"""
import argparse
from fractions import Fraction as F

import numpy as np


def solve(rows=4096, columns=64, edge_rows=2048, row_step=41,
          target=F(17, 2000), witness_column=0):
    if 2 * edge_rows != rows:
        raise ValueError("this gate expects top and bottom bands to cover all rows")
    neg = -(1 << 60)
    dp = np.full(columns + 1, neg, dtype=np.int64)
    dp[columns] = 0  # the first width may be anything in [0, columns]
    parents = np.empty((rows, columns + 1), dtype=np.int8)
    widths = np.arange(columns + 1)

    for row in range(rows):
        start = row_step * row % columns
        if row < edge_rows:
            threshold = (witness_column - start) % columns + 1
        else:
            threshold = (start + columns - 1 - witness_column) % columns + 1
        reward = columns * (widths >= threshold) - widths
        suffix = np.maximum.accumulate(dp[::-1])[::-1]

        # For current width w, choose the best previous width p >= w.
        parent = np.empty(columns + 1, dtype=np.int8)
        best, best_width = neg, -1
        for previous in range(columns, -1, -1):
            if dp[previous] > best:
                best, best_width = int(dp[previous]), previous
            parent[previous] = best_width
        parents[row] = parent
        dp = suffix + reward

    final_width = int(np.argmax(dp))
    scaled_deviation = int(dp[final_width])
    profile = [0] * rows
    width = final_width
    for row in range(rows - 1, -1, -1):
        profile[row] = width
        width = int(parents[row, width])
    assert all(profile[i] >= profile[i + 1] for i in range(rows - 1))

    loads = [0] * columns
    for row, width in enumerate(profile):
        start = row_step * row % columns
        for source in range(width):
            dest = ((start + source) % columns if row < edge_rows else
                    (start + columns - 1 - source) % columns)
            loads[dest] += 1

    total = sum(profile)
    q, rem = divmod(total, columns)
    balanced_squares = ((columns - rem) * q * q +
                        rem * (q + 1) * (q + 1))
    area = (sum(value * value for value in loads) - balanced_squares) // 2
    budget = target * rows * columns
    runs = []
    for value in sorted(set(profile), reverse=True):
        runs.append((value, profile.count(value)))
    out = {
        "rows": rows, "columns": columns, "edge_rows_per_side": edge_rows,
        "row_step": row_step, "witness_column": witness_column,
        "scaled_column_deviation": scaled_deviation,
        "profile_mass": total, "profile_runs": runs,
        "output_height_min": min(loads), "output_height_max": max(loads),
        "area": area, "area_fraction": F(area, rows * columns),
        "target_fraction": target, "target_area": budget,
        "exceeds_target": area > budget,
    }
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rows", type=int, default=4096)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--edge-rows", type=int, default=2048)
    ap.add_argument("--row-step", type=int, default=41)
    ap.add_argument("--target", default="17/2000")
    ap.add_argument("--witness-column", type=int, default=0)
    args = ap.parse_args()
    print(solve(args.rows, args.columns, args.edge_rows, args.row_step,
                F(args.target), args.witness_column), flush=True)
