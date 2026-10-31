#!/usr/bin/env python3
"""Exhaustively screen aggregate defects for fixed small two-scramble cores.

After the first column sort, every Boolean input is represented by its column
heights. For each fixed pair of row scrambles, enumerate all height vectors,
run the remaining two column sorts exactly, and maximize the sum of full-row
prefix defects. This is finite evidence only; it does not prove a uniform
large-rectangle bound or account for D2 stage transfer.
"""
import argparse
from itertools import product
import random

from rank_recurrence import prefix_interval


def column_sort(rows):
    m, n = len(rows), len(rows[0])
    columns = [sorted((rows[r][c] for r in range(m)), reverse=True)
               for c in range(n)]
    return [[columns[c][r] for c in range(n)] for r in range(m)]


def row_scramble(rows, permutations):
    return [[rows[r][permutations[r][c]] for c in range(len(rows[0]))]
            for r in range(len(rows))]


def run(rows, columns, seed):
    rng = random.Random(seed)
    scrambles = [[rng.sample(range(columns), columns) for _ in range(rows)]
                 for _ in range(2)]
    best = [(0, 0, None) for _ in range(rows * columns + 1)]

    for heights in product(range(rows + 1), repeat=columns):
        total = sum(heights)
        state = [[int(r < heights[c]) for c in range(columns)]
                 for r in range(rows)]
        state = column_sort(state)
        state = column_sort(row_scramble(state, scrambles[0]))
        state = column_sort(row_scramble(state, scrambles[1]))

        zeros = 0
        aggregate = peak = 0
        for j, row in enumerate(state, start=1):
            zeros += sum(row)
            defect = min(total, j * columns) - zeros
            assert defect >= 0
            aggregate += defect
            peak = max(peak, defect)
        old = best[total]
        if aggregate > old[0]:
            best[total] = (aggregate, peak, heights)

    results = []
    for total, (actual, peak, witness) in enumerate(best):
        caps = []
        for j in range(rows + 1):
            lower, _ = prefix_interval(
                rows * columns, (total, total), j * columns,
                row_count=rows,
            )
            caps.append(min(total, j * columns) - lower)
        cap_sum = sum(caps)
        assert actual <= cap_sum, (rows, columns, seed, total, actual, cap_sum)
        results.append((total, actual, peak, cap_sum, witness))

    worst_ratio = max((actual / cap if cap else 0, total)
                      for total, actual, _, cap, _ in results)
    worst_actual = max((actual, total) for total, actual, *_ in results)
    return worst_actual, worst_ratio, results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, nargs="+", default=[8, 16])
    parser.add_argument("--columns", type=int, default=4)
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    args = parser.parse_args()

    for m in args.rows:
        for seed in args.seeds:
            actual, ratio, results = run(m, args.columns, seed)
            total = actual[1]
            _, aggregate, peak, cap, witness = results[total]
            print({"rows": m, "columns": args.columns, "seed": seed,
                   "profiles": (m + 1) ** args.columns,
                   "max_aggregate": aggregate, "at_total": total,
                   "max_single_defect": peak, "pointwise_cap_sum": cap,
                   "aggregate_to_cap_ratio": round(ratio[0], 4),
                   "witness_column_heights": witness})
