#!/usr/bin/env python3
"""Adversarial screen for fixed row-cyclic two-scramble cores.

This is a heuristic profile search. The exact residue reduction used to
compare row heights that are multiples of the column count is documented in
``D2-PORT-VARIANCE-TRANSFER.md``; the search does not prove a uniform bound.
"""
import argparse
from contextlib import redirect_stdout
from io import StringIO
from math import gcd

import numpy as np

from d2_variance_fixed_core_attack import optimize


def cyclic(rows, cols, multiplier, offset=0):
    destination = np.arange(cols, dtype=np.int32)
    shifts = (multiplier * np.arange(rows, dtype=np.int32) + offset) % cols
    # Destination-to-source representation expected by apply_round.
    return (destination[None, :] - shifts[:, None]) % cols


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rows", type=int, default=8192)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--first-slope", type=int, default=1)
    ap.add_argument("--second-slope", type=int, default=35)
    ap.add_argument("--second-offset", type=int, default=17)
    ap.add_argument("--search-seed", type=int, default=20261026)
    ap.add_argument("--restarts", type=int, default=64)
    ap.add_argument("--steps", type=int, default=20000)
    ap.add_argument("--show-witness", action="store_true")
    ap.add_argument("--sweep-odd-second-slopes", action="store_true")
    args = ap.parse_args()
    if args.rows % args.columns:
        ap.error("rows must be a multiple of columns for the residue reduction")
    if gcd(args.first_slope, args.columns) != 1 or gcd(args.second_slope, args.columns) != 1:
        ap.error("both slopes must be coprime to the column count")

    first = cyclic(args.rows, args.columns, args.first_slope)
    slopes = (range(1, args.columns, 2) if args.sweep_odd_second_slopes
              else [args.second_slope])
    results = []
    for second_slope in slopes:
        if gcd(second_slope, args.columns) != 1:
            continue
        second = cyclic(args.rows, args.columns, second_slope,
                        args.second_offset)
        search_seed = (args.search_seed ^ (second_slope * 100)
                       if args.sweep_odd_second_slopes
                       else args.search_seed)
        rng = np.random.default_rng(search_seed)
        with redirect_stdout(StringIO()):
            value, heights, output = optimize(
                first, second, args.rows, args.columns, rng,
                args.restarts, args.steps)
        result = {"rows": args.rows, "columns": args.columns,
                  "slopes": (args.first_slope, second_slope),
                  "second_offset": args.second_offset,
                  "search_seed": search_seed,
                  "restarts": args.restarts, "steps": args.steps,
                  "Aw": value, "Aw_per_column": value / args.columns,
                  "output_range": int(output.max() - output.min())}
        if args.show_witness and not args.sweep_odd_second_slopes:
            result["input_heights"] = heights.tolist()
            result["output_heights"] = output.tolist()
        results.append(result)
        print(result, flush=True)
    if args.sweep_odd_second_slopes:
        print({"best": min(results, key=lambda r: r["Aw_per_column"]),
               "worst": max(results, key=lambda r: r["Aw_per_column"])},
              flush=True)


if __name__ == "__main__":
    main()
