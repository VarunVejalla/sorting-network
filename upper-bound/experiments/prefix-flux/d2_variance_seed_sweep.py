#!/usr/bin/env python3
"""Heuristic multi-core sweep for the fixed two-scramble variance gate.

For each core seed, search binary initial column heights with the same
incremental adversary used by ``d2_variance_fixed_core_attack.py``. This is
discovery evidence only: failure to find a violating profile is not a proof
of the uniform provider bound.
"""
import argparse
from contextlib import redirect_stdout
from io import StringIO

import numpy as np

from d2_variance_fixed_core_attack import inverse_row_permutations, optimize


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rows", type=int, default=8192)
    ap.add_argument("--cols", type=int, default=64)
    ap.add_argument("--first-seed", type=int, default=20261030)
    ap.add_argument("--cores", type=int, default=8)
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=10000)
    ap.add_argument("--cap-per-column", type=float, default=48.0)
    ap.add_argument("--show-witness", action="store_true")
    args = ap.parse_args()

    results = []
    for seed in range(args.first_seed, args.first_seed + args.cores):
        core_rng = np.random.default_rng(seed)
        first = inverse_row_permutations(core_rng, args.rows, args.cols)
        second = inverse_row_permutations(core_rng, args.rows, args.cols)
        search_rng = np.random.default_rng(seed ^ 0x5A17)
        # The shared optimizer reports every restart. Keep this sweep quiet
        # unless the caller explicitly asks for the witness arrays.
        with redirect_stdout(StringIO()):
            value, heights, output = optimize(
                first, second, args.rows, args.cols, search_rng,
                args.restarts, args.steps)
        result = {
            "core_seed": seed,
            "Aw": value,
            "Aw_per_column": value / args.cols,
            "cap_per_column": args.cap_per_column,
            "below_cap": value <= args.cap_per_column * args.cols,
        }
        if args.show_witness:
            result["input_heights"] = heights.tolist()
            result["output_heights"] = output.tolist()
        results.append(result)
        print(result, flush=True)

    worst = max(results, key=lambda item: item["Aw_per_column"])
    print({"cores": len(results), "worst_core_seed": worst["core_seed"],
           "worst_Aw_per_column": worst["Aw_per_column"],
           "cap_per_column": args.cap_per_column,
           "all_below_cap": all(item["below_cap"] for item in results)},
          flush=True)


if __name__ == "__main__":
    main()
