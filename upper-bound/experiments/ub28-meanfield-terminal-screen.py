#!/usr/bin/env python3
"""Check whether the zero-rate mean-field path reaches a bad anchor profile.

This diagnostic follows the typical density update for a comparator matching:
    (a,b) -> (a*b, a+b-a*b),
and duplicates each density at a physical split. It is not a bound on
non-typical trajectories or a sorting proof.
"""

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_local_edge_maxpath", HERE / "ub28-local-edge-maxpath.py"
)
maxpath = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(maxpath)


def meanfield_to_anchor(log_n, high, low):
    n = 1 << log_n
    density = np.array([0.5, 0.5], dtype=np.float64)
    width = n // 2
    while width > 16:
        blocks = len(density)
        top_distance = log_n - 1 - (width.bit_length() - 1)
        rounds = high if top_distance % 2 == 0 else low
        for offset in (0, 1):
            left = np.arange(offset, blocks - 1, 2)
            right = left + 1
            for _ in range(rounds):
                a = density[left].copy()
                b = density[right].copy()
                density[left] = a * b
                density[right] = a + b - a * b
        density = np.repeat(density, 2)
        width //= 2
    return density


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=20)
    parser.add_argument("--high", type=int, default=235)
    parser.add_argument("--low", type=int, default=35)
    parser.add_argument("--anchor-rounds", type=int, default=150)
    args = parser.parse_args()
    if not 8 <= args.log_n <= 20:
        raise ValueError("diagnostic requires 8 <= log-n <= 20")

    n = 1 << args.log_n
    edge = n // 2 - 64
    density = meanfield_to_anchor(args.log_n, args.high, args.low)
    support, anchor, _ = maxpath.edge_state_at_width(
        256, 64, args.anchor_rounds, 16
    )
    target_block_offset = n // 32 - 256 // 32
    target_support = tuple(i + target_block_offset for i in support)
    local_density = density[list(target_support)]
    nearest_counts = tuple(int(round(16 * x)) for x in local_density)
    viable = math.isfinite(anchor[nearest_counts])
    print(f"n=2^{args.log_n} edge={edge} rounds={args.high}/{args.low}")
    print(f"width16_support={target_support}")
    print("meanfield_densities=" + ",".join(f"{x:.10g}" for x in local_density))
    print(f"nearest_integer_counts={nearest_counts} anchor_viable={viable}")


if __name__ == "__main__":
    main()
