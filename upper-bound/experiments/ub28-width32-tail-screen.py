#!/usr/bin/env python3
"""Screen a UB-28 variant with exact sorting inside fixed 32-wire blocks.

After exact sorting each width-32 block, a remaining inversion can occur only
at a block boundary, and its predicate is (left_count > 0 and right_count <
32). The random matching schedule therefore starts at width 64. This finite
grid transfer is exploratory: it samples feasible count paths and does not
upper-bound off-grid paths or prove a uniform rate.
"""

import argparse
import importlib.util
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rate = load("ub28_rate_grid", "ub28-rate-grid.py")
phase = load("ub28_phase_closure", "ub28-phase-closure.py")


def width32_terminal_rate(log_n, grid, edge, high, low, fine_bottom=False):
    n = 1 << log_n
    blocks = n // 32
    width = 32
    base_grid = grid
    if fine_bottom:
        grid = 32
    support = (edge, edge + 1)
    table = rate.np.full((grid + 1, grid + 1), rate.NEG_INF)
    for left in range(grid + 1):
        left_ones = left * width // grid
        for right in range(grid + 1):
            right_ones = right * width // grid
            if left_ones > 0 and right_ones < width:
                table[left, right] = 0.0

    while blocks > 2:
        support, table = rate.reverse_split(support, table, grid, width)
        blocks //= 2
        width *= 2
        distance_from_top = blocks.bit_length() - 2
        stage_rounds = high if distance_from_top % 2 == 0 else low
        kernels = rate.rate_kernels(grid, stage_rounds, width)
        for offset in (1, 0):
            support, table = rate.reverse_pass(
                support, table, blocks, grid, width, offset, kernels
            )
        if fine_bottom and width == 64:
            # Keep every width-32 count through the first matching stage,
            # then restrict to the width-16 lattice before the support grows.
            stride = grid // base_grid
            table = table[tuple(slice(0, grid + 1, stride)
                                for _ in range(table.ndim))]
            grid = base_grid

    if support != (0, 1):
        raise AssertionError(f"unexpected root support {support}")
    best_log_rate = rate.NEG_INF
    for left in range(grid + 1):
        for right in range(grid + 1):
            left_ones = left * width // grid
            right_ones = right * width // grid
            candidate = (
                0.5 * table[left, right]
                + (rate.log_choose(width, left_ones)
                   + rate.log_choose(width, right_ones)
                   - 2 * width * math.log(2.0)) / (2 * width)
            )
            best_log_rate = max(best_log_rate, candidate)
    return -best_log_rate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-n", type=int, default=24)
    parser.add_argument("--grid", type=int, default=16,
                        choices=(1, 2, 4, 8, 16))
    parser.add_argument("--high", type=int, default=280)
    parser.add_argument("--low", type=int, default=20)
    parser.add_argument("--fine-bottom-grid32", action="store_true",
                        help="keep all 33 width-32 counts through width 64, then restrict to grid-16")
    parser.add_argument("--native-dll")
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--edge", type=int, action="append",
                        help="screen only these exact width-32 block boundaries")
    args = parser.parse_args()
    if args.log_n < 7 or 32 % args.grid:
        raise ValueError("requires log-n >= 7 and a grid dividing 32")
    if args.native_dll:
        rate.enable_native_kernel(args.native_dll)

    blocks = (1 << args.log_n) // 32
    edges = sorted(phase.representative_positions(blocks, 2))
    if args.edge:
        edges = args.edge
    if args.limit:
        edges = edges[:args.limit]
    print(f"terminal_width=32 grid={args.grid} representatives={len(edges)}",
          flush=True)
    results = []
    for edge in edges:
        value = width32_terminal_rate(args.log_n, args.grid, edge,
                                      args.high, args.low,
                                      args.fine_bottom_grid32)
        results.append((value, edge))
        print(f"edge={edge:7d} rate={value:.12g}", flush=True)
    worst = min(results)
    print(f"min_sampled_rate={worst[0]:.12g} ln2={math.log(2):.12g} "
          f"edge={worst[1]}")


if __name__ == "__main__":
    main()
