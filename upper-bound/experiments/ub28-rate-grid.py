#!/usr/bin/env python3
"""Coarse count-lattice screen for the annealed UB-28 process.

This extends the exact finite max-path transfer from width 16 through larger
scales, restricting every later block count to multiples of width/16. Those
are count values and are feasible transitions of the exact annealed
block-count process (see ub28-count-process.py). The lattice omits other
count trajectories, so it cannot upper-bound the full maximum rate. Log
binomial coefficients use binary64, so this is not a certified interval
result either.
"""

import argparse
import math
from functools import lru_cache

import numpy as np

from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = spec_from_file_location("ub28_maxpath", HERE / "ub28-local-edge-maxpath.py")
maxpath = module_from_spec(spec)
spec.loader.exec_module(maxpath)

NEG_INF = -math.inf


@lru_cache(maxsize=None)
def log_choose(n, k):
    if k < 0 or k > n:
        return NEG_INF
    return (math.lgamma(n + 1) - math.lgamma(k + 1)
            - math.lgamma(n - k + 1))


def maxplus_product(a, b):
    result = np.full((a.shape[0], b.shape[1]), NEG_INF)
    for k in range(a.shape[1]):
        np.maximum(result, a[:, k, None] + b[k, None, :], out=result)
    return result


@lru_cache(maxsize=None)
def rate_kernels(grid, rounds, width):
    m = grid
    kernels = {}
    for total in range(2 * m + 1):
        counts = tuple(range(max(0, total - m), min(m, total) + 1))
        one = np.full((len(counts), len(counts)), NEG_INF)
        for i, left in enumerate(counts):
            a = left * width // m
            pair_total = total * width // m
            b = pair_total - a
            for j, out_left in enumerate(counts):
                x = out_left * width // m
                one[i, j] = (
                    log_choose(b, x)
                    + log_choose(width - b, a - x)
                    - log_choose(width, a)
                ) / width
        power = np.full_like(one, NEG_INF)
        np.fill_diagonal(power, 0.0)
        base = one
        exponent = rounds
        while exponent:
            if exponent & 1:
                power = maxplus_product(power, base)
            exponent >>= 1
            if exponent:
                base = maxplus_product(base, base)
        kernels[total] = (counts, power)
    return kernels


def split_cost(parent_count, left_count, grid, child_width):
    parent_width = 2 * child_width
    parent_ones = parent_count * parent_width // grid
    left_ones = left_count * child_width // grid
    right_ones = parent_ones - left_ones
    return (
        log_choose(child_width, left_ones)
        + log_choose(child_width, right_ones)
        - log_choose(parent_width, parent_ones)
    ) / child_width


def reverse_split(support, table, grid, child_width):
    for parent in sorted({i // 2 for i in support}):
        children = [i for i in (2 * parent, 2 * parent + 1) if i in support]
        axes = [support.index(i) for i in children]
        rest_axes = [i for i in range(table.ndim) if i not in axes]
        moved = np.moveaxis(table, axes + rest_axes,
                            list(range(len(axes) + len(rest_axes))))
        rest_shape = moved.shape[len(axes):]
        flat = moved.reshape((grid + 1,) * len(axes) + (-1,))
        out = np.full((grid + 1, flat.shape[-1]), NEG_INF)
        for count in range(grid + 1):
            for left in range(grid + 1):
                cost = split_cost(count, left, grid, child_width)
                if cost == NEG_INF:
                    continue
                if len(axes) == 2:
                    candidate = cost + flat[left, 2 * count - left]
                else:
                    selected = left if children[0] % 2 == 0 else 2 * count - left
                    candidate = cost + flat[selected]
                np.maximum(out[count], candidate, out=out[count])
        out = out.reshape((grid + 1,) + rest_shape)
        insert = sum(i // 2 < parent for i in support if i // 2 != parent)
        table = np.moveaxis(out, 0, insert)
        support = tuple(sorted((set(support) - set(children)) | {parent}))
    return support, table / 2.0


def reverse_pass(support, table, blocks, grid, width, offset, kernels):
    for left in range(offset, blocks - 1, 2):
        right = left + 1
        if left not in support and right not in support:
            continue
        expanded = tuple(sorted(set(support) | {left, right}))
        if expanded != support:
            table = np.broadcast_to(
                table.reshape(tuple(grid + 1 if i in support else 1 for i in expanded)),
                (grid + 1,) * len(expanded),
            ).copy()
            support = expanded
        a, b = support.index(left), support.index(right)
        rest = [i for i in range(table.ndim) if i not in (a, b)]
        moved = np.moveaxis(table, (a, b, *rest), tuple(range(table.ndim)))
        flat = moved.reshape(grid + 1, grid + 1, -1)
        out = np.full_like(flat, NEG_INF)
        for total, (counts, kernel) in kernels.items():
            source = np.stack([flat[x, total - x] for x in counts], axis=0)
            for start in range(0, len(counts), 4):
                stop = min(start + 4, len(counts))
                candidates = kernel[start:stop, :, None] + source[None, :, :]
                best = np.max(candidates, axis=1)
                for offset, i in enumerate(range(start, stop)):
                    x = counts[i]
                    out[x, total - x] = best[offset]
        out = out.reshape(moved.shape)
        table = np.moveaxis(out, tuple(range(table.ndim)), (a, b, *rest))
    return support, table


def asymptotic_rate(exponent, rounds, grid, anchor_edge, alternating=False,
                    high_parity=0, top_alternating=False,
                    top_high=151, top_low=149, placement="center",
                    anchor_rounds=150):
    anchor_n = 256
    support, finite_table, blocks = maxpath.edge_state_at_width(
        anchor_n, anchor_edge, anchor_rounds, 16
    )
    if 16 % grid:
        raise ValueError("grid must divide 16 so the anchor counts embed exactly")
    stride = 16 // grid
    finite_table = finite_table[tuple(slice(0, 17, stride)
                                      for _ in range(len(support)))]
    table = finite_table / 16.0
    n = 1 << exponent
    anchor_blocks, target_blocks = anchor_n // 16, n // 16
    if placement == "left":
        delta = 0
    elif placement == "right":
        delta = target_blocks - anchor_blocks
    elif placement == "center":
        delta = target_blocks // 2 - anchor_blocks // 2
    else:
        raise ValueError("placement must be 'left', 'center', or 'right'")
    support = tuple(i + delta for i in support)
    blocks = n // 16
    width = 16
    kernels = rate_kernels(grid, rounds, width)
    while blocks > 2:
        support, table = reverse_split(support, table, grid, width)
        blocks //= 2
        width *= 2
        stage_rounds = rounds
        if alternating:
            scale = width.bit_length() - 1
            stage_rounds = 151 if scale % 2 == high_parity else 149
        if top_alternating:
            distance_from_top = blocks.bit_length() - 2
            stage_rounds = (top_high if distance_from_top % 2 == 0
                            else top_low)
        kernels = rate_kernels(grid, stage_rounds, width)
        for offset in (1, 0):
            support, table = reverse_pass(support, table, blocks, grid, width,
                                          offset, kernels)
    if support != (0, 1):
        raise AssertionError(f"unexpected top support {support}")
    best_log_rate = NEG_INF
    for a in range(grid + 1):
        for b in range(grid + 1):
            a_wires = a * width // grid
            b_wires = b * width // grid
            candidate = (0.5 * table[a, b]
                         + (log_choose(width, a_wires)
                            + log_choose(width, b_wires)
                            - (2 * width) * math.log(2.0)) / (2 * width))
            best_log_rate = max(best_log_rate, candidate)
    return -best_log_rate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-n", type=int, default=10)
    parser.add_argument("--rounds", type=int, default=70)
    parser.add_argument("--anchor-rounds", type=int, default=150,
                        help="rounds at widths 8 and 16 in the finite anchor")
    parser.add_argument("--grid", type=int, default=16)
    parser.add_argument("--anchor-edge", type=int, default=126)
    parser.add_argument("--alternate-149-151", action="store_true")
    parser.add_argument("--high-parity", type=int, choices=(0, 1), default=0)
    parser.add_argument("--top-alternating-149-151", action="store_true")
    parser.add_argument("--top-high", type=int, default=151)
    parser.add_argument("--top-low", type=int, default=149)
    parser.add_argument("--placement", choices=("left", "center", "right"),
                        default="center",
                        help="translate the finite anchor to the corresponding global position")
    args = parser.parse_args()
    if args.log_n < 8 or args.grid not in (1, 2, 4, 8, 16):
        raise ValueError("requires log-n >= 8 and a grid dividing 16")
    rate = asymptotic_rate(args.log_n, args.rounds, args.grid, args.anchor_edge,
                           args.alternate_149_151, args.high_parity,
                           args.top_alternating_149_151,
                           args.top_high, args.top_low, args.placement,
                           args.anchor_rounds)
    print(f"log_n={args.log_n} rounds={args.rounds} anchor_rounds={args.anchor_rounds} grid={args.grid}")
    if args.alternate_149_151:
        print(f"alternating_rounds=149/151 high_scale_parity={args.high_parity}")
    if args.top_alternating_149_151:
        print(f"top-relative rounds={args.top_high},{args.top_low},...")
    print(f"edge placement={args.placement}")
    print(f"max_path_rate={rate:.12g}  ln2={math.log(2):.12g}")


if __name__ == "__main__":
    main()
