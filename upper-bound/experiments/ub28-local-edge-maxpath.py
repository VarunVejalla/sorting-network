#!/usr/bin/env python3
"""Max-log local trajectory screen for the UB-28 first-moment route.

For one fixed output edge, this computes the most likely sequence of local
block counts leading to a terminal inversion. Count-path multiplicities are
subexponential in n for fixed rounds, so this is the relevant exponential
rate candidate. It is a finite numerical screen, not a proof of a uniform
asymptotic bound.
"""

import argparse
import importlib.util
import math
from functools import lru_cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_local_edge_exact", HERE / "ub28-local-edge-transfer.py"
)
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)

NEG_INF = -math.inf


def log_choose(n, k):
    if k < 0 or k > n:
        return NEG_INF
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def maxplus_product(a, b):
    result = np.full((a.shape[0], b.shape[1]), NEG_INF, dtype=np.float64)
    for k in range(a.shape[1]):
        np.maximum(result, a[:, k, None] + b[k, None, :], out=result)
    return result


@lru_cache(maxsize=None)
def matching_maxpath_kernels(width, rounds):
    """K[input-left,output-left] = max count-path log probability."""
    result = {}
    for total in range(2 * width + 1):
        counts = tuple(range(max(0, total - width), min(width, total) + 1))
        one = np.full((len(counts), len(counts)), NEG_INF, dtype=np.float64)
        for i, left in enumerate(counts):
            right_ones = total - left
            denom = log_choose(width, left)
            lo = max(0, left - (width - right_ones))
            hi = min(left, right_ones)
            for out_left in range(lo, hi + 1):
                j = out_left - counts[0]
                one[i, j] = (
                    log_choose(right_ones, out_left)
                    + log_choose(width - right_ones, left - out_left)
                    - denom
                )
        power = np.full_like(one, NEG_INF)
        np.fill_diagonal(power, 0.0)
        exponent = rounds
        base = one
        while exponent:
            if exponent & 1:
                power = maxplus_product(power, base)
            exponent >>= 1
            if exponent:
                base = maxplus_product(base, base)
        result[total] = (counts, power)
    return result


def split_logmass(parent_width, child_width, count, left):
    right = count - left
    return (log_choose(count, left)
            + log_choose(parent_width - count, child_width - left)
            - log_choose(parent_width, child_width))


def reverse_split(support, table, child_width):
    parent_width = 2 * child_width
    for parent in sorted({i // 2 for i in support}):
        children = [i for i in (2 * parent, 2 * parent + 1) if i in support]
        axes = [support.index(i) for i in children]
        rest_axes = [i for i in range(table.ndim) if i not in axes]
        moved = np.moveaxis(table, axes + rest_axes,
                            list(range(len(axes) + len(rest_axes))))
        rest_shape = moved.shape[len(axes):]
        flat = moved.reshape((child_width + 1,) * len(axes) + (-1,))
        out = np.full((parent_width + 1, flat.shape[-1]), NEG_INF)
        for count in range(parent_width + 1):
            lo = max(0, count - child_width)
            hi = min(child_width, count)
            for left in range(lo, hi + 1):
                mass = split_logmass(parent_width, child_width, count, left)
                if len(axes) == 2:
                    candidate = mass + flat[left, count - left]
                else:
                    selected = left if children[0] % 2 == 0 else count - left
                    candidate = mass + flat[selected]
                np.maximum(out[count], candidate, out=out[count])
        out = out.reshape((parent_width + 1,) + rest_shape)
        insert = sum(i // 2 < parent for i in support if i // 2 != parent)
        out = np.moveaxis(out, 0, insert)
        support = tuple(sorted((set(support) - set(children)) | {parent}))
        table = out
    return support, table


def reverse_pass(support, table, blocks, width, offset, rounds):
    kernels = matching_maxpath_kernels(width, rounds)
    for left in range(offset, blocks - 1, 2):
        right = left + 1
        if left not in support and right not in support:
            continue
        expanded = tuple(sorted(set(support) | {left, right}))
        if expanded != support:
            table = np.broadcast_to(
                table.reshape(tuple(width + 1 if i in support else 1 for i in expanded)),
                (width + 1,) * len(expanded),
            ).copy()
            support = expanded
        axis_left, axis_right = support.index(left), support.index(right)
        rest_axes = [i for i in range(table.ndim) if i not in (axis_left, axis_right)]
        moved = np.moveaxis(table, (axis_left, axis_right, *rest_axes),
                            tuple(range(table.ndim)))
        rest_shape = moved.shape[2:]
        flat = moved.reshape(width + 1, width + 1, -1)
        out = np.full_like(flat, NEG_INF)
        for total, (counts, kernel) in kernels.items():
            source = np.stack([flat[x, total - x] for x in counts], axis=0)
            for i, x in enumerate(counts):
                np.max(kernel[i, :, None] + source, axis=0, out=out[x, total - x])
        out = out.reshape(moved.shape)
        table = np.moveaxis(out, tuple(range(table.ndim)),
                            (axis_left, axis_right, *rest_axes))
    return support, table


def edge_max_log_probability(n, edge, rounds):
    support, terminal = exact.exact_tail_event(n, edge)
    table = np.full((5,) * len(support), NEG_INF, dtype=np.float64)
    for key, bad in terminal.items():
        if bad:
            table[key] = 0.0

    blocks, width = n // 4, 4
    support, table = reverse_split(support, table, width)
    blocks //= 2
    width *= 2
    while True:
        for offset in (1, 0):
            support, table = reverse_pass(support, table, blocks, width,
                                          offset, rounds)
        if blocks == 2:
            break
        support, table = reverse_split(support, table, width)
        blocks //= 2
        width *= 2

    assert support == (0, 1)
    best = NEG_INF
    for a in range(width + 1):
        for b in range(width + 1):
            candidate = (table[a, b] + log_choose(width, a)
                         + log_choose(width, b) - n * math.log(2))
            best = max(best, candidate)
    return best


def edge_max_log_probability_top_alternating(n, edge, low=20, high=280,
                                            anchor=150):
    """Exact finite max-path rate for low/high rounds counted from the top."""
    support, terminal = exact.exact_tail_event(n, edge)
    table = np.full((5,) * len(support), NEG_INF, dtype=np.float64)
    for key, bad in terminal.items():
        if bad:
            table[key] = 0.0
    blocks, width = n // 4, 4
    support, table = reverse_split(support, table, width)
    blocks //= 2
    width *= 2
    while True:
        if width <= 16:
            rounds = anchor
        else:
            distance = blocks.bit_length() - 2
            rounds = high if distance % 2 == 0 else low
        for offset in (1, 0):
            support, table = reverse_pass(support, table, blocks, width,
                                          offset, rounds)
        if blocks == 2:
            break
        support, table = reverse_split(support, table, width)
        blocks //= 2
        width *= 2
    assert support == (0, 1)
    best = NEG_INF
    for a in range(width + 1):
        for b in range(width + 1):
            candidate = (table[a, b] + log_choose(width, a)
                         + log_choose(width, b) - n * math.log(2))
            best = max(best, candidate)
    return best


def edge_state_at_width(n, edge, rounds, cutoff_width):
    """Exact finite max-path table at a chosen block width, before its split."""
    support, terminal = exact.exact_tail_event(n, edge)
    table = np.full((5,) * len(support), NEG_INF, dtype=np.float64)
    for key, bad in terminal.items():
        if bad:
            table[key] = 0.0
    blocks, width = n // 4, 4
    support, table = reverse_split(support, table, width)
    blocks //= 2
    width *= 2
    while True:
        for offset in (1, 0):
            support, table = reverse_pass(support, table, blocks, width,
                                          offset, rounds)
        if width == cutoff_width:
            return support, table, blocks
        if blocks == 2:
            raise ValueError("cutoff_width exceeds top block width")
        support, table = reverse_split(support, table, width)
        blocks //= 2
        width *= 2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=70)
    parser.add_argument("--edge", type=int, required=True)
    args = parser.parse_args()
    if args.n < 32 or args.n & (args.n - 1):
        raise ValueError("n must be a power of two >= 32")
    logp = edge_max_log_probability(args.n, args.edge, args.rounds)
    print(f"edge={args.edge} max_path_log_probability={logp:.12g}")
    print(f"max_path_rate=-logP/n={-logp / args.n:.12g}")


if __name__ == "__main__":
    main()
