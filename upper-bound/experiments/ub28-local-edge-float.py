#!/usr/bin/env python3
"""Scaled float64 version of the UB-28 one-edge local transfer.

This is a numerical scaling screen, not a proof. Unlike the exact Fraction
implementation, it stores dense local tables as NumPy arrays and rescales
after each transfer so that probabilities far below the normal float range
can still be reported through their logarithms.
"""

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def load_module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


exact = load_module("ub28_local_edge_exact", "ub28-local-edge-transfer.py")


def normalized(table, log_scale):
    peak = float(np.max(table))
    if peak == 0:
        return table, -math.inf
    return table / peak, log_scale + math.log(peak)


def make_tail_table(n, edge):
    support, values = exact.exact_tail_event(n, edge)
    shape = (5,) * len(support)
    table = np.empty(shape, dtype=np.float64)
    for index, value in values.items():
        table[index] = float(value)
    return support, table


def split_kernel(parent_width, child_width, count, child):
    """Mass of a selected child count given the parent count."""
    denom = math.comb(parent_width, child_width)
    lo = max(0, count - child_width)
    hi = min(child_width, count)
    result = {}
    for left in range(lo, hi + 1):
        right = count - left
        selected = left if child == 0 else right
        result[selected] = result.get(selected, 0.0) + (
            math.comb(count, left)
            * math.comb(parent_width - count, child_width - left)
            / denom
        )
    return result


def reverse_split(support, table, child_width):
    parent_width = 2 * child_width
    log_scale = 0.0
    for parent in sorted({index // 2 for index in support}):
        child_indices = [2 * parent, 2 * parent + 1]
        axes = [support.index(i) for i in child_indices if i in support]
        selected_children = [i % 2 for i in support if i // 2 == parent]
        rest_axes = [i for i in range(table.ndim) if i not in axes]
        moved = np.moveaxis(table, axes + rest_axes,
                            list(range(len(axes) + len(rest_axes))))
        rest_shape = moved.shape[len(axes):]
        flat = moved.reshape((child_width + 1,) * len(axes) + (-1,))
        out = np.zeros((parent_width + 1, flat.shape[-1]), dtype=np.float64)
        for count in range(parent_width + 1):
            if len(axes) == 2:
                for left, mass in split_kernel(parent_width, child_width, count, 0).items():
                    right = count - left
                    out[count] += mass * flat[left, right]
            else:
                child = selected_children[0]
                for value, mass in split_kernel(parent_width, child_width, count, child).items():
                    out[count] += mass * flat[value]
        out = out.reshape((parent_width + 1,) + rest_shape)
        insert = sum(i // 2 < parent for i in support if i // 2 != parent)
        out = np.moveaxis(out, 0, insert)
        new_support = tuple(sorted((set(support) - set(child_indices)) | {parent}))
        table = out
        support = new_support
        table, log_scale = normalized(table, log_scale)
    return support, table, log_scale


def matching_kernel(width, rounds):
    kernels = {}
    for total in range(2 * width + 1):
        inputs = range(max(0, total - width), min(width, total) + 1)
        outputs = range(max(0, total - width), min(width, total) + 1)
        inputs, outputs = tuple(inputs), tuple(outputs)
        one = np.zeros((len(inputs), len(outputs)), dtype=np.float64)
        for i, left_count in enumerate(inputs):
            right_ones = total - left_count
            lo = max(0, left_count - (width - right_ones))
            hi = min(left_count, right_ones)
            denom = math.comb(width, left_count)
            for out_left in range(lo, hi + 1):
                j = outputs.index(out_left)
                one[i, j] = (
                    math.comb(right_ones, out_left)
                    * math.comb(width - right_ones, left_count - out_left)
                    / denom
                )
        matrix = np.linalg.matrix_power(one, rounds)
        kernels[total] = (inputs, outputs, matrix)
    return kernels


def apply_matching(support, table, left, right, kernels):
    width = table.shape[0] - 1
    axes = [support.index(left), support.index(right)]
    rest_axes = [i for i in range(table.ndim) if i not in axes]
    moved = np.moveaxis(table, axes + rest_axes,
                        [0, 1] + list(range(2, table.ndim)))
    rest_shape = moved.shape[2:]
    flat = moved.reshape((width + 1, width + 1, -1))
    out = np.zeros_like(flat)
    for total, (inputs, outputs, matrix) in kernels.items():
        values = np.stack([flat[x, total - x] for x in outputs], axis=0)
        transformed = matrix @ values
        for i, x in enumerate(inputs):
            out[x, total - x] = transformed[i]
    out = out.reshape(moved.shape)
    table = np.moveaxis(out, list(range(table.ndim)), axes + rest_axes)
    return normalized(table, 0.0)


def reverse_pass(support, table, blocks, width, offset, rounds):
    log_scale = 0.0
    kernels = matching_kernel(width, rounds)
    for left in range(offset, blocks - 1, 2):
        right = left + 1
        if left not in support and right not in support:
            continue
        expanded = tuple(sorted(set(support) | {left, right}))
        if expanded != support:
            shape = [width + 1] * len(expanded)
            table = np.broadcast_to(table.reshape(
                tuple(width + 1 if i in support else 1 for i in expanded)), shape).copy()
            support = expanded
        table, local_scale = apply_matching(support, table, left, right, kernels)
        log_scale += local_scale
    return support, table, log_scale


def edge_log_probability(n, edge, rounds):
    support, table = make_tail_table(n, edge)
    log_scale = 0.0
    blocks, width = n // 4, 4
    support, table, delta = reverse_split(support, table, width)
    log_scale += delta
    blocks //= 2
    width *= 2
    while True:
        for offset in (1, 0):
            support, table, delta = reverse_pass(support, table, blocks, width, offset, rounds)
            log_scale += delta
        if blocks == 2:
            break
        support, table, delta = reverse_split(support, table, width)
        log_scale += delta
        blocks //= 2
        width *= 2
    assert support == (0, 1)
    # Each top block is uniform; use a normalized binomial mass for each.
    weights = np.array([math.comb(width, a) / 2**width for a in range(width + 1)])
    probability = float(np.sum(table * weights[:, None] * weights[None, :]))
    return math.log(probability) + log_scale if probability else -math.inf


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=70)
    parser.add_argument("--edge", type=int, required=True)
    args = parser.parse_args()
    if args.n < 32 or args.n & (args.n - 1):
        raise ValueError("n must be a power of two >= 32")
    logp = edge_log_probability(args.n, args.edge, args.rounds)
    print(f"edge={args.edge} log_P[bad]={logp:.12g}")
    print(f"rate=-log_P/n={-logp / args.n:.12g}")


if __name__ == "__main__":
    main()
