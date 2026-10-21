#!/usr/bin/env python3
"""Coarse analytic cell-Bellman screen for one central UB-28 edge.

The one-round matching and split log rates are negative mutual informations.
Pinsker's inequality bounds them above using separation of density intervals.
The resulting cell kernels are safe upper bounds on each asymptotic local
transition; max-plus composition therefore gives a safe (usually loose)
upper bound on the entropy-rate variational problem for this edge phase.

This is not yet a theorem about sorting networks: it uses floating arithmetic,
one edge phase, an exact finite anchor at that edge, and omits the uniform
finite-type/path-count proof. It tests whether a simple analytic cell
potential has enough rate margin to justify further work.
"""

import argparse
import importlib.util
from itertools import product
import math
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_local_edge_maxpath", HERE / "ub28-local-edge-maxpath.py"
)
maxpath = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(maxpath)

NEG_INF = -math.inf


def cell_interval(index, bins):
    return index / bins, (index + 1) / bins


def interval_gap(a0, a1, b0, b1):
    return max(0.0, a0 - b1, b0 - a1)


def matching_cell_kernel(bins, refine=1):
    """Upper bound one-round log rates, indexed source-pair -> target-pair.

    ``refine`` subdivides each source density cell while bounding the
    covariance gap. The Bellman state remains at ``bins`` resolution, so this
    tightens local kernels without eliminating cross-transition cell resets.
    """
    pairs = bins * bins
    kernel = np.full((pairs, pairs), NEG_INF)
    for a_cell in range(bins):
        for b_cell in range(bins):
            source = a_cell * bins + b_cell
            for x_cell in range(bins):
                for y_cell in range(bins):
                    x0, x1 = cell_interval(x_cell, bins)
                    y0, y1 = cell_interval(y_cell, bins)
                    best = NEG_INF
                    for ai in range(refine):
                        a0 = (a_cell + ai / refine) / bins
                        a1 = (a_cell + (ai + 1) / refine) / bins
                        for bi in range(refine):
                            b0 = (b_cell + bi / refine) / bins
                            b1 = (b_cell + (bi + 1) / refine) / bins
                            total_lo, total_hi = a0 + b0, a1 + b1
                            product_lo, product_hi = a0 * b0, a1 * b1
                            # Enclose feasible overlaps x=P[A=B=1], imposing
                            # both output cells and the Fréchet constraints.
                            allowed_x0 = max(x0, total_lo - y1, 0.0,
                                             total_lo - 1.0)
                            allowed_x1 = min(x1, total_hi - y0, a1, b1)
                            if allowed_x0 > allowed_x1:
                                continue
                            delta = interval_gap(
                                allowed_x0, allowed_x1,
                                product_lo, product_hi
                            )
                            # I(A;B) >= 8 * covariance^2.
                            best = max(best, -8.0 * delta**2)
                    kernel[source, x_cell * bins + y_cell] = best
    return kernel


def split_cell_kernel(bins):
    """Upper bound split log rates, indexed parent cell -> child-cell pair."""
    kernel = np.full((bins, bins, bins), NEG_INF)
    for parent in range(bins):
        c0, c1 = cell_interval(parent, bins)
        for left in range(bins):
            l0, l1 = cell_interval(left, bins)
            for right in range(bins):
                r0, r1 = cell_interval(right, bins)
                avg0, avg1 = (l0 + r0) / 2, (l1 + r1) / 2
                if interval_gap(c0, c1, avg0, avg1) > 0:
                    continue
                delta = interval_gap(l0, l1, r0, r1)
                # I(half-label; bit) >= (left_density-right_density)^2 / 2.
                kernel[parent, left, right] = -0.5 * delta**2
    return kernel


def maxplus_product(left, right):
    return np.max(left[:, :, None] + right[None, :, :], axis=1)


def maxplus_power(kernel, exponent):
    size = kernel.shape[0]
    result = np.full((size, size), NEG_INF)
    np.fill_diagonal(result, 0.0)
    base = kernel
    while exponent:
        if exponent & 1:
            result = maxplus_product(result, base)
        exponent >>= 1
        if exponent:
            base = maxplus_product(base, base)
    return result


def close_support(support, blocks, offset):
    result = set(support)
    for left in range(offset, blocks - 1, 2):
        if left in result or left + 1 in result:
            result.update((left, left + 1))
    return result


def reverse_split(support, table, parent_width, split_kernel):
    bins = split_kernel.shape[0]
    for parent in sorted({index // 2 for index in support}):
        children = (2 * parent, 2 * parent + 1)
        present = [child for child in children if child in support]
        axes = [support.index(child) for child in present]
        rest = [axis for axis in range(table.ndim) if axis not in axes]
        moved = np.moveaxis(table, axes + rest, list(range(table.ndim)))
        rest_shape = moved.shape[len(axes) :]

        if len(axes) == 2:
            values = moved.reshape((bins * bins, -1))
            local = split_kernel.reshape((bins, bins * bins))
            out = np.max(local[:, :, None] + 0.5 * values[None, :, :], axis=1)
        else:
            selected = present[0]
            if selected == children[0]:
                local = np.max(split_kernel, axis=2)
            else:
                local = np.max(split_kernel, axis=1)
            values = moved.reshape((bins, -1))
            out = np.max(local[:, :, None] + 0.5 * values[None, :, :], axis=1)

        out = out.reshape((bins,) + rest_shape)
        new_support = sorted((set(support) - set(children)) | {parent})
        insert = sum(index < parent for index in new_support)
        table = np.moveaxis(out, 0, insert)
        support = new_support
    return support, table


def reverse_pass(support, table, blocks, offset, pair_kernel, bins):
    for left in range(offset, blocks - 1, 2):
        right = left + 1
        if left not in support and right not in support:
            continue
        expanded = sorted(set(support) | {left, right})
        if expanded != support:
            table = np.broadcast_to(
                table.reshape(tuple(bins if index in support else 1 for index in expanded)),
                (bins,) * len(expanded),
            ).copy()
            support = expanded
        axis_left, axis_right = support.index(left), support.index(right)
        rest = [axis for axis in range(table.ndim) if axis not in (axis_left, axis_right)]
        moved = np.moveaxis(table, (axis_left, axis_right, *rest), range(table.ndim))
        values = moved.reshape((bins * bins, -1))
        out = np.max(pair_kernel[:, :, None] + values[None, :, :], axis=1)
        out = out.reshape((bins, bins) + moved.shape[2:])
        table = np.moveaxis(out, range(table.ndim), (axis_left, axis_right, *rest))
    return support, table


def compress_anchor(finite_table, bins):
    mask = np.isfinite(finite_table)
    compressed = np.zeros((bins,) * mask.ndim, dtype=bool)
    for cell_indices in product(range(bins), repeat=mask.ndim):
        slices = []
        for index in cell_indices:
            lo = (16 * index + bins - 1) // bins
            hi = (16 * (index + 1)) // bins
            slices.append(slice(lo, hi + 1))
        compressed[cell_indices] = np.any(mask[tuple(slices)])
    return np.where(compressed, 0.0, NEG_INF)


def entropy(x):
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log(x) - (1.0 - x) * math.log1p(-x)


def entropy_upper(index, bins):
    lo, hi = cell_interval(index, bins)
    return math.log(2.0) if lo <= 0.5 <= hi else max(entropy(lo), entropy(hi))


def run(log_n, bins, high, low, anchor_rounds, edge=None, kernel_refine=1):
    n = 1 << log_n
    edge = n // 2 - 2 if edge is None else edge
    support, anchor, _ = maxpath.edge_state_at_width(n, edge, anchor_rounds, 16)
    if len(support) > 6:
        raise AssertionError(f"anchor support too large: {support}")
    table = compress_anchor(anchor, bins)
    viable_cells = int(np.isfinite(table).sum())
    split_kernel = split_cell_kernel(bins)
    one_round = matching_cell_kernel(bins, kernel_refine)

    blocks, width = n // 16, 16
    while blocks > 2:
        parent_width = width * 2
        support, table = reverse_split(support, table, parent_width, split_kernel)
        blocks //= 2
        width = parent_width
        distance_from_top = (log_n - 1) - int(math.log2(width))
        rounds = high if distance_from_top % 2 == 0 else low
        pair_kernel = maxplus_power(one_round, rounds)
        for offset in (1, 0):
            support, table = reverse_pass(
                support, table, blocks, offset, pair_kernel, bins
            )

    if support != [0, 1] and tuple(support) != (0, 1):
        raise AssertionError(f"unexpected top support: {support}")
    best = NEG_INF
    for a in range(bins):
        for b in range(bins):
            initial = 0.5 * (entropy_upper(a, bins) + entropy_upper(b, bins)) - math.log(2.0)
            best = max(best, initial + 0.5 * table[a, b])
    half_cells = {bins // 2 - 1, bins // 2}
    half_action = max(table[a, b] for a in half_cells for b in half_cells)
    return edge, best, viable_cells, half_action


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=10)
    parser.add_argument("--bins", type=int, choices=(2, 4, 8), default=4)
    parser.add_argument("--high", type=int, default=280)
    parser.add_argument("--low", type=int, default=20)
    parser.add_argument("--anchor-rounds", type=int, default=150)
    parser.add_argument("--edge", type=int)
    parser.add_argument("--kernel-refine", type=int, choices=(1, 2, 4, 8),
                        default=1,
                        help="source-cell subdivision for tighter matching kernels")
    args = parser.parse_args()
    if args.log_n < 8:
        raise ValueError("require log-n >= 8")
    edge, exponent, viable_cells, half_action = run(
        args.log_n, args.bins, args.high, args.low, args.anchor_rounds,
        args.edge, args.kernel_refine
    )
    print(
        f"log_n={args.log_n} bins={args.bins} edge={edge} "
        f"viable_anchor_cells={viable_cells}/{args.bins**6} "
        f"half_density_action={half_action:.12g} "
        f"high_low={args.high},{args.low} kernel_refine={args.kernel_refine} "
        f"max_log_rate_upper={exponent:.12g} "
        f"target={-math.log(2):.12g} passes={exponent < -math.log(2)}"
    )


if __name__ == "__main__":
    main()
