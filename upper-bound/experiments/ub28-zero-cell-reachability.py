#!/usr/bin/env python3
"""Trace zero-cost paths in the coarse UB-28 density-cell abstraction.

This checks whether cells connected by zero-rate matching/split kernels can
reach any cell containing a viable width-16 anchor profile. Such a path is
only an abstraction witness: each transition may choose different densities
inside a shared cell.
"""

import argparse
import importlib.util
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


maxpath = load("ub28_maxpath", "ub28-local-edge-maxpath.py")
cells = load("ub28_cells", "ub28-pinsker-cell-bellman.py")


def reorder_and_project(reachable, old_support, new_support):
    dropped = tuple(old_support.index(i) for i in old_support
                    if i not in new_support)
    if dropped:
        reachable = np.any(reachable, axis=dropped)
    remaining = [i for i in old_support if i in new_support]
    permutation = [remaining.index(i) for i in new_support]
    if permutation != list(range(len(permutation))):
        reachable = np.transpose(reachable, permutation)
    return reachable


def forward_match(reachable, support_pre, support_post, left, right,
                  zero_pair, bins):
    axes = (support_pre.index(left), support_pre.index(right))
    rest = [i for i in range(reachable.ndim) if i not in axes]
    moved = np.moveaxis(reachable, (*axes, *rest), range(reachable.ndim))
    rest_shape = moved.shape[2:]
    source = moved.reshape(bins * bins, -1).astype(np.uint8)
    target = (zero_pair.T.astype(np.uint8) @ source) > 0
    moved_out = target.reshape((bins, bins) + rest_shape)
    reachable = np.moveaxis(moved_out, range(reachable.ndim),
                            (*axes, *rest))
    return reorder_and_project(reachable, support_pre, support_post)


def forward_split(reachable, support_pre, support_post, parent,
                  zero_split, bins):
    children = (2 * parent, 2 * parent + 1)
    present = tuple(child for child in children if child in support_post)
    if not present:
        return reorder_and_project(reachable, support_pre, support_post)
    local = zero_split.copy()
    if children[0] not in present:
        local = local.any(axis=0)
    if children[1] not in present:
        local = local.any(axis=-1)
    relation = local.reshape(bins, -1).astype(np.uint8)
    axis = support_pre.index(parent)
    rest = [i for i in range(reachable.ndim) if i != axis]
    moved = np.moveaxis(reachable, (axis, *rest), range(reachable.ndim))
    rest_shape = moved.shape[1:]
    source = moved.reshape(bins, -1).astype(np.uint8)
    target = (relation.T @ source) > 0
    child_shape = (bins,) * len(present)
    moved_out = target.reshape(child_shape + rest_shape)
    labels = list(present) + [i for i in support_pre if i != parent]
    return reorder_and_project(moved_out, labels, support_post)


def reverse_support_ops(n, edge, anchor_rounds, high, low):
    anchor_support, _, _ = maxpath.edge_state_at_width(n, edge, anchor_rounds, 16)
    support = list(anchor_support)
    blocks, width = n // 16, 16
    ops = []
    while blocks > 2:
        for parent in sorted({i // 2 for i in support}):
            children = tuple(i for i in (2 * parent, 2 * parent + 1)
                             if i in support)
            before = list(support)
            after = sorted((set(support) - set(children)) | {parent})
            ops.append(("split", after, before, parent, width * 2, None))
            support = after
        blocks //= 2
        width *= 2
        distance = (n.bit_length() - 2) - (width.bit_length() - 1)
        rounds = high if distance % 2 == 0 else low
        for offset in (1, 0):
            for left in range(offset, blocks - 1, 2):
                right = left + 1
                if left not in support and right not in support:
                    continue
                before = list(support)
                after = sorted(set(support) | {left, right})
                ops.append(("match", after, before, left, width, (right, rounds)))
                support = after
    if support != [0, 1]:
        raise RuntimeError(f"top support mismatch: {support}")
    return anchor_support, list(reversed(ops))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=10)
    parser.add_argument("--bins", type=int, choices=(4, 8), default=8)
    parser.add_argument("--high", type=int, default=235)
    parser.add_argument("--low", type=int, default=35)
    parser.add_argument("--anchor-rounds", type=int, default=150)
    parser.add_argument("--edge", type=int, help="defaults to the central residue-0 edge")
    parser.add_argument("--start", nargs=2, type=int,
                        help="one top density-cell pair; defaults to the four half cells")
    args = parser.parse_args()

    n = 1 << args.log_n
    bins = args.bins
    edge = n // 2 - 64 if args.edge is None else args.edge
    one = cells.matching_cell_kernel(bins)
    split = cells.split_cell_kernel(bins)
    zero_split = np.isfinite(split) & (np.abs(split) < 1e-12)
    anchor_support, forward_ops = reverse_support_ops(
        n, edge, args.anchor_rounds, args.high, args.low
    )
    support = [0, 1]
    start_cells = tuple(args.start) if args.start else (bins // 2 - 1, bins // 2)
    if any(i < 0 or i >= bins for i in start_cells):
        raise ValueError("start cells must lie in the density grid")
    reach = np.zeros((bins, bins), dtype=bool)
    reach[start_cells[0], start_cells[1]] = True
    for kind, support_pre, support_post, index, width, extra in forward_ops:
        if support != support_pre:
            raise RuntimeError(f"profile support mismatch at {kind}: "
                               f"{support} != {support_pre}")
        if kind == "match":
            right, rounds = extra
            pair_kernel = cells.maxplus_power(one, rounds)
            zero_pair = np.isfinite(pair_kernel) & (np.abs(pair_kernel) < 1e-12)
            reach = forward_match(reach, support_pre, support_post,
                                  index, right, zero_pair, bins)
        else:
            zero_split = np.isfinite(split) & (np.abs(split) < 1e-12)
            reach = forward_split(reach, support_pre, support_post,
                                  index, zero_split, bins)
        support = support_post

    anchor_support_check, anchor, _ = maxpath.edge_state_at_width(
        n, edge, args.anchor_rounds, 16
    )
    viable = np.isfinite(cells.compress_anchor(anchor, bins))
    if support != list(anchor_support) or support != list(anchor_support_check):
        raise RuntimeError(f"support mismatch: propagated={support}, anchor={anchor_support_check}")
    print(f"n=2^{args.log_n} edge={edge} bins={bins} top_cells={start_cells}")
    print(f"width16_support={support} reachable_cells={int(reach.sum())}")
    print(f"reachable_bad_cells={int((reach & viable).sum())} "
          f"viable_cells={int(viable.sum())}")


if __name__ == "__main__":
    main()
