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
    anchor_support, anchor, _ = maxpath.edge_state_at_width(
        n, edge, anchor_rounds, 16
    )
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
    return anchor_support, list(reversed(ops)), anchor


def sparse_reachability(n, edge, bins, start, high, low, anchor_rounds,
                        max_states):
    anchor_support, forward_ops, anchor = reverse_support_ops(
        n, edge, anchor_rounds, high, low
    )
    one = cells.matching_cell_kernel(bins)
    split = cells.split_cell_kernel(bins)
    zero_split = np.isfinite(split) & (np.abs(split) < 1e-12)
    split_targets = [list(zip(*np.where(zero_split[p]))) for p in range(bins)]
    pair_targets = {}
    support = [0, 1]
    reachable = {start}
    for kind, support_pre, support_post, index, width, extra in forward_ops:
        if support != support_pre:
            raise RuntimeError(f"support mismatch: {support} != {support_pre}")
        next_states = set()
        if kind == "match":
            right, rounds = extra
            if rounds not in pair_targets:
                kernel = cells.maxplus_power(one, rounds)
                zero_pair = np.isfinite(kernel) & (np.abs(kernel) < 1e-12)
                pair_targets[rounds] = [
                    np.flatnonzero(row).tolist() for row in zero_pair
                ]
            targets = pair_targets[rounds]
            ax, ay = support_pre.index(index), support_pre.index(right)
            for state in reachable:
                source = state[ax] * bins + state[ay]
                for target in targets[source]:
                    values = list(state)
                    values[ax], values[ay] = divmod(target, bins)
                    next_states.add(tuple(
                        values[support_pre.index(i)] for i in support_post
                    ))
        else:
            parent = index
            axis = support_pre.index(parent)
            children = (2 * parent, 2 * parent + 1)
            present = [child for child in children if child in support_post]
            for state in reachable:
                for left, right in split_targets[state[axis]]:
                    values = dict(zip(support_pre, state))
                    values.pop(parent)
                    if children[0] in present:
                        values[children[0]] = left
                    if children[1] in present:
                        values[children[1]] = right
                    next_states.add(tuple(values[i] for i in support_post))
        reachable = next_states
        support = support_post
        if len(reachable) > max_states:
            return support, len(reachable), None, anchor_support, anchor, False

    if support != list(anchor_support):
        raise RuntimeError(f"terminal support mismatch: {support} != {anchor_support}")
    viable = 0
    for state in reachable:
        slices = []
        for cell in state:
            lo = (16 * cell + bins - 1) // bins
            hi = (16 * (cell + 1) + bins - 1) // bins
            slices.append(slice(lo, hi + 1))
        viable += int(np.isfinite(anchor[tuple(slices)]).any())
    return support, len(reachable), viable, anchor_support, anchor, True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=10)
    parser.add_argument("--bins", type=int, choices=(4, 8, 16), default=8)
    parser.add_argument("--high", type=int, default=235)
    parser.add_argument("--low", type=int, default=35)
    parser.add_argument("--anchor-rounds", type=int, default=150)
    parser.add_argument("--edge", type=int, help="defaults to the central residue-0 edge")
    parser.add_argument("--start", nargs=2, type=int,
                        help="one top density-cell pair; defaults to the four half cells")
    parser.add_argument("--max-states", type=int, default=200000,
                        help="sparse reachability cap for the 16-bin diagnostic")
    args = parser.parse_args()

    n = 1 << args.log_n
    bins = args.bins
    edge = n // 2 - 64 if args.edge is None else args.edge
    start_cells = tuple(args.start) if args.start else (bins // 2 - 1, bins // 2)
    if any(i < 0 or i >= bins for i in start_cells):
        raise ValueError("start cells must lie in the density grid")
    if bins == 16:
        support, count, viable_count, anchor_support, anchor, complete = (
            sparse_reachability(n, edge, bins, start_cells, args.high, args.low,
                                args.anchor_rounds, args.max_states)
        )
        print(f"n=2^{args.log_n} edge={edge} bins={bins} top_cells={start_cells}")
        print(f"width16_support={support} reachable_cells={count}")
        if complete:
            print(f"reachable_bad_cells={viable_count} "
                  f"exact_viable_profiles={int(np.isfinite(anchor).sum())}")
        else:
            print(f"state_cap_exceeded={args.max_states}; reachability is incomplete")
        return
    one = cells.matching_cell_kernel(bins)
    split = cells.split_cell_kernel(bins)
    zero_split = np.isfinite(split) & (np.abs(split) < 1e-12)
    anchor_support, forward_ops, anchor = reverse_support_ops(
        n, edge, args.anchor_rounds, args.high, args.low
    )
    support = [0, 1]
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

    viable = np.isfinite(cells.compress_anchor(anchor, bins))
    if support != list(anchor_support):
        raise RuntimeError(f"support mismatch: propagated={support}, anchor={anchor_support}")
    print(f"n=2^{args.log_n} edge={edge} bins={bins} top_cells={start_cells}")
    print(f"width16_support={support} reachable_cells={int(reach.sum())}")
    print(f"reachable_bad_cells={int((reach & viable).sum())} "
          f"viable_cells={int(viable.sum())}")


if __name__ == "__main__":
    main()
