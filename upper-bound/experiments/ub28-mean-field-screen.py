#!/usr/bin/env python3
"""Zero-cost mean-field diagnostic for one UB-28 terminal edge.

The script propagates the typical type law under the zero-rate matching and
split kernels. By default it stops when the schedule switches to the exact
finite-width suffix. An explicit unsafe flag continues the mean-field model
through those small widths and reports a diagnostic terminal mass; that
quantity omits finite-width dependence and is not a probability bound.
"""

import argparse
from collections import defaultdict
import importlib.util
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent


def load_module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


support_module = load_module(
    "ub28_backward_window_support", "ub28-backward-window-support.py"
)
tail_windows = support_module.terminal
tail_counts = load_module("ub28_terminal_count_gate", "ub28-terminal-count-gate.py")


def support_phases_by_width(n, edge):
    blocks = n // 4
    terminal_supports = tail_windows.output_supports(blocks)
    child_support = (set(terminal_supports[edge])
                     | set(terminal_supports[edge + 1]))
    result = {4: child_support}
    width = 8
    while True:
        blocks = n // width
        after_pass = {index // 2 for index in child_support}
        after_offset0 = support_module.close_under_pairs(
            after_pass, blocks, 1
        )
        before_pass = support_module.close_under_pairs(
            after_offset0, blocks, 0
        )
        result[width] = (before_pass, after_offset0, after_pass)
        child_support = before_pass
        if blocks == 2:
            break
        width *= 2
    return result


def matching_map(q, left_bit, right_bit):
    previous = np.arange(q)[:, None, None]
    current = np.arange(q)[None, :, None]
    following = np.arange(q)[None, None, :]
    left = np.minimum((current >> left_bit) & 1,
                      (following >> right_bit) & 1)
    right = np.maximum((previous >> left_bit) & 1,
                       (current >> right_bit) & 1)
    output = current.copy()
    output = (output & ~(1 << left_bit)) | (left << left_bit)
    output = (output & ~(1 << right_bit)) | (right << right_bit)
    return np.broadcast_to(output, (q, q, q))


def mean_match(p, row_ids, left, right, cache):
    q = len(p)
    left_bit = row_ids.index(left)
    right_bit = row_ids.index(right)
    key = (q, left_bit, right_bit)
    if key not in cache:
        cache[key] = matching_map(q, left_bit, right_bit)
    masses = p[:, None, None] * p[None, :, None] * p[None, None, :]
    result = np.bincount(cache[key].ravel(), weights=masses.ravel(),
                         minlength=q)
    return result / result.sum()


def mean_split(p, parent_ids, child_ids):
    parent_positions = {block: index for index, block in enumerate(parent_ids)}
    q_parent = len(p)
    q_child = 1 << len(child_ids)
    mapping = np.zeros((q_parent, q_parent), dtype=np.int64)
    for u in range(q_parent):
        for v in range(q_parent):
            child_type = 0
            for index, child in enumerate(child_ids):
                parent_pos = parent_positions[child // 2]
                source = u if child % 2 == 0 else v
                bit = (source >> parent_pos) & 1
                child_type |= bit << index
            mapping[u, v] = child_type
    masses = p[:, None] * p[None, :]
    result = np.bincount(mapping.ravel(), weights=masses.ravel(),
                         minlength=q_child)
    return result / result.sum()


def project_distribution(p, old_ids, new_ids):
    positions = {block: index for index, block in enumerate(old_ids)}
    mapping = np.zeros(len(p), dtype=np.int64)
    for old_type in range(len(p)):
        new_type = 0
        for index, block in enumerate(new_ids):
            new_type |= ((old_type >> positions[block]) & 1) << index
        mapping[old_type] = new_type
    result = np.bincount(mapping, weights=p, minlength=1 << len(new_ids))
    return result / result.sum()


def terminal_bad_mass(p, support, n, edge):
    states = {(0,) * len(support): 1.0}
    types = [(t, mass) for t, mass in enumerate(p) if mass > 0.0]
    for _ in range(4):
        next_states = defaultdict(float)
        for counts, state_mass in states.items():
            for row_type, type_mass in types:
                updated = tuple(count + ((row_type >> i) & 1)
                                for i, count in enumerate(counts))
                next_states[updated] += state_mass * type_mass
        states = next_states

    bad_mass = 0.0
    total = 0.0
    for counts, mass in states.items():
        profile = [0] * (n // 4)
        for block, count in zip(sorted(support), counts):
            profile[block] = count
        output = tail_counts.tail_output(profile)
        total += mass
        if output[edge] > output[edge + 1]:
            bad_mass += mass
    if abs(total - 1.0) > 1e-9:
        raise ArithmeticError(f"terminal type mass sums to {total}")
    return bad_mass


def run(n, edge, rounds, min_random_width=200, unsafe_meanfield_tail=False,
        show_types=False):
    if n < 32 or n & (n - 1) or not 0 <= edge < n - 1:
        raise ValueError("n must be a power of two >=32 and edge in range")
    supports = support_phases_by_width(n, edge)
    top_width = n // 2
    parent_ids = sorted(supports[top_width][0])
    if parent_ids != [0, 1]:
        raise AssertionError((n, edge, parent_ids))
    p = np.full(1 << len(parent_ids), 1.0 / (1 << len(parent_ids)))
    cache = {}
    stopped_at_exact_suffix = None

    for width in sorted((w for w in supports if w >= 8), reverse=True):
        if width < min_random_width and not unsafe_meanfield_tail:
            stopped_at_exact_suffix = width
            break
        input_ids, mid_ids, output_ids = map(sorted, supports[width])
        blocks = n // width
        for left in range(0, blocks - 1, 2):
            if left in mid_ids or left + 1 in mid_ids:
                if left not in input_ids or left + 1 not in input_ids:
                    raise AssertionError((width, input_ids, mid_ids, left))
                for _ in range(rounds):
                    p = mean_match(p, input_ids, left, left + 1, cache)
        p = project_distribution(p, input_ids, mid_ids)
        for left in range(1, blocks - 1, 2):
            if left in output_ids or left + 1 in output_ids:
                if left not in mid_ids or left + 1 not in mid_ids:
                    raise AssertionError((width, mid_ids, output_ids, left))
                for _ in range(rounds):
                    p = mean_match(p, mid_ids, left, left + 1, cache)
        p = project_distribution(p, mid_ids, output_ids)
        child_width = width // 2
        child_ids = (sorted(supports[child_width]) if child_width == 4
                     else sorted(supports[child_width][0]))
        p = mean_split(p, output_ids, child_ids)
        if abs(float(p.sum()) - 1.0) > 1e-9:
            raise ArithmeticError(f"type mass sums to {p.sum()}")
        parent_ids = child_ids
        positive = p[p > 0.0]
        print(f"width={width:>5} input/mid/output="
              f"{len(input_ids)}/{len(mid_ids)}/{len(output_ids)} "
              f"next_support={len(child_ids)} "
              f"positive_types={len(positive)} "
              f"min_positive_mass={positive.min():.3g} "
              f"max_type_mass={p.max():.6g}")

    if show_types:
        print("state_types=" + repr([
            (format(t, f"0{len(supports[4])}b"), float(mass))
            for t, mass in enumerate(p) if mass > 1e-15
        ]))
    if stopped_at_exact_suffix is not None:
        print(f"n={n} edge={edge} rounds={rounds} "
              f"typical_state_at_exact_suffix_width={stopped_at_exact_suffix} "
              "terminal_failure_not_estimated")
    elif unsafe_meanfield_tail:
        bad = terminal_bad_mass(p, sorted(supports[4]), n, edge)
        print(f"n={n} edge={edge} rounds={rounds} "
              f"unsafe_all-scales_meanfield_bad_mass={bad:.12g}")
    else:
        raise AssertionError("missing exact-suffix cutoff")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=128)
    parser.add_argument("--edge", type=int, default=None)
    parser.add_argument("--rounds", type=int, default=70)
    parser.add_argument("--min-random-width", type=int, default=200)
    parser.add_argument("--unsafe-meanfield-tail", action="store_true",
                        help="continue mean-field propagation below the exact cutoff")
    parser.add_argument("--show-types", action="store_true")
    args = parser.parse_args()
    edge = args.n // 2 - 4 if args.edge is None else args.edge
    run(args.n, edge, args.rounds, args.min_random_width,
        args.unsafe_meanfield_tail, args.show_types)


if __name__ == "__main__":
    main()
