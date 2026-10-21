#!/usr/bin/env python3
"""Enumerate finite support/alignment phases for UB-28 bad even edges.

This follows each exact tail edge support backward through splits and both
matching offsets. It checks the six-coordinate locality bound and reports the
finite support-shape/alignment/boundary phases and observed scale transitions.
Finite powers-of-two are a phase-graph discovery audit, not a proof that the
reported transition graph covers every size.
"""

import argparse
import importlib.util
from collections import defaultdict
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_terminal_window_language", HERE / "ub28-terminal-window-language.py"
)
terminal = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(terminal)


def close_under_pairs(supports, blocks, offset):
    closed = []
    for support in supports:
        result = set(support)
        for left in range(offset, blocks - 1, 2):
            if left in result or left + 1 in result:
                result.update((left, left + 1))
        closed.append(result)
    return closed


def phase(support, blocks):
    ordered = tuple(sorted(support))
    if ordered != tuple(range(ordered[0], ordered[-1] + 1)):
        raise AssertionError(f"noncontiguous support: {ordered}")
    left, right = ordered[0], blocks - 1 - ordered[-1]
    return (
        tuple(index - left for index in ordered),
        left % 2,
        min(left, 6),
        min(right, 6),
    )


def stages(n):
    width4_blocks = n // 4
    tail_supports = terminal.output_supports(width4_blocks)
    supports = [
        tail_supports[edge] | tail_supports[edge + 1]
        for edge in range(0, n - 1, 2)
    ]
    blocks = width4_blocks // 2
    supports = [{index // 2 for index in support} for support in supports]
    width = 8
    result = {}
    while True:
        supports = close_under_pairs(supports, blocks, 1)
        supports = close_under_pairs(supports, blocks, 0)
        if max(map(len, supports)) > 6:
            raise AssertionError((n, width, max(map(len, supports))))
        result[width] = [phase(support, blocks) for support in supports]
        if blocks == 2:
            return result
        blocks //= 2
        supports = [{index // 2 for index in support} for support in supports]
        width *= 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-log", type=int, default=8)
    parser.add_argument("--max-log", type=int, default=12)
    args = parser.parse_args()
    if args.min_log < 5 or args.max_log < args.min_log:
        raise ValueError("require 5 <= min-log <= max-log")

    all_phases = defaultdict(set)
    all_transitions = defaultdict(set)
    for log_n in range(args.min_log, args.max_log + 1):
        n = 1 << log_n
        by_width = stages(n)
        print(f"n={n}")
        for width, edge_phases in by_width.items():
            unique = set(edge_phases)
            all_phases[width].update(unique)
            print(
                f"  width={width} phases={len(unique)} "
                f"max_support={max(len(p[0]) for p in unique)}"
            )
        widths = sorted(by_width)
        for width, next_width in zip(widths, widths[1:]):
            for source, target in zip(by_width[width], by_width[next_width]):
                all_transitions[(width, source)].add(target)

    print("union across tested sizes:")
    for width in sorted(all_phases):
        print(f"  width={width} phases={len(all_phases[width])}")
    multi = sum(len(targets) > 1 for targets in all_transitions.values())
    print(
        f"observed_transition_arcs={sum(map(len, all_transitions.values()))} "
        f"source_phases_with_multiple_targets={multi}"
    )


if __name__ == "__main__":
    main()
