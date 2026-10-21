#!/usr/bin/env python3
"""Finite-state discovery screen for the UB-28 interior support phases.

The phase records an interval support's length, left parity, and distances to
the two block-array boundaries capped at six. A backward scale step halves
indices, then closes the support through offsets 1 and 0. For more than 128
blocks, placements within 32 of either boundary cover all exact boundary
cases; farther inside, the transition depends only on the position modulo
four, represented around the center. Thus the finite representative rule
covers every block count, not just tested powers of two.
"""

import argparse
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_support_phase_audit", HERE / "ub28-support-phase-audit.py"
)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)
TAIL_SPEC = importlib.util.spec_from_file_location(
    "ub28_terminal_window_language", HERE / "ub28-terminal-window-language.py"
)
terminal = importlib.util.module_from_spec(TAIL_SPEC)
TAIL_SPEC.loader.exec_module(terminal)


def phase_from_interval(left, length, blocks):
    if length <= 0 or left < 0 or left + length > blocks:
        raise ValueError((left, length, blocks))
    return (tuple(range(length)), left % 2, min(left, 6),
            min(blocks - left - length, 6))


def close_interval(left, right, blocks, offset):
    """Close one interval under all pairs in a single offset matching."""
    if left > offset and left % 2 != offset:
        left -= 1
    if right + 1 < blocks and right % 2 == offset:
        right += 1
    return left, right


def check_local_closure():
    for blocks in range(1, 33):
        for first in range(blocks):
            for last in range(first, blocks):
                for offset in (0, 1):
                    expected = set(range(first, last + 1))
                    for pair_left in range(offset, blocks - 1, 2):
                        if pair_left in expected or pair_left + 1 in expected:
                            expected.update((pair_left, pair_left + 1))
                    got_left, got_right = close_interval(
                        first, last, blocks, offset
                    )
                    if expected != set(range(got_left, got_right + 1)):
                        raise AssertionError((blocks, first, last, offset,
                                              expected, got_left, got_right))


def one_scale_target(left, length, child_blocks):
    """Map a child support interval to its parent phase."""
    parent_blocks = child_blocks // 2
    first, last = left // 2, (left + length - 1) // 2
    for offset in (1, 0):
        first, last = close_interval(first, last, parent_blocks, offset)
    return phase_from_interval(first, last - first + 1, parent_blocks)


def width8_seed_phases(width4_blocks):
    """Exact support phases after the width-8 matching passes."""
    output = terminal.output_supports(width4_blocks)
    blocks = width4_blocks // 2
    seeds = set()
    for edge in range(0, 4 * width4_blocks - 1, 2):
        support = {index // 2 for index in output[edge] | output[edge + 1]}
        first, last = min(support), max(support)
        for offset in (1, 0):
            first, last = close_interval(first, last, blocks, offset)
        seeds.add(phase_from_interval(first, last - first + 1, blocks))
    return seeds


def representative_positions(blocks, length):
    """Positions covering boundary neighborhoods and interior residues."""
    last_start = blocks - length
    positions = set(range(min(last_start + 1, 32)))
    positions.update(range(max(0, last_start - 31), last_start + 1))
    middle = blocks // 2
    positions.update(range(max(0, middle - 16), min(last_start, middle + 16) + 1))
    if blocks <= 128:
        positions.update(range(last_start + 1))
    return positions


def phase_targets(source, max_log_blocks=18):
    shape, parity, left_cap, right_cap = source
    length = len(shape)
    if shape != tuple(range(length)) or not 1 <= length <= 6:
        raise ValueError(source)
    targets = set()
    for log_blocks in range(3, max_log_blocks + 1):
        blocks = 1 << log_blocks
        for left in representative_positions(blocks, length):
            if left % 2 != parity:
                continue
            if min(left, 6) != left_cap:
                continue
            if min(blocks - left - length, 6) != right_cap:
                continue
            targets.add(one_scale_target(left, length, blocks))
    return targets


def run(min_log=8, max_log=14, max_log_blocks=8):
    check_local_closure()
    observed_phases = set()
    observed_arcs = set()
    seeds = width8_seed_phases(64)
    seed_checks = all(width8_seed_phases(1 << k) == seeds
                      for k in range(6, 11))
    if not seed_checks:
        raise AssertionError("width-8 seed phases changed on 64..1024 blocks")
    for log_n in range(min_log, max_log + 1):
        by_width = audit.stages(1 << log_n)
        widths = sorted(by_width)
        for width, phases in by_width.items():
            if (1 << log_n) // width >= 4:
                observed_phases.update(phases)
        for width, next_width in zip(widths, widths[1:]):
            child_blocks = (1 << log_n) // width
            if child_blocks < 8:  # top interface is handled separately
                continue
            observed_arcs.update(zip(by_width[width], by_width[next_width]))

    missing = [(source, target) for source, target in observed_arcs
               if target not in phase_targets(source, max_log_blocks)]
    graph = {}
    pending = list(seeds)
    while pending:
        source = pending.pop()
        if source in graph:
            continue
        targets = phase_targets(source, max_log_blocks)
        graph[source] = targets
        pending.extend(target for target in targets if target not in graph)
    missing_observed = observed_phases - set(graph)
    print(f"width8_seed_phases={len(seeds)} seed_checks_64_to_1024={seed_checks} "
          f"observed_phases={len(observed_phases)} "
          f"closure_phases={len(graph)} observed_arcs={len(observed_arcs)}")
    print(f"closure_arcs={sum(map(len, graph.values()))} "
          f"period_two_bellman_states={2 * len(graph)} "
          f"phase_labeled_arcs={2 * sum(map(len, graph.values()))} "
          f"source_phases_with_multiple_targets={sum(len(v)>1 for v in graph.values())} "
          f"observed_phases_missing_from_closure={len(missing_observed)}")
    print(f"observed_arcs_missing_from_representatives={len(missing)}")
    if missing:
        print("first_missing=", missing[:5])
        raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-log", type=int, default=8)
    parser.add_argument("--max-log", type=int, default=14)
    parser.add_argument("--max-log-blocks", type=int, default=8)
    args = parser.parse_args()
    if args.max_log_blocks < 8:
        parser.error("max-log-blocks must be at least 8 (256 representatives needed)")
    run(args.min_log, args.max_log, args.max_log_blocks)
