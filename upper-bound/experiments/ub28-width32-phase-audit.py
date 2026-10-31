#!/usr/bin/env python3
"""Audit finite support phases for the width-32 terminal boundary event.

This checks the interval-support abstraction used by the width-32 tail screen.
It is a discovery/coverage audit, not a Lean proof of the representative rule.
"""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_phase_closure", HERE / "ub28-phase-closure.py"
)
phase = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(phase)


def reachable_graph(max_log_blocks):
    initial = set()
    for log_blocks in range(3, max_log_blocks + 1):
        blocks = 1 << log_blocks
        for edge in phase.representative_positions(blocks, 2):
            initial.add(phase.phase_from_interval(edge, 2, blocks))

    states = set(initial)
    arcs = set()
    todo = list(initial)
    while todo:
        source = todo.pop()
        for target in phase.phase_targets(
            source, max_log_blocks=max_log_blocks
        ):
            arcs.add((source, target))
            if target not in states:
                states.add(target)
                todo.append(target)
    return initial, states, arcs


def verify_representative_positions():
    # For these manageable widths, compare the representative policy with an
    # exhaustive enumeration of every possible boundary.
    for blocks in range(2, 2049):
        representative_keys = {
            phase.phase_from_interval(edge, 2, blocks)
            for edge in phase.representative_positions(blocks, 2)
        }
        exhaustive_keys = {
            phase.phase_from_interval(edge, 2, blocks)
            for edge in range(blocks - 1)
        }
        if representative_keys != exhaustive_keys:
            raise AssertionError((blocks, representative_keys ^ exhaustive_keys))

    # Exercise the separate large-scale regime used by the all-scale argument:
    # near-boundary distances below 32 are represented exactly, while interior
    # placements are represented by their parity-compatible residues mod 4.
    for log_blocks in range(8, 19):
        blocks = 1 << log_blocks
        for length in range(1, 7):
            reps_by_phase = {}
            for edge in phase.representative_positions(blocks, length):
                source = phase.phase_from_interval(edge, length, blocks)
                reps_by_phase.setdefault(source, set()).add(edge)
            exact_targets = {}
            for edge in range(blocks - length + 1):
                source = phase.phase_from_interval(edge, length, blocks)
                first, last = edge // 2, (edge + length - 1) // 2
                parent_blocks = blocks // 2
                for offset in (1, 0):
                    first, last = phase.close_interval(
                        first, last, parent_blocks, offset
                    )
                target = phase.phase_from_interval(
                    first, last - first + 1, parent_blocks
                )
                exact_targets.setdefault(source, set()).add(target)
            for source, targets in exact_targets.items():
                representative_targets = set()
                for edge in reps_by_phase.get(source, ()):
                    first, last = edge // 2, (edge + length - 1) // 2
                    parent_blocks = blocks // 2
                    for offset in (1, 0):
                        first, last = phase.close_interval(
                            first, last, parent_blocks, offset
                        )
                    representative_targets.add(phase.phase_from_interval(
                        first, last - first + 1, parent_blocks
                    ))
                if representative_targets != targets:
                    raise AssertionError(
                        (blocks, length, source,
                         representative_targets ^ targets)
                    )


def main():
    phase.check_local_closure()
    verify_representative_positions()
    baseline = None
    for max_log_blocks in (24, 32, 48, 64, 96, 128):
        initial, states, arcs = reachable_graph(max_log_blocks)
        summary = (initial, states, arcs)
        if baseline is None:
            baseline = summary
        elif summary != baseline:
            raise AssertionError(
                f"phase graph changed by horizon {max_log_blocks}"
            )
        print(
            f"horizon={max_log_blocks} initial={len(initial)} "
            f"reachable={len(states)} arcs={len(arcs)} "
            f"max_support={max(len(s[0]) for s in states)}"
        )


if __name__ == "__main__":
    main()
