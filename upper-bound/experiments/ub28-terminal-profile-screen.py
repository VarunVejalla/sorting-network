#!/usr/bin/env python3
"""Exhaustive SMT screen of a sufficient terminal-profile condition for UB-28.

For the deterministic cyclic h=4,2,1 tail on 32 wires, check each
nondecreasing width-4 block-count profile. A profile is universally safe when
the SMT solver finds no input arrangement with those counts that leaves an
adjacent output inversion. This is a finite diagnostic, not an all-size proof.
"""

from collections import Counter
from itertools import combinations_with_replacement

import importlib.util
from pathlib import Path

import z3


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_actual_schedule", HERE / "ub28-actual-schedule-screen.py"
)
schedule_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(schedule_module)


def main():
    n = 32
    tail = schedule_module.build(n, seed=0)[-14:]
    inputs = [z3.Bool(f"x{i}") for i in range(n)]
    wires = inputs[:]
    for layer in tail:
        after = wires[:]
        for i, j in layer:
            after[i] = z3.And(wires[i], wires[j])
            after[j] = z3.Or(wires[i], wires[j])
        wires = after

    inversion = z3.Or(
        *[z3.And(wires[i], z3.Not(wires[i + 1])) for i in range(n - 1)]
    )
    blocks = [inputs[4 * b : 4 * b + 4] for b in range(n // 4)]
    solver = z3.Solver()
    solver.add(inversion)

    by_span = Counter()
    safe_total = 0
    unsafe_total = 0
    for profile in combinations_with_replacement(range(5), n // 4):
        partial = [i for i, c in enumerate(profile) if c not in (0, 4)]
        span = partial[-1] - partial[0] + 1 if partial else 0
        solver.push()
        for block, count in zip(blocks, profile):
            solver.add(z3.PbEq([(wire, 1) for wire in block], count))
        unsafe = solver.check() == z3.sat
        solver.pop()
        by_span[(span, "unsafe" if unsafe else "safe")] += 1
        if unsafe:
            unsafe_total += 1
        else:
            safe_total += 1

    assert all(by_span[(s, "unsafe")] == 0 for s in range(4))
    assert by_span[(4, "unsafe")] > 0
    print(f"profiles={safe_total + unsafe_total}")
    print(f"universally_safe={safe_total} unsafe={unsafe_total}")
    for span in range(9):
        print(
            f"partial_span={span} safe={by_span[(span, 'safe')]} "
            f"unsafe={by_span[(span, 'unsafe')]}"
        )


if __name__ == "__main__":
    main()
