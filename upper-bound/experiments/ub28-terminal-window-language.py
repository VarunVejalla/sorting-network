#!/usr/bin/env python3
"""Extract the exact local forbidden-window language for UB-28's exact tail.

Each final adjacent output pair depends on at most six incoming width-4
block counts. The support propagation below follows the exact count map in
ub28-terminal-count-gate.py. We enumerate each resulting local truth table,
then verify that translated edges with the same phase/support signature have
the same table. This reduces the exact tail gate to finitely many forbidden
count windows; it does not bound how often the randomized prefix produces
those windows.
"""

from collections import defaultdict
from itertools import product
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_terminal_count_gate", HERE / "ub28-terminal-count-gate.py"
)
tail_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tail_module)


def support_pass(supports, offset):
    result = [set(s) for s in supports]
    for i in range(offset, len(supports) - 1, 2):
        merged = supports[i] | supports[i + 1]
        result[i] = merged
        result[i + 1] = merged
    return result


def output_supports(blocks):
    supports = [{i} for i in range(blocks)]
    supports = support_pass(support_pass(supports, 0), 1)
    supports = [s for parent in supports for s in (parent, parent)]
    supports = support_pass(support_pass(supports, 0), 1)
    supports = [s for parent in supports for s in (parent, parent)]
    return support_pass(support_pass(supports, 0), 1)


def signature(edge, support):
    lo = min(support)
    return edge % 4, (edge // 4) % 4, tuple(i - lo for i in sorted(support))


def edge_is_bad(profile, edge):
    out = tail_module.tail_output(profile)
    return out[edge] > out[edge + 1]


def main():
    blocks = 12
    supports = output_supports(blocks)
    grouped = defaultdict(list)
    for edge in range(4 * blocks - 1):
        support = supports[edge] | supports[edge + 1]
        offsets = tuple(sorted(support))
        assert len(offsets) <= 6
        assert offsets == tuple(range(offsets[0], offsets[-1] + 1))
        grouped[signature(edge, support)].append((edge, offsets))

    print(f"blocks={blocks} edges={4 * blocks - 1} signatures={len(grouped)}")
    print(f"max_input_blocks_per_edge={max(len(s) for s in (a | b for a,b in zip(supports, supports[1:])))}")
    for sig, occurrences in sorted(grouped.items()):
        edge0, positions0 = occurrences[0]
        width = len(positions0)
        table = set()
        for values in product(range(5), repeat=width):
            profile = [0] * blocks
            for pos, value in zip(positions0, values):
                profile[pos] = value
            if edge_is_bad(profile, edge0):
                table.add(values)

        # Check exact translation invariance for every edge sharing this
        # periodic phase and support shape.
        for edge, positions in occurrences[1:]:
            for values in product(range(5), repeat=width):
                profile = [0] * blocks
                for pos, value in zip(positions, values):
                    profile[pos] = value
                if edge_is_bad(profile, edge) != (values in table):
                    raise AssertionError((sig, edge, values))
        print(
            f"phase={sig[:2]} support={sig[2]} occurrences={len(occurrences)} "
            f"forbidden={len(table)}/{5**width}"
        )


if __name__ == "__main__":
    main()
