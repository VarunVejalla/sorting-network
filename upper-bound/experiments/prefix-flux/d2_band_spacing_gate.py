#!/usr/bin/env python3
"""Exact finite check that scheduled D2 child intervals leave room for bands.

This checks only the abstract sparse-bottom flow's contiguous output blocks.
It is not a proof that the physical D2 wiring realizes those intervals or
that the band repair preserves the global rank invariant.
"""
import argparse

from flow_dag import FlowDAG
from oracle import Par


def check(depth: int, scale: int, width: int, radius: int) -> None:
    flow = FlowDAG(depth, scale=scale, p=Par(3, 2, 2),
                   sparse_bottom=True).build()
    active = unsaturated = zero_blocks = 0
    minimum = None
    off_lattice = 0
    witness = None
    for t, row in enumerate(flow.rows):
        for node, (a, pi, blocks) in row.items():
            level = flow.nodes[node][0]
            role = Par(3, 2, 2).role(depth, level, t)
            if role not in {"topRise", "mid", "botDesc"} or not a:
                continue
            active += 1
            if pi >= a:
                continue
            unsaturated += 1
            zero_blocks += sum(b == 0 for b in blocks)
            for child, block in enumerate(blocks):
                if block <= 0:
                    continue
                if block % scale:
                    off_lattice += 1
                if minimum is None or block < minimum:
                    minimum = block
                    witness = (t, level, role, a, pi, child, tuple(blocks))

    if minimum is None:
        raise RuntimeError("no positive unsaturated child block found")
    if off_lattice:
        raise AssertionError(("positive blocks off scale lattice", off_lattice))
    if scale % width:
        raise AssertionError(("flow scale is not an integer number of tile rows",
                              scale, width))
    if minimum % width:
        raise AssertionError(("minimum block is not row-aligned", minimum, width))
    gap_rows = minimum // width
    print(f"depth={depth} scale={scale} active={active} unsaturated={unsaturated} "
          f"zero_blocks={zero_blocks}")
    print(f"positive_blocks_off_scale_lattice={off_lattice}")
    print(f"minimum_positive_block={minimum} wires = {gap_rows} rows; "
          f"required_gap={2 * radius}; pass={gap_rows >= 2 * radius}")
    print(f"witness={witness}")
    if gap_rows < 2 * radius:
        raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", nargs="+", type=int, default=[25, 50, 100])
    parser.add_argument("--scale", type=int, default=4096)
    parser.add_argument("--width", type=int, default=64,
                        help="wires per physical row in the tiled core")
    parser.add_argument("--radius", type=int, default=28)
    args = parser.parse_args()
    for depth in args.depths:
        check(depth, args.scale, args.width, args.radius)
