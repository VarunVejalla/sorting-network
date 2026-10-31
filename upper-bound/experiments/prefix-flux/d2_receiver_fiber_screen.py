#!/usr/bin/env python3
"""Measure static-flow contributors per receiver bag and fixed core tile.

This is an exact finite address audit, not a proof of a uniform fiber bound.
Each contributor is one source bag/port whose routed wire interval meets the
receiver. Splitting the receiver at 262144-wire fixed-core tile boundaries
tests the finer grouping needed by the conditional Lean seam lemma.
"""
from __future__ import annotations

import argparse
from collections import defaultdict

from flow_dag import FlowDAG
from oracle import Par


def slice_intervals(intervals, start, stop):
    out = []
    rank = 0
    for lo, hi in intervals:
        left, right = max(start, rank), min(stop, rank + hi - lo)
        if left < right:
            out.append((lo + left - rank, lo + right - rank))
        rank += hi - lo
    assert stop <= rank, (start, stop, rank, intervals)
    return out


def add_contributor(fibers, intervals, source, port, tile_width):
    for lo, hi in intervals:
        for tile in range(lo // tile_width, (hi - 1) // tile_width + 1):
            fibers[tile].add((source, port))


def audit(depth, scale, params, tile_width):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    p = flow.p
    maximum_bag, maximum_tile = (0, None), (0, None)

    for t, row in enumerate(flow.rows):
        active = {
            (lev, idx)
            for lev in range(depth + 1)
            for idx in range(p.k**lev)
            if (lev == 0 if t == 0 else p.active(depth, lev, t))
        }
        for lev in range(depth + 1):
            for idx in range(p.k**lev):
                key = (lev, idx)
                fibers = defaultdict(set)

                if key not in active:
                    node = flow.lookup(t, *key)
                    add_contributor(fibers, flow.bag_intervals(node, idx),
                                    key, "stay", tile_width)

                if lev > 0:
                    parent = (lev - 1, idx // p.k)
                    if parent in active:
                        node = flow.lookup(t, *parent)
                        allocation, quota, blocks = row[node]
                        if quota < allocation:
                            port = idx % p.k
                            half = quota // 2
                            start = half + sum(blocks[:port])
                            stop = start + blocks[port]
                            intervals = slice_intervals(
                                flow.bag_intervals(node, idx // p.k), start, stop
                            )
                            add_contributor(fibers, intervals, parent,
                                            ("down", port), tile_width)

                if lev < depth:
                    for port in range(p.k):
                        child = (lev + 1, idx * p.k + port)
                        if child not in active:
                            continue
                        node = flow.lookup(t, *child)
                        allocation, quota, _ = row[node]
                        half = quota // 2
                        ranges = ([(0, allocation)] if quota == allocation else
                                  [(0, half), (allocation - half, allocation)])
                        wires = flow.bag_intervals(node, idx * p.k + port)
                        for side, (start, stop) in enumerate(ranges):
                            intervals = slice_intervals(wires, start, stop)
                            add_contributor(fibers, intervals, child,
                                            ("up", port, side), tile_width)

                bag_size = sum(map(len, fibers.values()))
                if bag_size > maximum_bag[0]:
                    maximum_bag = (bag_size, (t, key))
                for tile, contributors in fibers.items():
                    if len(contributors) > maximum_tile[0]:
                        maximum_tile = (len(contributors), (t, key, tile))

    wires = p.k**depth * scale
    return wires // tile_width, maximum_bag, maximum_tile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, nargs="+", default=[4, 5, 6, 7])
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    parser.add_argument("--tile-width", type=int, default=262144)
    args = parser.parse_args()
    for depth in args.depths:
        tiles, bag, tile = audit(depth, args.scale, args.params,
                                 args.tile_width)
        print(f"d={depth} tiles={tiles}: max bag fiber={bag}; "
              f"max bag/core-tile fiber={tile}", flush=True)


if __name__ == "__main__":
    main()
