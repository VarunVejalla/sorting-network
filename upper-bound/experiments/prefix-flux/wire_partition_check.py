#!/usr/bin/env python3
"""Check exact static-wire routing for the D2 rank-profile flow.

For each scheduled stage, an active bag's output positions are divided into
its parent up-ports and child down-ports. This verifies that those routed
wire intervals, together with unchanged inactive bags, partition each next
bag's static wire set exactly. It checks geometry only; no sorting claim.
"""
import argparse

from flow_dag import FlowDAG


def active_keys(flow, t):
    p = flow.p
    return {
        (lev, idx)
        for lev in range(flow.d + 1)
        for idx in range(p.k**lev)
        if (lev == 0 if t == 0 else p.active(flow.d, lev, t))
    }


def slice_intervals(intervals, start, stop):
    """Map a local rank slice to its ordered static-wire intervals."""
    out = []
    rank = 0
    for lo, hi in intervals:
        left, right = max(start, rank), min(stop, rank + hi - lo)
        if left < right:
            out.append((lo + left - rank, lo + right - rank))
        rank += hi - lo
    assert stop <= rank, (start, stop, rank, intervals)
    return out


def merge(intervals):
    out = []
    for lo, hi in sorted(intervals):
        if lo >= hi:
            continue
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def check(depth, scale=1):
    flow = FlowDAG(depth, scale=scale).build()
    p = flow.p
    N = p.k**depth * scale
    comparisons = 0

    for t, row in enumerate(flow.rows):
        active = active_keys(flow, t)
        next_intervals = []
        next_size = 0

        for lev in range(depth + 1):
            for idx in range(p.k**lev):
                key = (lev, idx)
                routed = []

                # Inactive bags keep their wires unchanged.
                if key not in active:
                    node = flow.lookup(t, lev, idx)
                    routed.extend(flow.bag_intervals(node, idx))

                # The parent's middle output block is routed down to this bag.
                if lev > 0:
                    parent = (lev - 1, idx // p.k)
                    if parent in active:
                        node = flow.lookup(t, *parent)
                        a, pi, blocks = row[node]
                        if pi < a:
                            h = pi // 2
                            port = idx % p.k
                            start = h + sum(blocks[:port])
                            stop = start + blocks[port]
                            routed.extend(slice_intervals(
                                flow.bag_intervals(node, idx // p.k), start, stop
                            ))

                # Each active child sends its two end ports up to this bag.
                if lev < depth:
                    for port in range(p.k):
                        child = (lev + 1, idx * p.k + port)
                        if child not in active:
                            continue
                        node = flow.lookup(t, *child)
                        a, pi, _ = row[node]
                        if pi == a:
                            ranges = [(0, a)]
                        else:
                            h = pi // 2
                            ranges = [(0, h), (a - h, a)]
                        wires = flow.bag_intervals(node, idx * p.k + port)
                        for start, stop in ranges:
                            routed.extend(slice_intervals(wires, start, stop))

                target = flow.bag_intervals(flow.lookup(t + 1, lev, idx), idx)
                # Equality of unions plus equal total length rules out both
                # missing wires and duplicate routing.
                assert merge(routed) == merge(target), (
                    depth, scale, t, key, merge(routed), merge(target)
                )
                assert sum(hi - lo for lo, hi in routed) == sum(
                    hi - lo for lo, hi in merge(routed)
                ), (depth, scale, t, key, routed)
                next_intervals.extend(target)
                next_size += sum(hi - lo for lo, hi in target)
                comparisons += 1

        assert merge(next_intervals) == [(0, N)], (depth, scale, t)
        assert next_size == N, (depth, scale, t, next_size, N)

    return len(flow.rows), comparisons, len(flow.nodes)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=8)
    parser.add_argument("--scales", type=int, nargs="+", default=[1, 2])
    args = parser.parse_args()
    for depth in range(2, args.max_depth + 1):
        for scale in args.scales:
            stages, checks, states = check(depth, scale)
            print(
                f"d={depth} scale={scale}: {stages} stages, {checks} bag checks, "
                f"{states} shared states passed"
            )
