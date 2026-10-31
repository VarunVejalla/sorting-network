#!/usr/bin/env python3
"""Check exact static-wire routing for the D2 rank-profile flow.

For each scheduled stage, an active bag's output positions are divided into
its parent up-ports and child down-ports. This verifies that those routed
wire intervals, together with unchanged inactive bags, partition each next
bag's static wire set exactly. It checks geometry only; no sorting claim.
"""
import argparse

from flow_dag import FlowDAG
from oracle import Par


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


def check(depth, scale=1, p=None, sparse_bottom=False):
    flow = FlowDAG(depth, scale=scale, p=p,
                   sparse_bottom=sparse_bottom).build()
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


def reachable_by_level(flow, root):
    """One representative static index for each reachable shared state."""
    levels = [{root: 0}]
    for _ in range(flow.d):
        children = {}
        for node, idx in levels[-1].items():
            for j, child in enumerate(flow.nodes[node][4]):
                children.setdefault(child, idx * flow.p.k + j)
        levels.append(children)
    return levels


def check_compressed(depth, scale=1, p=None, sparse_bottom=False):
    """Check exact local routing patterns modulo static-index translation.

    A bag interval at index ``i`` is its index-zero interval translated by
    ``i * native(level)``. Rank slicing commutes with that translation. Thus
    one representative occurrence of each shared state and child slot covers
    every occurrence.
    """
    flow = FlowDAG(depth, scale=scale, p=p,
                   sparse_bottom=sparse_bottom).build()
    contexts = 0
    for t in range(len(flow.rows)):
        states = reachable_by_level(flow, flow.roots[t])
        # The root has no incoming parent port.
        root = flow.roots[t]
        routed = []
        lev, _, _, _, children = flow.nodes[root]
        active = (lev == 0) if t == 0 else flow.p.active(flow.d, lev, t)
        if not active:
            routed.extend(flow.bag_intervals(root, 0))
        for j, child in enumerate(children):
            if flow.nodes[child][0] < flow.d and child in flow.rows[t]:
                a, pi, _ = flow.rows[t][child]
                wires = flow.bag_intervals(child, j)
                ranges = [(0, a)] if pi == a else [(0, pi // 2),
                                                      (a - pi // 2, a)]
                for start, stop in ranges:
                    routed.extend(slice_intervals(wires, start, stop))
        target = flow.bag_intervals(flow.lookup(t + 1, 0, 0), 0)
        assert merge(routed) == merge(target), (depth, scale, t, "root",
                                                merge(routed), merge(target))
        assert sum(b - a for a, b in routed) == sum(
            b - a for a, b in merge(routed)
        ), (depth, scale, t, "root duplicate")
        contexts += 1

        for lev in range(1, depth + 1):
            for parent, parent_idx in states[lev - 1].items():
                for port, node in enumerate(flow.nodes[parent][4]):
                    idx = parent_idx * flow.p.k + port
                    routed = []
                    active = flow.p.active(flow.d, lev, t) if t else False
                    if not active:
                        routed.extend(flow.bag_intervals(node, idx))

                    if parent in flow.rows[t]:
                        a, pi, blocks = flow.rows[t][parent]
                        if pi < a:
                            h = pi // 2
                            start = h + sum(blocks[:port])
                            stop = start + blocks[port]
                            routed.extend(slice_intervals(
                                flow.bag_intervals(parent, parent_idx), start, stop
                            ))

                    for j, child in enumerate(flow.nodes[node][4]):
                        if flow.nodes[child][0] >= depth or child not in flow.rows[t]:
                            continue
                        a, pi, _ = flow.rows[t][child]
                        wires = flow.bag_intervals(child, idx * flow.p.k + j)
                        h = pi // 2
                        ranges = [(0, a)] if pi == a else [(0, h), (a - h, a)]
                        for start, stop in ranges:
                            routed.extend(slice_intervals(wires, start, stop))

                    target = flow.bag_intervals(
                        flow.lookup(t + 1, lev, idx), idx
                    )
                    assert merge(routed) == merge(target), (
                        depth, scale, t, lev, parent, port,
                        merge(routed), merge(target)
                    )
                    assert sum(b - a for a, b in routed) == sum(
                        b - a for a, b in merge(routed)
                    ), (depth, scale, t, lev, parent, port,
                        "duplicate routing")
                    contexts += 1
    return len(flow.rows), contexts, len(flow.nodes)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=8)
    parser.add_argument("--depths", type=int, nargs="+",
                        help="check only these depths (avoids rebuilding all smaller depths)")
    parser.add_argument("--scales", type=int, nargs="+", default=[1, 2])
    parser.add_argument("--params", type=int, nargs=3, default=(2, 3, 2))
    parser.add_argument("--sparse-bottom", action="store_true")
    parser.add_argument("--compressed", action="store_true",
                        help="check exact routing modulo static-index translation")
    args = parser.parse_args()
    depths = args.depths if args.depths is not None else range(2, args.max_depth + 1)
    for depth in depths:
        if depth < 2:
            parser.error("depths must be at least 2")
        for scale in args.scales:
            checker = check_compressed if args.compressed else check
            stages, checks, states = checker(
                depth, scale, Par(*args.params), args.sparse_bottom
            )
            print(
                f"d={depth} scale={scale}: {stages} stages, {checks} routing cases, "
                f"{states} shared states passed"
            )
