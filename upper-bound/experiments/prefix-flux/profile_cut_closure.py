#!/usr/bin/env python3
"""Backward closure of profile cuts needed for ordered prefix constraints.

Seed cuts are D2 port boundaries and terminal native-block boundaries. A cut
in a bag is mapped to its static-wire coordinate; source-profile cuts needed
to express its input prefix are propagated backward through the flow.
This counts the exact finite cut system, but does not yet solve its LP.
"""
import argparse
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par


def active_bags(flow, t):
    p = flow.p
    is_initial_root_stage = t == 0 and getattr(flow, 'stage_offset', 0) == 0
    return [
        key for key in occupied_bag_keys(flow, t)
        if (key[0] == 0 if is_initial_root_stage
            else p.active(flow.d, key[0], t))
    ]


def occupied_bag_keys(flow, t):
    """Addresses with positive bag mass, found by traversing occupied subtrees.

    The full address tree has k**d leaves, but the D2 flow is sparse. A
    saturated subtree has no occupied wires and can be skipped wholesale.
    This returns exactly the addresses whose allocation is positive.
    """
    keys = []
    todo = [(flow.roots[t], 0, 0)]
    while todo:
        node, lev, idx = todo.pop()
        if flow.subtree_interval(node, idx) is None:
            continue
        if flow.allocation(node) > 0:
            keys.append((lev, idx))
        for j, child in enumerate(flow.nodes[node][4]):
            todo.append((child, lev + 1, idx * flow.p.k + j))
    return keys


def bag_intervals(flow, t, key):
    lev, idx = key
    return flow.bag_intervals(flow.lookup(t, lev, idx), idx)


def allocation(intervals):
    return sum(hi - lo for lo, hi in intervals)


def rank_before(intervals, wire_cut):
    return sum(max(0, min(hi, wire_cut) - lo) for lo, hi in intervals)


def wire_cut_at_rank(intervals, rank):
    total = 0
    for lo, hi in intervals:
        width = hi - lo
        if rank <= total + width:
            return lo + rank - total
        total += width
    assert rank == total, (rank, total, intervals)
    return intervals[-1][1] if intervals else 0


def prefix_components(intervals, wire_cut):
    """Global prefix cuts sufficient to count a bag's wires below wire_cut."""
    cuts = set()
    for lo, hi in intervals:
        right = min(hi, wire_cut)
        if lo < right:
            cuts.add(lo)
            cuts.add(right)
    return cuts


def cut_system(depth=6, scale=65536, threshold=F(1, 3), root_rows=False,
               all_row_cuts=False, row_stride=1, params=(2, 3, 2),
               row_count=1 << 12, all_global_cuts=False,
               all_root_cuts=False, root_inversion_cap=None,
               flow_override=None):
    assert row_stride > 0 and row_count % row_stride == 0
    flow = flow_override or FlowDAG(depth, scale=scale, p=Par(*params)).build()
    p = flow.p
    T = len(flow.rows)
    N = p.k**depth * scale
    global_cuts = [set((0, N)) for _ in range(T + 1)]
    if all_global_cuts or all_root_cuts:
        assert N <= (1 << 18), (N, 'all-global-cut diagnostic limit')
    if all_global_cuts:
        for cuts in global_cuts:
            cuts.update(range(N + 1))
    elif all_root_cuts:
        global_cuts[0].update(range(N + 1))
    if root_inversion_cap is not None:
        assert root_inversion_cap >= 0
        q = int(threshold * N)
        left = max(0, q - root_inversion_cap)
        right = min(N, q + root_inversion_cap + 1)
        global_cuts[0].update(range(left, right + 1))
    ycuts = [dict() for _ in range(T)]
    active = [active_bags(flow, t) for t in range(T)]
    interval_cache = {}

    def wires_at(t, key):
        cache_key = (t, key)
        if cache_key not in interval_cache:
            interval_cache[cache_key] = bag_intervals(flow, t, key)
        return interval_cache[cache_key]

    # Bag totals are actual profile integrals, so retain every static endpoint.
    support = [occupied_bag_keys(flow, t) for t in range(T + 1)]
    for t in range(T + 1):
        for key in support[t]:
            for lo, hi in wires_at(t, key):
                global_cuts[t].update((lo, hi))

    # Seed every active output profile at its exact D2 port boundaries.
    for t, keys in enumerate(active):
        row = flow.rows[t]
        for key in keys:
            node = flow.lookup(t, *key)
            a, pi, blocks = row[node]
            cuts = {0, a}
            if pi < a:
                h = pi // 2
                cuts.add(h)
                pos = h
                for width in blocks:
                    pos += width
                    cuts.add(pos)
                if all_row_cuts and a:
                    assert a % row_count == 0, (depth, scale, t, key, a)
                    row_width = a // row_count
                    cuts.update(i * row_width for i in range(0, row_count, row_stride))
                    cuts.add(a)
            ycuts[t][key] = cuts
            wires = wires_at(t, key)
            for cut in cuts:
                global_cuts[t + 1].add(wire_cut_at_rank(wires, cut))

    if root_rows:
        root = flow.lookup(0, 0, 0)
        root_arity = flow.allocation(root)
        assert root_arity % row_count == 0
        row_width = root_arity // row_count
        global_cuts[1].update(i * row_width for i in range(0, row_count, row_stride))
        global_cuts[1].add(root_arity)

    # Exact terminal block totals and the threshold cut are required.
    q = int(threshold * N)
    global_cuts[T].add(q)
    for key in support[T]:
        wires = wires_at(T, key)
        for lo, hi in wires:
            global_cuts[T].update((lo, hi))

    # A global cut at time t+1 needs each active source's output prefix and
    # its input prefix; input-prefix counts reduce to global counts at the
    # endpoints of the source bag's static-wire intervals.
    for t in range(T - 1, -1, -1):
        for wire_cut in tuple(global_cuts[t + 1]):
            global_cuts[t].add(wire_cut)
            for key in active[t]:
                wires = wires_at(t, key)
                cut = rank_before(wires, wire_cut)
                if 0 < cut < allocation(wires):
                    ycuts[t][key].add(cut)
                    global_cuts[t].update(prefix_components(wires, wire_cut))

        # Every selected output cut also receives prefix dominance against
        # its actual local input. Add the global endpoints needed to count it.
        for key in active[t]:
            wires = wires_at(t, key)
            for cut in tuple(ycuts[t][key]):
                wire_cut = wire_cut_at_rank(wires, cut)
                global_cuts[t + 1].add(wire_cut)
                if 0 < cut < allocation(wires):
                    global_cuts[t].update(prefix_components(wires, wire_cut))

    return flow, ycuts, global_cuts, active


def close(depth=6, scale=65536, threshold=F(1, 3), root_rows=False,
          all_row_cuts=False, row_stride=1, params=(2, 3, 2),
          row_count=1 << 12, all_global_cuts=False, all_root_cuts=False,
          root_inversion_cap=None):
    flow, ycuts, global_cuts, _ = cut_system(
        depth, scale, threshold, root_rows=root_rows,
        all_row_cuts=all_row_cuts, row_stride=row_stride,
        params=params, row_count=row_count, all_global_cuts=all_global_cuts,
        all_root_cuts=all_root_cuts, root_inversion_cap=root_inversion_cap
    )
    T = len(flow.rows)
    return dict(
        depth=depth,
        scale=scale,
        root_rows=root_rows,
        all_row_cuts=all_row_cuts,
        row_stride=row_stride,
        params=params,
        row_count=row_count,
        stages=T,
        global_cut_counts=[len(xs) for xs in global_cuts],
        output_profile_cut_counts=[
            sum(len(cuts) for cuts in stage.values()) for stage in ycuts
        ],
        max_cuts_in_one_profile=max(
            (len(cuts) for stage in ycuts for cuts in stage.values()), default=0
        ),
        total_y_profiles=sum(len(stage) for stage in ycuts),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--scale", type=int, default=65536)
    parser.add_argument("--root-rows", action="store_true")
    parser.add_argument("--all-row-cuts", action="store_true")
    parser.add_argument("--row-stride", type=int, default=1)
    parser.add_argument("--params", nargs=3, type=int, default=(2, 3, 2),
                        metavar=("X", "Y", "Z"))
    parser.add_argument("--row-bits", type=int, default=12)
    args = parser.parse_args()
    print("ORDERED PROFILE CUT CLOSURE; diagnostic only")
    print(close(args.depth, args.scale, root_rows=args.root_rows,
                all_row_cuts=args.all_row_cuts, row_stride=args.row_stride,
                params=tuple(args.params), row_count=1 << args.row_bits))
