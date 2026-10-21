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


def active_bags(flow, t):
    p = flow.p
    return [
        (lev, idx)
        for lev in range(flow.d + 1)
        for idx in range(p.k**lev)
        if (lev == 0 if t == 0 else p.active(flow.d, lev, t))
    ]


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
               all_row_cuts=False, row_stride=1):
    assert row_stride > 0 and 4096 % row_stride == 0
    flow = FlowDAG(depth, scale=scale).build()
    p = flow.p
    T = len(flow.rows)
    N = p.k**depth * scale
    ycuts = [dict() for _ in range(T)]
    global_cuts = [set((0, N)) for _ in range(T + 1)]
    active = [active_bags(flow, t) for t in range(T)]
    interval_cache = {}

    def wires_at(t, key):
        cache_key = (t, key)
        if cache_key not in interval_cache:
            interval_cache[cache_key] = bag_intervals(flow, t, key)
        return interval_cache[cache_key]

    # Bag totals are actual profile integrals, so retain every static endpoint.
    for t in range(T + 1):
        for lev in range(depth + 1):
            for idx in range(p.k**lev):
                for lo, hi in wires_at(t, (lev, idx)):
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
                    assert a % 4096 == 0, (depth, scale, t, key, a)
                    row_width = a // 4096
                    cuts.update(i * row_width for i in range(0, 4096, row_stride))
                    cuts.add(a)
            ycuts[t][key] = cuts
            wires = wires_at(t, key)
            for cut in cuts:
                global_cuts[t + 1].add(wire_cut_at_rank(wires, cut))

    if root_rows:
        root = flow.lookup(0, 0, 0)
        root_arity = flow.allocation(root)
        assert root_arity % 4096 == 0
        row_width = root_arity // 4096
        global_cuts[1].update(i * row_width for i in range(0, 4096, row_stride))
        global_cuts[1].add(root_arity)

    # Exact terminal block totals and the threshold cut are required.
    q = int(threshold * N)
    global_cuts[T].add(q)
    for lev in range(depth + 1):
        for idx in range(p.k**lev):
            wires = wires_at(T, (lev, idx))
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
          all_row_cuts=False, row_stride=1):
    flow, ycuts, global_cuts, _ = cut_system(
        depth, scale, threshold, root_rows=root_rows,
        all_row_cuts=all_row_cuts, row_stride=row_stride
    )
    T = len(flow.rows)
    return dict(
        depth=depth,
        scale=scale,
        root_rows=root_rows,
        all_row_cuts=all_row_cuts,
        row_stride=row_stride,
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
    args = parser.parse_args()
    print("ORDERED PROFILE CUT CLOSURE; diagnostic only")
    print(close(args.depth, args.scale, root_rows=args.root_rows,
                all_row_cuts=args.all_row_cuts, row_stride=args.row_stride))
