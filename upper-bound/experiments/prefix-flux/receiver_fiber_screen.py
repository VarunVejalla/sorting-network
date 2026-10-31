#!/usr/bin/env python3
"""Finite screen of physical-tile fan-in under exact D2 static-wire routing.

For each stage, map each aligned 4096-wire cell of a current sender's ordered
address set to its local 4096x64 tile, then locate that same static cell in its
next-stage sender/tile.  Report how many distinct source tiles feed a receiver
tile.  This is a geometry diagnostic, not an all-depth proof or a key-count
bound.
"""
from collections import defaultdict
import argparse

from flow_dag import FlowDAG
from oracle import Par


CELL = 4096
TILE = CELL * 64


def owner_runs(flow, stage):
    """Return aligned static-cell intervals with one local source-tile owner."""
    result = []
    for level in range(flow.d + 1):
        for index in range(flow.p.k ** level):
            node = flow.lookup(stage, level, index)
            rank = 0
            for lo, hi in flow.bag_intervals(node, index):
                assert lo % CELL == hi % CELL == 0, (stage, level, index, lo, hi)
                cell, stop = lo // CELL, hi // CELL
                while cell < stop:
                    local_cell = rank // CELL
                    tile = local_cell // 64
                    take = min(stop - cell, 64 - local_cell % 64)
                    result.append((cell, cell + take, (level, index, tile)))
                    cell += take
                    rank += take * CELL
    result.sort()
    expected = (flow.p.k ** flow.d * flow.scale) // CELL
    assert result and result[0][0] == 0 and result[-1][1] == expected
    assert all(a[1] == b[0] for a, b in zip(result, result[1:])), (stage, result[:4])
    return result


def transition_fibers(source, target):
    """Overlay source/target owner runs and count distinct tile incidences."""
    incoming, outgoing = defaultdict(set), defaultdict(set)
    i = j = 0
    while i < len(source) and j < len(target):
        slo, shi, skey = source[i]
        tlo, thi, tkey = target[j]
        assert max(slo, tlo) < min(shi, thi), (source[i], target[j])
        incoming[tkey].add(skey)
        outgoing[skey].add(tkey)
        end = min(shi, thi)
        if end == shi:
            i += 1
        if end == thi:
            j += 1
    assert i == len(source) and j == len(target)
    return (max(map(len, incoming.values()), default=0),
            max(map(len, outgoing.values()), default=0))


def check(depth, scale, params):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    max_in = max_out = 0
    maxima = []
    for t in range(len(flow.rows)):
        src, dst = owner_runs(flow, t), owner_runs(flow, t + 1)
        mi, mo = transition_fibers(src, dst)
        max_in, max_out = max(max_in, mi), max(max_out, mo)
        maxima.append((t, mi, mo))
    return len(flow.rows), len(flow.nodes), max_in, max_out, maxima


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depths', nargs='+', type=int, default=[3, 4])
    ap.add_argument('--scale', type=int, default=8192)
    ap.add_argument('--params', nargs=3, type=int, default=(3, 3, 2))
    args = ap.parse_args()
    for d in args.depths:
        stages, states, max_in, max_out, maxima = check(d, args.scale, args.params)
        print(f'd={d} scale={args.scale}: stages={stages} states={states} '
              f'max_source_tiles_per_receiver={max_in} '
              f'max_receiver_tiles_per_source={max_out}')
        print('per-stage (stage, max incoming, max outgoing):', maxima)
