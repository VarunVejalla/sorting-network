#!/usr/bin/env python3
"""Exact stage-labelled ancestry screen for the D2 physical-tile routing DAG.

Unlike receiver_ancestor_screen.py, this does not collapse a tile identity
that reappears at different stages. It reports both the maximum live
footprint after each backward transition and the maximum total number of
tile-stage visits in any terminal tile's dependency cone. The audit is still
finite diagnostic evidence, not an all-depth theorem.
"""
from collections import defaultdict
import argparse

from flow_dag import FlowDAG
from oracle import Par
from receiver_fiber_screen import owner_runs


def source_map(source, target):
    incoming = defaultdict(set)
    i = j = 0
    while i < len(source) and j < len(target):
        slo, shi, skey = source[i]
        tlo, thi, tkey = target[j]
        if max(slo, tlo) < min(shi, thi):
            incoming[tkey].add(skey)
        end = min(shi, thi)
        if end == shi:
            i += 1
        if end == thi:
            j += 1
    assert i == len(source) and j == len(target)
    return incoming


def screen(depth, scale, params):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    maps = []
    for t in range(len(flow.rows)):
        maps.append(source_map(owner_runs(flow, t), owner_runs(flow, t + 1)))
    terminals = set(x[2] for x in owner_runs(flow, len(flow.rows)))
    max_live = [0] * (len(maps) + 1)
    max_live[0] = len(terminals)
    max_total_visits = 0
    for terminal in terminals:
        current = {terminal}
        total_visits = len(current)  # include the terminal stage itself
        for t in range(len(maps) - 1, -1, -1):
            previous = set()
            for dest in current:
                previous.update(maps[t].get(dest, ()))
            current = previous
            total_visits += len(current)  # stage label is implicit in this step
            max_live[len(maps) - t] = max(max_live[len(maps) - t], len(current))
        max_total_visits = max(max_total_visits, total_visits)
    return len(flow.rows), len(flow.nodes), len(terminals), max_live, max_total_visits


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depths', nargs='+', type=int, default=[5, 6, 7])
    ap.add_argument('--scale', type=int, default=8192)
    ap.add_argument('--params', nargs=3, type=int, default=(3, 3, 2))
    args = ap.parse_args()
    for d in args.depths:
        stages, nodes, tiles, live, visits = screen(d, args.scale, args.params)
        print(f'd={d}: stages={stages}, DAG nodes={nodes}, terminal tiles={tiles}')
        print(f'max stage-labelled live footprint by backward transitions: {live}')
        print(f'max total tile-stage visits in a terminal cone: {visits}', flush=True)
