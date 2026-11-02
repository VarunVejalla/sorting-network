#!/usr/bin/env python3
"""Exact address-cut throughput of the tile-scatter D2 stage network.

A comparator changes the false count of the address prefix [0,m) only if it
joins a wire below m to a wire at or above m. Consecutive sender-rank tiles
are address-ordered, so a sender has at most one tile straddling m, and that
tile moves at most min(u, T-u) keys across m when u of its T wires lie below.

This script computes that bound at the midpoint m = n/2 from the exact FlowDAG
bags, and checks that every active non-root bag stays inside its native
interval. Finite model evidence: the bags are the static bags, and their
equality with routed sets is what wire_partition_check.py audits.

    python d2_cut_crossing_gate.py --depths 7 8 10 20 40 100
"""
import argparse
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par

TILE = 262144


def wires_below(runs, cut):
    return sum(max(0, min(hi, cut) - lo) for lo, hi in runs)


def gate(depth, scale, params, sparse_bottom=False):
    flow = FlowDAG(depth, scale, Par(*params),
                   sparse_bottom=sparse_bottom).build()
    n = scale * 8 ** depth
    mid = n // 2
    crossing = root_stages = root_mass_after_start = checked = 0
    start_crossing = None
    for t, rows in enumerate(flow.rows):
        for node in rows:
            level = flow.nodes[node][0]
            native = flow.native(level)
            for lo, hi in flow.bag_intervals(node, 0):
                assert 0 <= lo <= hi <= native, (t, level, lo, hi, native)
            checked += 1
        root = flow.roots[t]
        if root not in rows:
            continue
        runs = flow.bag_intervals(root, 0)
        offset = wires_below(runs, mid) % TILE
        moved = min(offset, TILE - offset) if offset else 0
        if t == 0:
            start_crossing = moved
        else:
            root_stages += 1
            root_mass_after_start += rows[root][0]
        crossing += moved
    return (depth, flow.p.tf(depth), n, checked, start_crossing, root_stages,
            root_mass_after_start, crossing, mid)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depths', type=int, nargs='+',
                    default=[7, 8, 10, 20, 40, 100])
    ap.add_argument('--scale', type=int, default=8192)
    ap.add_argument('--params', type=int, nargs=3, default=[3, 3, 2])
    ap.add_argument('--sparse-bottom', action='store_true')
    args = ap.parse_args()
    print('d tf log2n active_states t0_crossing root_stages '
          'root_mass/n crossing_bound/needed')
    for row in (gate(d, args.scale, args.params, args.sparse_bottom)
                for d in args.depths):
        d, tf, n, checked, start, stages, mass, crossing, needed = row
        print(d, tf, n.bit_length() - 1, checked, start, stages,
              f'{float(Fraction(mass, n)):.6f}',
              f'{crossing}/2^{needed.bit_length() - 1}')


if __name__ == '__main__':
    main()
