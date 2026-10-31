#!/usr/bin/env python3
"""Finite exact audit of D2 sender-port cuts against physical 4096-wire cells.

The FlowDAG represents equal subtrees by shared state, but this screen expands
sender occurrences and their ordered address runs. It verifies that each
stage's rank-port pieces partition [0,N) and reports any piece endpoint not on
the requested cell grid. This is diagnostic finite evidence, not an induction.
"""
import argparse
from flow_dag import FlowDAG
from oracle import Par


def audit(depth: int, scale: int, cell: int, params: tuple[int, int, int]):
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    n = scale * p.k ** depth
    print(f"depth={depth} stages={len(flow.rows)} N={n} cell={cell}")
    all_ok = True
    for stage, rows in enumerate(flow.rows):
        spans = []
        senders = 0
        unaligned = 0
        for level in range(depth + 1):
            active = (level == 0) if stage == 0 else p.active(depth, level, stage)
            if not active:
                continue
            for index in range(p.k ** level):
                node = flow.lookup(stage, level, index)
                if node not in rows:
                    continue
                senders += 1
                allocation, up, down = rows[node]
                ends = [0]
                for width in [up // 2, *down, up // 2]:
                    ends.append(ends[-1] + width)
                assert ends[-1] == allocation, (stage, level, index, rows[node], ends)
                rank_start = 0
                for addr_lo, addr_hi in flow.bag_intervals(node, index):
                    run_len = addr_hi - addr_lo
                    for port, (port_lo, port_hi) in enumerate(zip(ends, ends[1:])):
                        left = max(rank_start, port_lo)
                        right = min(rank_start + run_len, port_hi)
                        if left >= right:
                            continue
                        lo = addr_lo + left - rank_start
                        hi = addr_lo + right - rank_start
                        spans.append((lo, hi))
                        if lo % cell or hi % cell:
                            unaligned += 1
                    rank_start += run_len
        spans.sort()
        cursor = 0
        partition = True
        for lo, hi in spans:
            if lo != cursor:
                partition = False
                break
            cursor = hi
        partition = partition and cursor == n
        stage_ok = partition and unaligned == 0
        all_ok &= stage_ok
        print(f" stage={stage}: senders={senders} port-pieces={len(spans)} "
              f"partition={partition} unaligned-endpoints={unaligned}")
    print(f"all_stages_pass={all_ok}")
    return all_ok


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=9)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--cell", type=int, default=4096)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    args = parser.parse_args()
    raise SystemExit(0 if audit(args.depth, args.scale, args.cell, tuple(args.params)) else 1)
