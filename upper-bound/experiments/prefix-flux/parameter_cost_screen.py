#!/usr/bin/env python3
"""Conditional UB-42 D2 parameter/cost screen; not a sorting proof.

The candidate row height uses q=x+y+z+5 as a scaling heuristic. D2's
non-uniform flow is audited directly at a finite depth; no closed all-depth
fringe lower bound is claimed. The script reports the asymptotic stage/core
coefficient and exact finite flow integrality and fringe-row counts.
"""
from fractions import Fraction
import argparse

from flow_dag import FlowDAG
from oracle import Par


def bitonic_depth(bits):
    return bits * (bits + 1) // 2


def row_bits_for_fringe(x, y, z):
    if x < 2 or y <= z:
        raise ValueError("require k>=4 and A*nu>1")
    # Candidate scaling, validated only by the exact finite-flow audit below.
    return x + y + z + 5


def screen(x, y, z, depth):
    q = row_bits_for_fringe(x, y, z)
    row_count = 1 << q
    local_depth = 3 * bitonic_depth(q)
    stage_rate = Fraction(x + y, x * z)
    coefficient = local_depth * stage_rate

    p = Par(x, y, z)
    flow = FlowDAG(depth, scale=row_count, p=p).build()
    fringe_rows = []
    for t, row in enumerate(flow.rows):
        for node, (a, pi, _) in row.items():
            if not pi or not a:
                continue
            lev, deficit, low_deficit, high_deficit, _ = flow.nodes[node]
            fringe_rows.append((Fraction(row_count * pi, 2 * a), t, lev,
                                a, pi, deficit, low_deficit, high_deficit))
    if not fringe_rows:
        raise ValueError("no positive sender in finite flow")
    if any(pi % 2 for row in flow.rows
           for _, pi, _ in row.values()):
        raise AssertionError("odd up-port count")
    if any(a % row_count for row in flow.rows
           for a, _, _ in row.values()):
        raise AssertionError("sender arity not divisible by row count")

    seen = set()
    pending = [flow.roots[-1]]
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        pending.extend(flow.nodes[node][4])
    terminal_sizes = [flow.native(flow.nodes[node][0]) for node in seen
                      if flow.allocation(node) > 0]
    minimum = min(fringe_rows)
    return dict(x=x, y=y, z=z, row_bits=q, row_count=row_count,
                local_depth=local_depth, stage_rate=stage_rate,
                coefficient=coefficient, finite_depth=depth,
                finite_stages=len(flow.rows), states=len(flow.nodes),
                min_fringe_rows=minimum[0],
                min_sender=dict(time=minimum[1], level=minimum[2],
                                allocation=minimum[3], up=minimum[4],
                                deficit=minimum[5], low_deficit=minimum[6],
                                high_deficit=minimum[7]),
                max_terminal_bits=max(terminal_sizes).bit_length() - 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=30)
    ap.add_argument("--params", nargs=3, type=int, action="append",
                    metavar=("X", "Y", "Z"))
    args = ap.parse_args()
    params = args.params or [(2, 3, 2), (3, 3, 2), (4, 4, 3)]
    print("Conditional cost model; local tail/global recurrence unproved")
    for x, y, z in params:
        r = screen(x, y, z, args.depth)
        print(f"{(x,y,z)} rows=2^{r['row_bits']} core={r['local_depth']} "
              f"stage/log={r['stage_rate']} coefficient={r['coefficient']} "
              f"finite_tf={r['finite_stages']} min_fringe_rows="
              f"{r['min_fringe_rows']} min_sender={r['min_sender']} "
              f"terminal_bits={r['max_terminal_bits']} "
              f"states={r['states']}")


if __name__ == "__main__":
    main()
