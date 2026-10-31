#!/usr/bin/env python3
"""Exact finite screen for D2 top-descending sender allocations by frontier history.

This is an audit of the fixed integer flow, not an all-depth bound.
"""
import argparse
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth):
    p = Par(3, 3, 2)
    flow = FlowDAG(depth, scale=1, p=p).build()
    result = {}
    for t, row in enumerate(flow.rows):
        if t < 2 or t + 1 >= p.tf(depth):
            continue
        level = p.alpha(depth, t)
        if level >= p.alpha(depth, t + 1):
            continue
        pattern = (p.alpha(depth, t - 2) - level,
                   p.alpha(depth, t - 1) - level)
        record = result.setdefault(pattern, [Fraction(0), None, 0])
        scheduled = Fraction(p.alloc(depth, level, t))
        assert scheduled > 0
        for node in flow.reachable(t):
            if flow.nodes[node][0] != level or node not in row:
                continue
            ratio = Fraction(flow.allocation(node), 1) / scheduled
            record[2] += 1
            if ratio > record[0]:
                record[0] = ratio
                record[1] = (t, level, flow.allocation(node), scheduled)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depth", type=int, nargs="*", default=[20, 30, 40])
    for depth in parser.parse_args().depth:
        print(f"depth={depth}")
        for pattern, (ratio, witness, count) in sorted(screen(depth).items()):
            print(f"  history={pattern}: max={ratio}, witness={witness}, nodes={count}")
