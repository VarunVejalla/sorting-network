#!/usr/bin/env python3
"""Finite screen for whether an 832-wire dirty band can span 3 D2 ports.

This checks every compressed active sender row in the FlowDAG at the requested
depth. It is a schedule diagnostic only; it is not an all-depth theorem or a
fixed-network sorting proof.
"""
import argparse

from flow_dag import FlowDAG
from oracle import Par


def audit(depth=100, scale=8192, band_width=832, params=(3, 3, 2)):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    minimum = None
    witness = None
    positive = below = 0
    for t, row in enumerate(flow.rows):
        for node, (_allocation, _quota, blocks) in row.items():
            level = flow.nodes[node][0]
            role = "topDesc" if t == 0 else flow.p.role(depth, level, t)
            for port, width in enumerate(blocks):
                if width <= 0:
                    continue
                positive += 1
                if width < band_width:
                    below += 1
                if minimum is None or width < minimum:
                    minimum = width
                    witness = (t, level, role, port, width)
    return {
        "depth": depth,
        "scale": scale,
        "band_width": band_width,
        "flow_nodes": len(flow.nodes),
        "compressed_stage_rows": sum(map(len, flow.rows)),
        "positive_child_ports": positive,
        "ports_below_band_width": below,
        "minimum_positive_child_port": minimum,
        "minimum_witness_(stage,level,role,port,width)": witness,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=100)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--band-width", type=int, default=832)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    args = parser.parse_args()
    result = audit(args.depth, args.scale, args.band_width, tuple(args.params))
    print(result)
    print("FINITE DIAGNOSTIC ONLY; not an all-depth port-width proof")
