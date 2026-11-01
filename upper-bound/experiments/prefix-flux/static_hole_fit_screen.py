#!/usr/bin/env python3
"""Compare the current and clamped empty-hole conventions on reachable D2 states.

This is a finite model screen, not a proof. Saturated children have empty
occupied intervals, so their point markers may be moved without changing the
sender bag. The screen checks whether clamping those points into the parent
interval restores the ordered StaticHolesFit geometry in the exact FlowDAG.
"""
import argparse

from flow_dag import FlowDAG
from oracle import Par


def holes_for(flow, node, clamp_empty):
    level, _, left, right, children = flow.nodes[node]
    width = flow.native(level + 1)
    stop = 8 * width - right
    holes = []
    for j, child in enumerate(children):
        _, deficit, child_left, child_right, _ = flow.nodes[child]
        if deficit == width:
            point = j * width
            if clamp_empty:
                point = min(stop, max(left, point))
            elif j == 0:
                point = left
            elif j == 7:
                point = stop
            holes.append((point, point))
        else:
            holes.append((j * width + child_left,
                          (j + 1) * width - child_right))
    return left, stop, holes


def fits(flow, node, clamp_empty):
    cursor, stop, holes = holes_for(flow, node, clamp_empty)
    if cursor > stop:
        return False
    for lo, hi in holes:
        if not cursor <= lo <= hi <= stop:
            return False
        cursor = hi
    return True


def check(depth, scale, params, sparse_bottom=False):
    flow = FlowDAG(depth, scale=scale, p=Par(*params),
                   sparse_bottom=sparse_bottom).build()
    old_fail = 0
    clamped_fail = 0
    checked = 0
    first_old = None
    first_clamped = None
    for stage in range(len(flow.roots)):
        for node in flow.reachable(stage):
            if not flow.nodes[node][4]:
                continue
            checked += 1
            if not fits(flow, node, clamp_empty=False):
                old_fail += 1
                if first_old is None:
                    first_old = (stage, node, flow.nodes[node])
            if not fits(flow, node, clamp_empty=True):
                clamped_fail += 1
                if first_clamped is None:
                    first_clamped = (stage, node, flow.nodes[node])
    return checked, old_fail, clamped_fail, first_old, first_clamped


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, nargs="+",
                        default=[7, 8, 10, 12, 14, 16, 20])
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    parser.add_argument("--sparse-bottom", action="store_true")
    args = parser.parse_args()

    for depth in args.depths:
        checked, old_fail, clamped_fail, first_old, first_clamped = check(
            depth, args.scale, args.params, args.sparse_bottom
        )
        print(f"d={depth}: {checked} reachable node-stages; "
              f"current markers fail {old_fail}; clamped markers fail "
              f"{clamped_fail}")
        if first_old is not None:
            stage, node, state = first_old
            level, deficit, left, right, children = state
            print(f"  first current-marker failure: stage={stage}, level={level}, "
                  f"state={node}, (G,low,high)=({deficit},{left},{right})")
        if first_clamped is not None:
            stage, node, state = first_clamped
            level, deficit, left, right, children = state
            print(f"  first clamped-marker failure: stage={stage}, level={level}, "
                  f"state={node}, (G,low,high)=({deficit},{left},{right})")


if __name__ == "__main__":
    main()
