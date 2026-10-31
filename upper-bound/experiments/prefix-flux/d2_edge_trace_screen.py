#!/usr/bin/env python3
"""Exact finite screen for the extreme-left omega-2 mid-sender trace."""
import argparse
from collections import Counter
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--depths", nargs="+", type=int, default=[25, 50, 100])
    ap.add_argument("--row-bits", type=int, default=12)
    args = ap.parse_args()
    m = 1 << args.row_bits
    p = Par(3, 2, 2)
    for depth in args.depths:
        flow = FlowDAG(depth, scale=m, p=p, sparse_bottom=True).build()
        live_edge_states = 0
        edge_send_counts = Counter()
        min_tail_reserves = {}
        child_floors = {
            "topRise": [F(7, 64)] * 6 + [F(1, 8)],
            "mid": [F(7, 64)] * 6 + [F(21, 128)],
            "botDesc": [F(1, 512)] * 7,
        }
        quota_caps = {"topRise": F(1, 128), "mid": F(7, 1024),
                      "botDesc": F(7, 1024)}
        floor_reserves = {"topRise": F(199, 256),
                          "mid": F(1673, 2048),
                          "botDesc": F(21, 2048)}
        # Full boundary-path invariant, at every tree level and snapshot.
        for t in range(len(flow.rows) + 1):
            for level in range(1, depth + 1):
                for edge, index in (("left", 0), ("right", p.k ** level - 1)):
                    node = flow.lookup(t, level, index)
                    _, deficit, low, high, _ = flow.nodes[node]
                    if not flow.allocation(node):
                        continue
                    live_edge_states += 1
                    expected = ((low == deficit and high == 0) if edge == "left"
                                else (low == 0 and high == deficit))
                    assert expected, (depth, t, level, edge,
                                     deficit, low, high)
        # Check the schedule reserve that makes this invariant inductive:
        # ordinary cuts cannot clip the opposite end of either edge child.
        for t, step in enumerate(flow.rows):
            for level in range(1, depth + 1):
                for edge, index in (("left", 0), ("right", p.k ** level - 1)):
                    node = flow.lookup(t, level, index)
                    if node not in step:
                        continue
                    role = p.role(depth, level, t)
                    if role in ("botRise", "topDesc"):
                        continue
                    _, _, low, high, children = flow.nodes[node]
                    _, quota, _ = step[node]
                    child_sizes = [flow.nodes[c][1] for c in children]
                    total = sum(child_sizes)
                    capacity = m * p.cap(depth, level, t)
                    tail = (child_sizes[1:] if edge == "left"
                            else list(reversed(child_sizes[:-1])))
                    assert len(tail) == 7
                    assert all(F(size, capacity) >= bound
                               for size, bound in zip(tail, child_floors[role])), (
                        depth, t, level, edge, role,
                        [F(size, capacity) for size in tail])
                    assert F(quota, capacity) <= quota_caps[role], (
                        depth, t, level, edge, role,
                        F(quota, capacity), quota_caps[role])
                    if edge == "left":
                        reserve = total - high - quota // 2 - child_sizes[0]
                    else:
                        reserve = total - child_sizes[-1] - (low + quota // 2)
                    assert reserve >= 0, (depth, t, level, edge, role, reserve)
                    ratio = F(reserve, capacity)
                    key = (edge, role)
                    previous = min_tail_reserves.get(key)
                    if previous is None or ratio < previous[0]:
                        min_tail_reserves[key] = (ratio, t, level)
                    edge_send_counts[key] += 1

        sides = {"left": Counter(), "right": Counter()}
        minima = {"left": None, "right": None}
        parent_roles = Counter()
        min_reserves = {"left": None, "right": None}
        for t, step in enumerate(flow.rows):
            level = p.omega(depth, t) - 2
            if level < 1 or not p.active(depth, level, t):
                continue
            if p.role(depth, level, t) != "mid":
                continue
            edge_indices = {"left": 0, "right": p.k ** level - 1}
            for edge, index in edge_indices.items():
                node = flow.lookup(t, level, index)
                _, deficit, low, high, _ = flow.nodes[node]
                allocation, quota, _ = step[node]
                expected = ((low == deficit and high == 0) if edge == "left"
                            else (low == 0 and high == deficit))
                assert expected, (depth, t, level, edge, deficit, low, high)
                sides[edge]["one-sided"] += 1
                capacity = m * p.cap(depth, level, t)

                # Check that the preceding parent cut created this endpoint
                # interval by clipping only the designated end child.
                assert t > 0
                parent_level = level - 1
                parent_index = 0 if edge == "left" else p.k ** parent_level - 1
                parent = flow.lookup(t - 1, parent_level, parent_index)
                assert parent in flow.rows[t - 1], (depth, t, edge, "inactive parent")
                parent_roles[p.role(depth, parent_level, t - 1)] += 1
                _, _, parent_low, parent_high, children = flow.nodes[parent]
                _, parent_pi, _ = flow.rows[t - 1][parent]
                child_sizes = [flow.nodes[c][1] for c in children]
                total = sum(child_sizes)
                left_front = parent_low + parent_pi // 2
                right_front = total - parent_high - parent_pi // 2
                parent_capacity = m * p.cap(depth, parent_level, t - 1)
                if edge == "left":
                    margin_a = child_sizes[0] - left_front
                    margin_b = right_front - child_sizes[0]
                    expected_state = (level, left_front, left_front, 0)
                else:
                    last_start = total - child_sizes[-1]
                    margin_a = last_start - left_front
                    margin_b = right_front - last_start
                    right_clip = total - right_front
                    expected_state = (level, right_clip, 0, right_clip)
                assert margin_a >= 0 and margin_b >= 0, (
                    depth, t, edge, margin_a, margin_b)
                assert flow.nodes[node][:4] == expected_state, (
                    depth, t, edge, flow.nodes[node][:4], expected_state)
                for tag, margin in (("near", margin_a), ("far", margin_b)):
                    ratio = F(margin, parent_capacity)
                    old = min_reserves[edge]
                    if old is None or ratio < old[0]:
                        min_reserves[edge] = (ratio, tag, t, parent_level)

                if quota:
                    fringe = F(m * quota, 2 * allocation)
                    candidate = (fringe, t, level, F(allocation, capacity),
                                 F(deficit, capacity))
                    old = minima[edge]
                    if old is None or fringe < old[0]:
                        minima[edge] = candidate
        print(f"depth={depth}, row_bits={args.row_bits}, "
              f"live_edge_states={live_edge_states}, "
              f"edge_senders={dict(edge_send_counts)}, "
              f"floor_reserve_targets={floor_reserves}, "
              f"min_tail_reserves={min_tail_reserves}, "
              f"edge_states={sum(c['one-sided'] for c in sides.values())}, "
              f"left={dict(sides['left'])}, right={dict(sides['right'])}, "
              f"parent_roles={dict(parent_roles)}, reserves={min_reserves}, "
              f"minima={minima}")


if __name__ == "__main__":
    main()
