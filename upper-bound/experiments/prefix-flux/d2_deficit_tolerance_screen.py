#!/usr/bin/env python3
"""Finite screen for relaxing the D2 per-sender outsider/deficit allowance.

For every reachable active ordinary sender, compare its actual parent deficit
with the scheduled capacity. Report both the unconditional maximum ratio and
the maximum among states whose non-deficit local gates (quota and endpoint
reserves) pass. This is diagnostic evidence only; it is not an all-depth
invariant proof.
"""
import argparse
from collections import Counter
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth: int, scale: int, params: tuple[int, int, int]) -> None:
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    roles = {"topRise", "mid", "botDesc"}
    maxima = {"all": (Fraction(-1), None), "other_gates": (Fraction(-1), None)}
    checked = Counter()
    pass_counts = Counter()
    budget_violations = Counter()
    budgets = (Fraction(1, 512), Fraction(23, 4096), Fraction(1, 128),
               Fraction(1, 64), Fraction(1, 32))

    for stage, row in enumerate(flow.rows):
        if stage == 0:
            continue
        for node_id in flow.reachable(stage):
            level, deficit, _low, _high, children = flow.nodes[node_id]
            role = p.role(depth, level, stage)
            if role not in roles or node_id not in row:
                continue
            capacity = scale * p.cap(depth, level, stage)
            if capacity <= 0:
                continue
            ratio = Fraction(deficit, 1) / capacity
            where = (stage, level, role, deficit, capacity)
            checked[role] += 1
            if ratio > maxima["all"][0]:
                maxima["all"] = (ratio, where)
            quota = row[node_id][1]
            ends_ok = (128 * flow.nodes[children[0]][1] >= capacity and
                       128 * flow.nodes[children[-1]][1] >= capacity)
            other_ok = 256 * quota <= capacity and ends_ok
            if other_ok:
                if ratio > maxima["other_gates"][0]:
                    maxima["other_gates"] = (ratio, where)
                pass_counts[role] += 1
                for budget in budgets:
                    if ratio > budget:
                        budget_violations[(role, budget)] += 1

    print(f"depth={depth} scale={scale} reachable={sum(map(len, flow.rows))}")
    for label, (ratio, where) in maxima.items():
        print(f"{label}_max={ratio} ({float(ratio):.12g}) at={where}")
    for role in sorted(roles):
        print(f"role={role} checked={checked[role]} pass_other_gates={pass_counts[role]}")
        for budget in budgets:
            violations = budget_violations[(role, budget)]
            print(f"  budget={budget} violations={violations}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=30)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    args = parser.parse_args()
    screen(args.depth, args.scale, tuple(args.params))
