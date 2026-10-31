#!/usr/bin/env python3
"""Finite schedule audit for the parent sources of active D2 senders.

For every active topRise/mid/botDesc node, check that its parent was active
one stage earlier, that the parent was not botRise, and that a topRise node's
parent was topDesc. Also classify the same-level sender two stages earlier:
either it was ordinary, or the current sender is the strong botDesc base case.
This checks schedule arithmetic only, not flow values.
"""
import argparse

from oracle import Par


def audit(depth):
    p = Par(3, 3, 2)
    ordinary = {"topRise", "mid", "botDesc"}
    parents = {}
    predecessors = {}
    bases = {}
    checked = 0
    for t in range(1, p.tf(depth) + 1):
        if t == 1:
            levels = (1,)
        else:
            lo, hi = p.alpha(depth, t), p.omega(depth, t)
            levels = range(lo + ((t - lo) % 2), hi + 1, 2)
        for i in levels:
            if i == 0 or not p.active(depth, i, t):
                continue
            role = p.role(depth, i, t)
            if role not in ordinary:
                continue
            parent_role = p.role(depth, i - 1, t - 1)
            assert p.active(depth, i - 1, t - 1), (depth, i, t, role)
            assert parent_role != "botRise", (depth, i, t, role, parent_role)
            if role == "topRise":
                assert parent_role == "topDesc", (depth, i, t, role, parent_role)
            parents[parent_role] = parents.get(parent_role, 0) + 1
            if t < 3:
                expected = (1, 1, "topRise") if t == 1 else (2, 2, "botDesc")
                assert (t, i, role) == expected, (depth, t, i, role)
                bases[role] = bases.get(role, 0) + 1
            else:
                assert p.active(depth, i, t - 2), (depth, i, t, role)
                old_role = p.role(depth, i, t - 2)
                if old_role == "botRise":
                    assert role == "botDesc" and t == 3 * i - 4, (
                        depth, i, t, role, old_role)
                    old_role = "botRise -> strong botDesc"
                else:
                    assert old_role in ordinary, (depth, i, t, role, old_role)
                predecessors[old_role] = predecessors.get(old_role, 0) + 1
            checked += 1
    print(f"depth={depth}: checked {checked} ordinary active senders")
    print(f"preceding parent roles: {parents}")
    print(f"same-level two-stage predecessors: {predecessors}; startup bases: {bases}")
    print("PASS: each case is an ordinary predecessor, strong botDesc/native base, or startup base")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=1000)
    args = ap.parse_args()
    audit(args.depth)
