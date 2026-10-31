#!/usr/bin/env python3
"""Exact finite audit of D2 sender alignment with the 4096x64 core tiles.

This checks the integer (3,3,2) sparse-bottom FlowDAG, matching the Lean
candidate's 15/4096 ordinary quota factor. It is evidence for a
divisibility induction, not that induction or a sorting theorem.
"""

import argparse
from collections import Counter

from flow_dag import FlowDAG
from oracle import Par


TILE = 4096 * 64
ROW = 64
PARAMS = (3, 3, 2)


def check(depth: int, scale: int, params: tuple[int, int, int]) -> None:
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p,
                   sparse_bottom=True).build()
    states = Counter()
    bad_row = []
    bad_coupled = []
    off_scale = []
    remainders = Counter()
    cut_checks = 0
    for t, row in enumerate(flow.rows):
        for node, (a, pi, blocks) in row.items():
            level, deficit, low, high, children = flow.nodes[node]
            states["active_state"] += 1
            if a:
                remainders[a % TILE] += 1
            else:
                states["zero_allocation"] += 1
            values = {
                "allocation": a,
                "quota": pi,
                "deficit": deficit,
                "low": low,
                "high": high,
                "half_quota": pi // 2,
                **{f"child_{j}": b for j, b in enumerate(blocks)},
            }
            bad_row.extend((t, level, name, value)
                           for name, value in values.items()
                           if value % ROW)
            bad_coupled.extend((t, level, name, value)
                               for name, value in values.items()
                               if (name == "half_quota" or name in ("low", "high"))
                               and value % 2048)
            bad_coupled.extend((t, level, name, value)
                               for name, value in values.items()
                               if name not in ("half_quota", "low", "high")
                               and value % 4096)
            role = "topDesc" if t == 0 else p.role(depth, level, t)
            if children and role not in ("topDesc", "botRise"):
                child_sizes = [flow.nodes[c][1] for c in children]
                total = sum(child_sizes)
                left = low + pi // 2
                right = total - high - pi // 2
                if pi % 8192 or left % 4096 or right % 4096:
                    raise AssertionError((t, level, role, pi, left, right))
                pos = 0
                for child_size in child_sizes:
                    end = pos + child_size
                    left_cut = max(0, min(end, left) - pos)
                    right_cut = max(0, end - max(pos, right))
                    if left_cut % 4096 or right_cut % 4096:
                        raise AssertionError((t, level, pos, child_size,
                                              left, right, left_cut, right_cut))
                    cut_checks += 1
                    pos = end
            if scale % 4096 == 0:
                # 4096-alignment is a useful diagnostic, but not the physical
                # interface: row-major addressing only requires 64-alignment.
                off_scale.extend((t, level, name, value)
                                 for name, value in values.items()
                                 if name != "half_quota" and value % scale)
    if bad_row:
        raise AssertionError(("not row aligned", bad_row[:5]))
    if bad_coupled:
        raise AssertionError(("not coupled 4096/2048 aligned", bad_coupled[:5]))
    print(f"depth={depth} stages={len(flow.rows)} stage_state_rows="
          f"{states['active_state']} zero_allocation_rows="
          f"{states['zero_allocation']}")
    print(f"row_alignment_mod_{ROW}=PASS")
    print("coupled_deficit_port_cut_scales_mod_4096_2048=PASS")
    print(f"ordinary_fronts_and_child_cuts_mod_4096={cut_checks} PASS")
    if scale % 4096 == 0:
        print(f"not_scale_{scale}_aligned_values={len(off_scale)} "
              f"sample={off_scale[:5]}")
        print(f"tile_remainder_classes={len(remainders)} "
              f"partial_states={sum(v for r, v in remainders.items() if r)} "
              f"exact_tile_states={remainders[0]}")
        print(f"tile_remainders={dict(sorted(remainders.items()))}")


def check_reachable_tree_states(depth: int, scale: int,
                                params: tuple[int, int, int]) -> None:
    """Audit every state in every materialized tree, not only active senders."""
    flow = FlowDAG(depth, scale=scale, p=Par(*params),
                   sparse_bottom=True).build()
    checked = 0
    for t, root in enumerate(flow.roots):
        seen = set()
        todo = [root]
        while todo:
            node = todo.pop()
            if node in seen:
                continue
            seen.add(node)
            level, deficit, low, high, children = flow.nodes[node]
            allocation = flow.allocation(node)
            if (deficit % 4096 or allocation % 4096 or
                    low % 2048 or high % 2048):
                raise AssertionError((t, level, deficit, low, high, allocation))
            checked += 1
            todo.extend(children)
    print(f"reachable_tree_states={checked} coupled_alignment_mod_4096_2048=PASS")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=50)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=PARAMS,
                        metavar=("X", "Y", "Z"))
    parser.add_argument("--audit-reachable", action="store_true",
                        help="also check all reachable states at each stage")
    args = parser.parse_args()
    params = tuple(args.params)
    check(args.depth, args.scale, params)
    if args.audit_reachable:
        check_reachable_tree_states(args.depth, args.scale, params)


if __name__ == "__main__":
    main()
