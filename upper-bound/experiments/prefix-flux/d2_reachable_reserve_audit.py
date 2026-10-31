#!/usr/bin/env python3
"""Finite audit of the proposed D2 sender and endpoint-reserve invariant.

This checks actual FlowDAG states for the (3,3,2) candidate. Passing depths
are diagnostics only; they do not establish the all-depth induction.
"""
import argparse
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def audit(depth: int, scale: int) -> None:
    params = Par(3, 3, 2)
    flow = FlowDAG(depth, scale=scale, p=params).build()
    checked = 0
    max_deficit_ratio = (Fraction(0), None)
    max_quota_ratio = (Fraction(0), None)
    min_left_reserve = (None, None)
    min_right_reserve = (None, None)
    min_allocation_slack = (None, None)
    min_affine_deficit_slack = (None, None)
    min_affine_deficit_slack_ratio = (None, None)
    affine_profile_failures = 0
    affine_profile_witness = None
    balanced_special_senders = 0
    special_balance_failures = 0
    topdesc_senders = 0
    topdesc_nonzero_roots = 0
    for stage, rows in enumerate(flow.rows):
        for node_id, (allocation, quota, _blocks) in rows.items():
            level, deficit, low, high, children = flow.nodes[node_id]
            role = params.role(depth, level, stage)
            if role in ("topDesc", "botRise"):
                balanced_special_senders += 1
                special_balance_failures += low + high != deficit
                if role == "topDesc":
                    topdesc_senders += 1
                    topdesc_nonzero_roots += deficit != 0
                    if low + high != deficit or deficit != 0:
                        affine_profile_failures += 1
                        if affine_profile_witness is None:
                            affine_profile_witness = {
                                "location": (stage, level, role),
                                "deficit": deficit,
                                "low": low,
                                "high": high,
                                "reason": "topDesc requires balance and zero root",
                            }
                continue
            if role not in ("topRise", "mid", "botDesc"):
                continue
            capacity = scale * params.cap(depth, level, stage)
            assert capacity.denominator == 1, (depth, stage, level, capacity)
            capacity = int(capacity)
            end_deficits = (
                flow.nodes[children[0]][1],
                flow.nodes[children[-1]][1],
            )
            child_total = sum(flow.nodes[child][1] for child in children)
            location = (stage, level, role)
            checks = (
                512 * deficit <= capacity,
                256 * quota <= capacity,
                128 * end_deficits[0] >= capacity,
                128 * end_deficits[1] >= capacity,
                quota <= allocation,
                quota % 2 == 0,
                low + high == deficit,
                allocation == child_total - deficit,
            )
            if not all(checks):
                raise AssertionError(
                    {
                        "depth": depth,
                        "stage": stage,
                        "level": level,
                        "role": role,
                        "allocation": allocation,
                        "deficit": deficit,
                        "quota": quota,
                        "capacity": capacity,
                        "endpoint_deficits": end_deficits,
                        "child_total": child_total,
                        "checks": checks,
                    }
                )
            affine_profile_ok = (
                role == "topRise"
                and deficit == 0
                and 256 * quota <= capacity
            ) or (
                role in ("mid", "botDesc")
                and 8192 * deficit + 7 <= 15 * capacity
                and 4096 * quota <= 15 * capacity
            )
            if not affine_profile_ok:
                affine_profile_failures += 1
                if affine_profile_witness is None:
                    affine_profile_witness = {
                        "location": location,
                        "deficit": deficit,
                        "quota": quota,
                        "capacity": capacity,
                        "affine_slack": 15 * capacity - 8192 * deficit,
                    }
            checked += 1
            g_ratio = Fraction(deficit, capacity)
            if g_ratio > max_deficit_ratio[0]:
                max_deficit_ratio = (g_ratio, location)
            q_ratio = Fraction(256 * quota, capacity)
            if q_ratio > max_quota_ratio[0]:
                max_quota_ratio = (q_ratio, location)
            left_reserve = Fraction(128 * end_deficits[0], capacity)
            if min_left_reserve[0] is None or left_reserve < min_left_reserve[0]:
                min_left_reserve = (left_reserve, location)
            right_reserve = Fraction(128 * end_deficits[1], capacity)
            if min_right_reserve[0] is None or right_reserve < min_right_reserve[0]:
                min_right_reserve = (right_reserve, location)
            allocation_slack = Fraction(allocation - quota, capacity)
            if min_allocation_slack[0] is None or allocation_slack < min_allocation_slack[0]:
                min_allocation_slack = (allocation_slack, location)
            affine_slack = 15 * capacity - 8192 * deficit
            if min_affine_deficit_slack[0] is None or affine_slack < min_affine_deficit_slack[0]:
                min_affine_deficit_slack = (affine_slack, location)
            affine_slack_ratio = Fraction(affine_slack, capacity)
            if (
                min_affine_deficit_slack_ratio[0] is None
                or affine_slack_ratio < min_affine_deficit_slack_ratio[0]
            ):
                min_affine_deficit_slack_ratio = (affine_slack_ratio, location)
    print(
        f"d={depth}: {checked} active ordinary senders pass deficit, quota, "
        f"sender-input checks; {len(flow.nodes)} interned states\n"
        f"  special-role senders={balanced_special_senders}, "
        f"balance failures={special_balance_failures}; "
        f"topDesc senders={topdesc_senders}, "
        f"nonzero topDesc roots={topdesc_nonzero_roots}\n"
        f"  max deficit/cap={max_deficit_ratio[0]} at {max_deficit_ratio[1]}\n"
        f"  max 256*quota/cap={max_quota_ratio[0]} at {max_quota_ratio[1]}\n"
        f"  min endpoint reserve 128*G/cap: left={min_left_reserve[0]} "
        f"at {min_left_reserve[1]}, right={min_right_reserve[0]} "
        f"at {min_right_reserve[1]}\n"
        f"  min normalized (allocation-quota)/cap={min_allocation_slack[0]} "
        f"at {min_allocation_slack[1]}\n"
        f"  min integer slack 15*cap-8192*deficit="
        f"{min_affine_deficit_slack[0]} at {min_affine_deficit_slack[1]}\n"
        f"  min normalized affine slack="
        f"{min_affine_deficit_slack_ratio[0]} at "
        f"{min_affine_deficit_slack_ratio[1]}\n"
        f"  strong affine-profile failures={affine_profile_failures}; "
        f"first witness={affine_profile_witness}"
    )
    return (
        affine_profile_failures == 0
        and special_balance_failures == 0
        and topdesc_nonzero_roots == 0
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=110)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument(
        "--require-affine",
        action="store_true",
        help="exit nonzero unless ordinary affine and special-role balance/zero-root gates pass",
    )
    args = parser.parse_args()
    affine_ok = audit(args.depth, args.scale)
    if args.require_affine and not affine_ok:
        raise SystemExit(1)
