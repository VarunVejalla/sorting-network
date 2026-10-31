#!/usr/bin/env python3
"""Exact two-step identity audit for the standard (3,3,2) D2 flow.

This is a finite check against FlowDAG itself, not an all-depth proof. Unlike
d2_two_step_audit.py, it uses the standard unsaturated (3,3,2) flow underlying
the conditional 273 coefficient.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache

from flow_dag import FlowDAG
from oracle import Par


ORDINARY = {"mid", "botDesc", "topRise"}


def audit(depth: int, row_bits: int) -> None:
    p = Par(3, 3, 2)
    scale = 1 << row_bits
    flow = FlowDAG(depth, scale=scale, p=p).build()
    endpoint_slack_by_role = {}
    endpoint_reserve_by_role = {}
    endpoint_front_by_role = {}
    endpoint_containment_checks = 0
    for t, rows in enumerate(flow.rows):
        for node, (_, pi, _) in rows.items():
            if pi <= 0:
                continue
            role = p.role(depth, flow.nodes[node][0], t)
            if role not in ORDINARY:
                continue
            _, _, low, high, children = flow.nodes[node]
            assert children
            end_cap = scale * p.cap(depth, flow.nodes[node][0] + 1, t)
            parent_cap = scale * p.cap(depth, flow.nodes[node][0], t)
            first_u = flow.nodes[children[0]][1]
            last_u = flow.nodes[children[-1]][1]
            first_slack = first_u - low - pi // 2
            last_slack = last_u - high - pi // 2
            assert first_slack >= 0 and last_slack >= 0, (
                depth, t, flow.nodes[node][0], role,
                first_slack, last_slack, low, high, pi,
            )
            slack = F(min(first_slack, last_slack), end_cap)
            endpoint_slack_by_role[role] = min(
                endpoint_slack_by_role.get(role, slack), slack
            )
            reserve = F(min(first_u, last_u), parent_cap)
            front = F(max(low + pi // 2, high + pi // 2), parent_cap)
            endpoint_reserve_by_role[role] = min(
                endpoint_reserve_by_role.get(role, reserve), reserve
            )
            endpoint_front_by_role[role] = max(
                endpoint_front_by_role.get(role, front), front
            )
            endpoint_containment_checks += 1

    cases = Counter()
    max_ratio = F(0)
    max_g = F(0)
    min_ratio_by_role = {}
    min_surplus_by_role = {}
    checked = 0

    @lru_cache(None)
    def triples(n0: int, n1: int, n2: int, lev: int):
        """Traverse each shared aligned state triple once in the DAG."""
        yield n0, n1, n2, lev
        c0, c1, c2 = (flow.nodes[n][4] for n in (n0, n1, n2))
        assert len(c0) == len(c1) == len(c2)
        for a, b, c in zip(c0, c1, c2):
            yield from triples(a, b, c, lev + 1)

    for t in range(3, len(flow.rows)):
        triples.cache_clear()
        aligned = set(triples(flow.roots[t - 2], flow.roots[t - 1],
                              flow.roots[t], 0))
        for n0, n1, n2, lev in aligned:
            if lev == 0 or not p.active(depth, lev, t):
                continue
            role = p.role(depth, lev, t)
            if role not in ORDINARY:
                continue
            current = flow.rows[t].get(n2)
            if current is None or current[1] <= 0:
                continue
            old = flow.rows[t - 2].get(n0)
            if old is None:
                raise AssertionError((depth, t, lev, role, "missing t-2 update"))

            c2 = scale * p.cap(depth, lev, t)
            c0 = scale * p.cap(depth, lev, t - 2)
            c1 = scale * p.cap(depth, lev + 1, t - 1)
            assert c0 == 16 * c2 and c1 == 32 * c2, (
                depth, t, lev, c0, c1, c2
            )
            g0 = F(flow.nodes[n0][1], c0)
            g2 = F(flow.nodes[n2][1], c2)
            rho0 = F(old[1], c0)
            child_rho = F(0)
            for child in flow.nodes[n1][4]:
                child_row = flow.rows[t - 1].get(child)
                if child_row is not None:
                    rho_child = F(child_row[1], c1)
                    assert rho_child <= F(1, 256), (
                        depth, t, lev, role, child, rho_child
                    )
                    child_rho += rho_child

            lhs = F(current[0], c2)
            rho_current = F(current[1], c2)
            rhs = 16 * g0 + 16 * rho0 + 32 * child_rho - g2
            assert lhs == rhs, (depth, t, lev, role, lhs, rhs)
            assert lhs >= rho_current, (depth, t, lev, role, lhs, rho_current)
            assert g2 <= F(1, 512), (depth, t, lev, role, g2)
            assert rho0 <= F(1, 256), (depth, t, lev, role, rho0)
            max_ratio = max(max_ratio, lhs)
            max_g = max(max_g, g2)
            min_ratio_by_role[role] = min(min_ratio_by_role.get(role, lhs), lhs)
            surplus = lhs - rho_current
            min_surplus_by_role[role] = min(
                min_surplus_by_role.get(role, surplus), surplus
            )
            checked += 1

            child_role = (p.role(depth, lev + 1, t - 1)
                          if p.active(depth, lev + 1, t - 1) else "inactive")
            old_role = p.role(depth, lev, t - 2)
            if child_role == "botRise":
                assert role == old_role == "botDesc", (
                    depth, t, lev, role, old_role, child_role
                )
                assert lhs <= F(279, 256)
                cases["botRise children / botDesc endpoints"] += 1
            elif child_role == "inactive":
                assert old_role == "botRise", (
                    depth, t, lev, role, old_role, child_role
                )
                # At a botRise time 3j, level i=j+2. The explicit omega
                # residue formulas put every earlier omega below i+1, so its
                # eight children have remained inactive/full since startup.
                old_children = flow.nodes[n0][4]
                child_native = scale * p.k ** (depth - lev - 1)
                assert len(old_children) == p.k
                assert all(flow.nodes[ch][1] == child_native
                           for ch in old_children), (
                    depth, t, lev, [flow.nodes[ch][1] for ch in old_children],
                    child_native
                )
                # The allocation definition gives G+a=sum child deficits;
                # botRise then sends all a, so g+rho=native/c=1/256.
                assert g0 + rho0 == F(1, 256), (
                    depth, t, lev, g0, rho0
                )
                assert lhs >= F(31, 512), (
                    depth, t, lev, lhs, g2, g0, rho0
                )
                cases["inactive child / botRise predecessor exact sum"] += 1
            else:
                assert child_role != "topRise", (depth, t, lev, child_role)
                cases[f"child {child_role}; predecessor {old_role}"] += 1
                assert lhs <= F(279, 256), (
                    depth, t, lev, role, old_role, child_role, lhs
                )

    print(f"(3,3,2) depth={depth}, row_scale=2^{row_bits}: "
          f"checked={checked}, max a/c={max_ratio}, max g={max_g}")
    print(f"minimum a/c by role={dict(min_ratio_by_role)}")
    print(f"minimum (a-pi)/c by role={dict(min_surplus_by_role)}")
    print(f"minimum normalized endpoint slack by role="
          f"{dict(endpoint_slack_by_role)}")
    print(f"minimum endpoint reserve / parent cap by role="
          f"{dict(endpoint_reserve_by_role)}")
    print(f"maximum endpoint front / parent cap by role="
          f"{dict(endpoint_front_by_role)}")
    print(f"exact endpoint-containment checks={endpoint_containment_checks}")
    print(f"schedule cases={dict(cases)}")
    print("Exact finite identity and role bounds pass; no all-depth theorem claimed.")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=30)
    ap.add_argument("--row-bits", type=int, default=13)
    args = ap.parse_args()
    audit(args.depth, args.row_bits)


if __name__ == "__main__":
    main()
