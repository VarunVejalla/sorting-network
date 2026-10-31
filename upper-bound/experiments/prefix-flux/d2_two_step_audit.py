#!/usr/bin/env python3
"""Exact finite audit of the two-step allocation identity for D2 sparse flow.

This checks every distinct aligned state triple in the shared FlowDAG.  It is
finite evidence only; in particular, the G monotonicity result is not proved
for arbitrary depth.
"""
import argparse
from collections import Counter
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par


def audit(depth: int, row_bits: int) -> None:
    p = Par(3, 2, 2)
    scale = 1 << row_bits
    flow = FlowDAG(depth, scale=scale, p=p, sparse_bottom=True).build()
    counts = {"mid": 0, "previous_unsaturated": 0, "children_unsaturated": 0,
              "identity": 0, "child_deficit_update": 0,
              "g_monotone": 0, "bound": 0}
    min_ratio = None
    min_child_quota = None
    min_quota_term = None
    min_deficit_drop = None
    child_role_counts = {}
    previous_role_counts = {}
    profile_counts = {"mid": 0, "envelope": 0, "allocation_identity": 0,
                      "left_cut": 0, "right_cut": 0,
                      "left_eq": 0, "right_eq": 0}
    min_profile_margin = None
    min_left_cut_margin = None
    min_right_cut_margin = None
    min_half_terms = {name: None for name in
                      ("left_carry", "right_carry", "left_fresh", "right_fresh",
                       "left_slack4", "right_slack4")}
    half_role_summary = {}
    botdesc_pair_points = set()
    botdesc_ancestor_roles = Counter()
    botdesc_reset_summary = {}
    botdesc_allocation_points = {}
    botdesc_endpoint_prefix_min = [None] * 4
    cut_tightness = Counter()
    cut_boundary_exception_stages = Counter()
    floor = (F(21, 512), *([F(7, 256)] * 6), F(21, 512))
    max_level_triples = 0

    for t in range(2, len(flow.rows)):
        # Test a componentwise strengthening and the paired half-profile cut
        # invariant on every distinct current mid state.
        C_parent = lambda lev: scale * p.cap(depth, lev, t)
        for node, (a, _, _) in flow.rows[t].items():
            lev, G, low, high, children = flow.nodes[node]
            if lev == 0 or p.role(depth, lev, t) != "mid":
                continue
            C = C_parent(lev)
            g = F(G, C)
            profiles = [F(flow.nodes[ch][1], p.A * C) for ch in children]
            left_slack = sum(profiles[:4], F(0)) - F(63, 512)
            right_slack = sum(profiles[4:], F(0)) - F(63, 512)
            left_cut_margin = left_slack - F(low, 4 * C)
            right_cut_margin = right_slack - F(high, 4 * C)
            debt_side = "both" if low and high else "low" if low else "high" if high else "zero"
            cut_tightness[(debt_side, left_cut_margin == 0,
                           right_cut_margin == 0)] += 1
            expected_tight = (
                right_cut_margin == 0 if low and not high else
                left_cut_margin == 0 if high and not low else
                left_cut_margin == 0 and right_cut_margin == 0 if not low and not high else
                False
            )
            if (lev == p.omega(depth, t) - 2 and low + high > 0
                    and not expected_tight):
                cut_boundary_exception_stages[t] += 1
            profile_counts["left_cut"] += left_cut_margin >= 0
            profile_counts["right_cut"] += right_cut_margin >= 0
            profile_counts["left_eq"] += left_cut_margin == 0
            profile_counts["right_eq"] += right_cut_margin == 0
            min_left_cut_margin = (left_cut_margin if min_left_cut_margin is None
                                   else min(min_left_cut_margin, left_cut_margin))
            min_right_cut_margin = (right_cut_margin if min_right_cut_margin is None
                                    else min(min_right_cut_margin, right_cut_margin))
            profile_counts["mid"] += 1
            profile_counts["allocation_identity"] += F(a, C) == (
                p.A * sum(profiles, F(0)) - g
            )
            for actual, base in zip(profiles, floor):
                margin = actual - base - g / (p.A * p.k)
                min_profile_margin = (margin if min_profile_margin is None
                                      else min(min_profile_margin, margin))
                if margin >= 0:
                    profile_counts["envelope"] += 1

        # This is a DAG traversal, not a tree generator: repeated interned
        # triples should be visited once. Use an explicit visited set rather
        # than relying on cached, partially consumed generator objects.
        triples = set()
        stack = [(flow.roots[t - 2], flow.roots[t - 1], flow.roots[t], 0)]
        while stack:
            n0, n1, n2, lev = stack.pop()
            triple = (n0, n1, n2, lev)
            if triple in triples:
                continue
            triples.add(triple)
            ch0, ch1, ch2 = (flow.nodes[n][4] for n in (n0, n1, n2))
            assert len(ch0) == len(ch1) == len(ch2)
            stack.extend((a, b, c, lev + 1)
                         for a, b, c in zip(ch0, ch1, ch2))
        by_level = {}
        for triple in triples:
            by_level.setdefault(triple[3], []).append(triple)
        for lev, level_triples in by_level.items():
            max_level_triples = max(max_level_triples, len(level_triples))
            if lev == 0 or not p.active(depth, lev, t) or p.role(depth, lev, t) != "mid":
                continue
            C0 = scale * p.cap(depth, lev, t - 2)
            C1 = scale * p.cap(depth, lev + 1, t - 1)
            C2 = scale * p.cap(depth, lev, t)
            assert C0 == 16 * C2 and C1 == 16 * C2, (depth, t, lev, C0, C1, C2)
            for n0, n1, n2, _ in level_triples:
                old = flow.rows[t - 2].get(n0)
                cur = flow.rows[t].get(n2)
                if old is None or cur is None:
                    raise AssertionError(("missing endpoint row", t, lev))
                a0, pi0, _ = old
                a2, _, _ = cur
                G0 = flow.nodes[n0][1]
                G2 = flow.nodes[n2][1]
                kids1 = flow.nodes[n1][4]
                child_rows = [flow.rows[t - 1].get(child) for child in kids1]
                if any(row is None for row in child_rows):
                    raise AssertionError(("missing child row", t, lev))
                child_pi = [int(row[1]) for row in child_rows]
                cut_children = flow.nodes[n1][4]
                current_children = flow.nodes[n2][4]
                child_update = all(
                    flow.nodes[current_child][1]
                    == flow.nodes[cut_child][1] + int(row[1])
                    for cut_child, current_child, row
                    in zip(cut_children, current_children, child_rows)
                )
                counts["child_deficit_update"] += child_update
                low2, high2 = flow.nodes[n2][2:4]
                left_carry = F(sum(flow.nodes[ch][1] for ch in cut_children[:4]) - low2, C2)
                right_carry = F(sum(flow.nodes[ch][1] for ch in cut_children[4:]) - high2, C2)
                left_fresh = F(sum(child_pi[:4]), C2)
                right_fresh = F(sum(child_pi[4:]), C2)
                current_left = F(sum(flow.nodes[ch][1] for ch in current_children[:4]), C2)
                current_right = F(sum(flow.nodes[ch][1] for ch in current_children[4:]), C2)
                left_slack4 = left_carry + left_fresh - F(63, 128)
                right_slack4 = right_carry + right_fresh - F(63, 128)
                assert current_left - F(low2, C2) - F(63, 128) == left_slack4
                assert current_right - F(high2, C2) - F(63, 128) == right_slack4
                for name, value in (("left_carry", left_carry), ("right_carry", right_carry),
                                    ("left_fresh", left_fresh), ("right_fresh", right_fresh),
                                    ("left_slack4", left_slack4), ("right_slack4", right_slack4)):
                    old = min_half_terms[name]
                    min_half_terms[name] = value if old is None else min(old, value)
                child_role = p.role(depth, lev + 1, t - 1)
                role_key = (child_role, p.role(depth, lev, t - 2))
                role_values = half_role_summary.setdefault(
                    role_key, {"count": 0, "left_min_sum": None,
                               "right_min_sum": None, "left_min_carry": None,
                               "left_min_fresh": None})
                role_values["count"] += 1
                for name, value in (("left_min_sum", left_carry + left_fresh),
                                    ("right_min_sum", right_carry + right_fresh),
                                    ("left_min_carry", left_carry),
                                    ("left_min_fresh", left_fresh)):
                    old = role_values[name]
                    role_values[name] = value if old is None else min(old, value)
                if role_key == ("botDesc", "botDesc"):
                    ancestor_role = (
                        p.role(depth, lev - 1, t - 1)
                        if p.active(depth, lev - 1, t - 1) else "inactive"
                    )
                    botdesc_ancestor_roles[ancestor_role] += 1
                    botdesc_pair_points.add((left_carry, left_fresh))
                    botdesc_pair_points.add((right_carry, right_fresh))
                    q_child = F(7, 64)  # raw botDesc quota / current parent C
                    for indices, debt in ((range(4), low2),
                                          (range(7, 3, -1), high2)):
                        term_sum = F(0)
                        for prefix, j in enumerate(indices, start=1):
                            g_j = flow.nodes[cut_children[j]][1]
                            a_j = int(child_rows[j][0])
                            capacity_j = F(g_j + a_j, C2)
                            assert capacity_j >= q_child
                            term_sum += min(F(g_j, C2), capacity_j - q_child)
                            reserve_slack = term_sum - F(debt, C2) - F(7, 128)
                            old = botdesc_endpoint_prefix_min[prefix - 1]
                            botdesc_endpoint_prefix_min[prefix - 1] = (
                                reserve_slack if old is None else min(old, reserve_slack)
                            )
                r0, rkids = F(int(pi0), C0), sum(map(F, child_pi), F(0)) / C1
                lhs = F(int(a2), C2)
                rhs = 16 * F(G0, C0) + 16 * r0 + 16 * rkids - F(G2, C2)
                counts["mid"] += 1
                counts["identity"] += lhs == rhs
                counts["g_monotone"] += G2 <= G0
                counts["previous_unsaturated"] += int(int(pi0) < int(a0))
                prev_role = p.role(depth, lev, t - 2)
                prev_counts = previous_role_counts.setdefault(prev_role, [0, 0, 0])
                prev_counts[0] += 1
                prev_counts[1] += int(int(pi0) >= int(a0))
                prev_counts[2] += int(int(a0) > 0 and int(pi0) >= int(a0))
                child_unsat = all(int(row[1]) < int(row[0]) for row in child_rows)
                counts["children_unsaturated"] += int(child_unsat)
                ratio = lhs
                min_ratio = ratio if min_ratio is None else min(min_ratio, ratio)
                min_child_quota = rkids if min_child_quota is None else min(min_child_quota, rkids)
                quota_term = 16 * (r0 + rkids)
                deficit_drop = F(G0 - G2, C2)
                min_quota_term = (quota_term if min_quota_term is None
                                  else min(min_quota_term, quota_term))
                min_deficit_drop = (deficit_drop if min_deficit_drop is None
                                    else min(min_deficit_drop, deficit_drop))
                counts["bound"] += ratio >= F(63, 64)
                for child, row in zip(kids1, child_rows):
                    child_role = p.role(depth, lev + 1, t - 1)
                    child_a, child_quota, _ = row
                    role_counts = child_role_counts.setdefault(child_role, [0, 0, 0])
                    role_counts[0] += 1
                    role_counts[1] += int(int(child_quota) < int(child_a))
                    role_counts[2] += int(int(child_a) > 0 and int(child_quota) >= int(child_a))

                child_role_now = p.role(depth, lev + 1, t - 1)
                prev_role_now = p.role(depth, lev, t - 2)
                if child_role_now == prev_role_now == "botDesc":
                    ancestor_role = (
                        p.role(depth, lev - 1, t - 1)
                        if p.active(depth, lev - 1, t - 1) else "inactive"
                    )
                    reset = F(G0 + int(pi0) - G2, C2)
                    child_quota_total = 16 * rkids
                    assert lhs == reset + child_quota_total
                    points = botdesc_allocation_points.setdefault(ancestor_role, set())
                    points.add((reset, child_quota_total))
                    stats = botdesc_reset_summary.setdefault(
                        ancestor_role,
                        {"count": 0, "allocation_min": None,
                         "reset_min": None, "reset_max": None,
                         "child_quota_min": None, "child_quota_max": None})
                    stats["count"] += 1
                    for name, value, fn in (
                        ("allocation_min", lhs, min),
                        ("reset_min", reset, min), ("reset_max", reset, max),
                        ("child_quota_min", child_quota_total, min),
                        ("child_quota_max", child_quota_total, max)):
                        old_value = stats[name]
                        stats[name] = value if old_value is None else fn(old_value, value)

    print(f"depth={depth}, row_bits={row_bits}, DAG states={len(flow.nodes)}")
    print(f"distinct aligned triples at any one level max={max_level_triples}")
    print(f"mid-sender triples={counts['mid']}; G identity={counts['identity']}; "
          f"child-deficit updates={counts['child_deficit_update']}; "
          f"G(t)<=G(t-2)={counts['g_monotone']}; "
          f"previous unsaturated={counts['previous_unsaturated']}; "
          f"all children unsaturated={counts['children_unsaturated']}; "
          f"a/c>=63/64={counts['bound']}")
    print(f"minimum exact a/c={min_ratio}; minimum child-quota sum/C_child={min_child_quota}; "
          f"minimum quota term={min_quota_term}; minimum deficit-drop term="
          f"{min_deficit_drop}")
    print(f"minimum paired-cut decomposition terms, normalized by parent C: "
          f"{min_half_terms}")
    print(f"paired-cut carry+fresh minima by [child role, t-2 parent role]: "
          f"{dict(sorted(half_role_summary.items()))}")
    pareto = []
    best_fresh = None
    for carry, fresh in sorted(botdesc_pair_points):
        if best_fresh is None or fresh < best_fresh:
            pareto.append((carry, fresh))
            best_fresh = fresh
    min_pair_sum = min((carry + fresh for carry, fresh in botdesc_pair_points),
                       default=None)
    print(f"botDesc-to-botDesc [carry, fresh] distinct={len(botdesc_pair_points)}; "
          f"Pareto frontier={pareto}; min sum={min_pair_sum}")
    print(f"botDesc-to-botDesc intervening ancestor roles: "
          f"{dict(sorted(botdesc_ancestor_roles.items()))}")
    print(f"botDesc-to-botDesc allocation reset + child quotas by ancestor role: "
          f"{dict(sorted(botdesc_reset_summary.items()))}")
    for ancestor_role, points in sorted(botdesc_allocation_points.items()):
        frontier = []
        best_quota = None
        for reset, quota_sum in sorted(points):
            if best_quota is None or quota_sum < best_quota:
                frontier.append((reset, quota_sum))
                best_quota = quota_sum
        min_total = min(reset + quota_sum for reset, quota_sum in points)
        print(f"allocation [reset, child-quota] frontier for {ancestor_role}: "
              f"distinct={len(points)}, frontier={frontier}, min sum={min_total}")
    print(f"botDesc-to-botDesc endpoint-prefix reserve minima (1..4)="
          f"{botdesc_endpoint_prefix_min}")
    print(f"child roles [visits, unsaturated, positive capped]: {child_role_counts}")
    print(f"previous roles [visits, capped-or-empty, positive capped]: {previous_role_counts}")
    print(f"mid profile states={profile_counts['mid']}; componentwise floor margin="
          f"{min_profile_margin}; left/right cut-debt margins="
          f"{min_left_cut_margin}, {min_right_cut_margin}")
    print(f"paired-cut tightness by debt side [side, left tight, right tight]: "
          f"{dict(sorted(cut_tightness.items()))}")
    boundary_items = sorted(cut_boundary_exception_stages.items())
    print(f"boundary single-debt equality exceptions: "
          f"{sum(cut_boundary_exception_stages.values())} states at "
          f"{len(boundary_items)} stages; first/last stages="
          f"{boundary_items[:4]} / {boundary_items[-4:]}")
    assert counts["identity"] == counts["mid"]
    assert counts["child_deficit_update"] == counts["mid"]
    assert counts["g_monotone"] == counts["mid"]
    assert counts["bound"] == counts["mid"]
    assert profile_counts["allocation_identity"] == profile_counts["mid"]
    assert profile_counts["left_cut"] == profile_counts["mid"]
    assert profile_counts["right_cut"] == profile_counts["mid"]
    assert all(stats[side] >= F(63, 128)
               for stats in half_role_summary.values()
               for side in ("left_min_sum", "right_min_sum"))
    assert min_pair_sum is None or min_pair_sum >= F(63, 128)
    assert botdesc_endpoint_prefix_min[3] is None or botdesc_endpoint_prefix_min[3] >= 0


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=30)
    ap.add_argument("--row-bits", type=int, default=14)
    args = ap.parse_args()
    audit(args.depth, args.row_bits)


if __name__ == "__main__":
    main()
