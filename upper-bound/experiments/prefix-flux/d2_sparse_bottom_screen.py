#!/usr/bin/env python3
"""Finite screen for send-all-up repair of sparse-bottom D2 nodes.

This is an exploratory flow check only. It does not prove address purity,
local separator bounds, or a sorting theorem.
"""
import argparse
from collections import Counter
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par


def screen(depth: int, row_bits: int, params: tuple[int, int, int],
           cleanup_tail: int = 0) -> None:
    p = Par(*params)
    row_count = 1 << row_bits
    flow = FlowDAG(depth, scale=row_count, p=p, sparse_bottom=True).build()
    fringe_rows = []
    min_fringe_by_side = {}
    send_all = 0
    checked = 0
    min_quota_v2 = {}
    capped_by_role = {}
    min_alloc_over_cap = {}
    min_alloc_over_quota = {}
    canonical_mid_times = 0
    canonical_profiles = Counter()
    canonical_profile_exceptions = []
    canonical_sequence = []
    odd_sendall_by_role = {}
    odd_sendall_no_future_ordinary_by_role = {}
    odd_sendall_locations = {}
    future_ordinary = {}
    min_capped_ordinary_v2 = None
    provider_cutoff = max(0, len(flow.rows) - cleanup_tail)
    cleanup_max_allocation = 0
    cleanup_sender_classes = 0
    boundary_fringe = {}
    canonical_floor = (F(21, 512), *([F(7, 256)] * 6), F(21, 512))
    for t, step in enumerate(flow.rows):
        if params == (3, 2, 2) and t >= 2:
            lev = p.omega(depth, t) - 2
            if p.active(depth, lev, t) and p.role(depth, lev, t) == "mid":
                c = row_count * p.cap(depth, lev, t)
                index_one = flow.lookup(t, lev, 1)
                _, deficit, low, high, children = flow.nodes[index_one]
                profile = tuple(
                    F(flow.nodes[child][1], p.A * c) for child in children
                )
                assert (deficit, low, high) == (0, 0, 0), (
                    depth, t, lev, "index-1 canonical state", deficit, low, high
                )
                index_one_ratio = F(int(step[index_one][0]), c)
                assert index_one_ratio >= F(63, 64), (
                    depth, t, lev, index_one_ratio, profile
                )
                assert all(actual >= floor for actual, floor in
                           zip(profile, canonical_floor)), (
                    depth, t, lev, "index-1 child profile floor", profile
                )
                if profile != canonical_floor:
                    canonical_profile_exceptions.append((t, lev, index_one_ratio))
                canonical_profiles[(index_one_ratio, profile)] += 1
                canonical_sequence.append((t, p.omega(depth, t), profile))
                canonical = []
                for node, (a0, _, _) in step.items():
                    node_lev, deficit, low, high, children = flow.nodes[node]
                    if node_lev == lev and (deficit, low, high) == (0, 0, 0):
                        child_profile = tuple(
                            F(flow.nodes[child][1], p.A * c) for child in children
                        )
                        canonical.append((F(int(a0), c), child_profile))
                assert canonical, (depth, t, lev, "missing canonical mid state")
                assert all(a_ratio >= F(63, 64)
                           and p.A * sum(profile, F(0)) == a_ratio
                           and all(actual >= floor for actual, floor in
                                   zip(profile, canonical_floor))
                           for a_ratio, profile in canonical), (
                    depth, t, lev, canonical[:1]
                )
                canonical_mid_times += 1
        for node, (a0, pi0, blocks) in step.items():
            a, pi = int(a0), int(pi0)
            if t >= provider_cutoff and a:
                cleanup_sender_classes += 1
                cleanup_max_allocation = max(cleanup_max_allocation, a)
            checked += 1
            _, deficit, low, high, _ = flow.nodes[node]
            lev = flow.nodes[node][0]
            role = "topDesc" if t == 0 else p.role(depth, lev, t)
            planned = 0 if t == 0 else row_count * p.up(depth, lev, t)
            capped_ordinary = role != "botRise" and planned >= a
            if a and role in ("topRise", "mid"):
                assert planned < a, (depth, t, lev, role, a, planned)
            if a and capped_ordinary:
                capped_by_role[role] = capped_by_role.get(role, 0) + 1
                assert role == "botDesc", (depth, t, lev, role, a, planned)
            # Candidate induction lattice: live mass/deficit in m units;
            # stored cut offsets in m/2 units. Ordinary unsaturated quotas
            # lie in 2m units; botRise and send-all caps use pi=a.
            assert a % row_count == 0, (t, node, a)
            assert deficit % row_count == 0, (t, node, deficit)
            assert low % (row_count // 2) == 0, (t, node, low)
            assert high % (row_count // 2) == 0, (t, node, high)
            if role == "botRise":
                assert pi % row_count == 0, (t, node, pi)
            elif capped_ordinary:
                assert pi == a, (t, node, a, pi)
            else:
                assert pi % (2 * row_count) == 0, (t, node, pi)
            if role != "topDesc" and pi == a and a % (2 * row_count):
                key = (lev, t)
                if key not in future_ordinary:
                    future_ordinary[key] = any(
                        p.active(depth, lev, u)
                        and p.role(depth, lev, u) not in ("topDesc", "botRise")
                        for u in range(t + 1, len(flow.rows))
                    )
                assert not future_ordinary[key], (depth, t, lev, role, pi)
                odd_sendall_by_role[role] = odd_sendall_by_role.get(role, 0) + 1
                odd_sendall_no_future_ordinary_by_role[role] = (
                    odd_sendall_no_future_ordinary_by_role.get(role, 0) + 1
                )
                # The required phase condition is no later ordinary cut.
                # Record locations without asserting the former exact tail
                # formula, which fails at depth 150.
                assert role in ("botDesc", "botRise"), (depth, t, lev, role, a)
                odd_sendall_locations.setdefault(role, []).append((t, lev))
            if role not in ("topDesc", "botRise") and flow.nodes[node][4]:
                children = flow.nodes[node][4]
                child_mass = sum(flow.nodes[c][1] for c in children)
                left_front = low + pi // 2
                right_front = child_mass - high - pi // 2
                if pi == a:
                    assert left_front == right_front, (
                        t, node, role, left_front, right_front
                    )
                else:
                    assert left_front % row_count == 0, (t, node, role, left_front)
                    assert right_front % row_count == 0, (t, node, role, right_front)
            if not a:
                continue
            if pi and t < provider_cutoff:
                side = (
                    "both-positive" if low and high else
                    "low-only" if low else
                    "high-only" if high else
                    "zero-debt"
                )
                fringe = F(row_count * pi, 2 * a)
                witness = (fringe, t, lev, role, a, pi, deficit, low, high)
                if (side not in min_fringe_by_side
                        or fringe < min_fringe_by_side[side][0]):
                    min_fringe_by_side[side] = witness
            if t > 0:
                capacity = row_count * p.cap(depth, lev, t)
                ratio = F(a, capacity)
                min_alloc_over_cap[role] = min(
                    min_alloc_over_cap.get(role, ratio), ratio
                )
                if role == "topRise":
                    assert ratio >= 1, (depth, t, lev, role, ratio)
                if role == "mid":
                    assert ratio >= F(63, 64), (depth, t, lev, role, ratio)
                if role != "botRise" and planned:
                    quota_ratio = F(a, planned)
                    min_alloc_over_quota[role] = min(
                        min_alloc_over_quota.get(role, quota_ratio), quota_ratio
                    )
            assert all(int(b) >= 0 for b in blocks), (t, node, blocks)
            assert sum(map(int, blocks)) + pi == a, (t, node, a, pi, blocks)
            if not pi:
                continue
            fringe = F(row_count * pi, 2 * a)
            if t > 0 and role == "mid" and lev == p.omega(depth, t) - 2:
                c = row_count * p.cap(depth, lev, t)
                side = "high-only" if high and not low else (
                    "low-only" if low and not high else
                    "both-positive" if low and high else "zero-debt"
                )
                key = (t, side)
                sample = (fringe, F(a, c), a, pi, deficit, low, high)
                if key not in boundary_fringe or fringe < boundary_fringe[key][0]:
                    boundary_fringe[key] = sample
            if t < provider_cutoff:
                fringe_rows.append(fringe)
            if pi:
                v2 = (pi & -pi).bit_length() - 1
                min_quota_v2[role] = min(min_quota_v2.get(role, v2), v2)
            if capped_ordinary:
                v2 = (a & -a).bit_length() - 1
                min_capped_ordinary_v2 = (
                    v2 if min_capped_ordinary_v2 is None
                    else min(min_capped_ordinary_v2, v2)
                )
                send_all += 1

    boundary_transition_counts = Counter()
    if params == (3, 2, 2):
        if canonical_sequence:
            assert canonical_sequence[0][2] == canonical_floor, (
                depth, canonical_sequence[0]
            )
        for first, second in zip(canonical_sequence, canonical_sequence[1:]):
            t0, omega0, profile0 = first
            t1, omega1, profile1 = second
            if t1 != t0 + 1:
                continue
            delta = omega1 - omega0
            assert delta in (-1, 1), (depth, t0, omega0, omega1)
            if delta == 1:
                assert all(after >= before for before, after in
                           zip(profile0, profile1)), (
                    depth, t0, omega0, profile0, profile1
                )
            else:
                assert profile1 == canonical_floor, (
                    depth, t0, omega0, profile0, profile1
                )
            boundary_transition_counts[delta] += 1

    terminal_native = [
        flow.native(flow.nodes[node][0])
        for node in flow.reachable(len(flow.rows))
        if flow.allocation(node) > 0
    ]
    stage_rate = F(p.x + p.y, p.x * p.z)
    bitonic = row_bits * (row_bits + 1) // 2
    core_depth = 3 * bitonic
    min_fringe = min(fringe_rows) if fringe_rows else "n/a"
    max_fringe = max(fringe_rows) if fringe_rows else "n/a"
    print(f"params={params}, depth={depth}, rows=2^{row_bits}, "
          f"stages={len(flow.rows)}, states={len(flow.nodes)}")
    print(f"active node-classes={checked}, capped send-all classes={send_all}, "
          f"provider stages=[0,{provider_cutoff}), min fringe rows={min_fringe}, "
          f"max fringe rows={max_fringe}")
    if cleanup_tail:
        sorter_log = max(0, (cleanup_max_allocation - 1).bit_length())
        print(f"exact-sort cleanup stages=[{provider_cutoff},{len(flow.rows)}), "
              f"sender classes={cleanup_sender_classes}, max bag={cleanup_max_allocation}, "
              f"padded bitonic depth<={sorter_log * (sorter_log + 1) // 2}")
    print(f"positive capped ordinary classes by role={capped_by_role}")
    print(f"minimum allocation/capacity by role={min_alloc_over_cap}")
    print(f"minimum allocation/planned-quota by ordinary role="
          f"{min_alloc_over_quota}")
    print("minimum fringe witness by cut-debt side "
          "(fringe, stage, level, role, allocation, quota, G, low, high):")
    for side, witness in sorted(min_fringe_by_side.items()):
        print(f"  {side}: {witness}")
    print("boundary omega-2 mid minimum fringe by stage (last 30 stages):")
    for (t, side), sample in sorted(boundary_fringe.items()):
        if t >= max(0, len(flow.rows) - 30):
            fringe, ratio, a, pi, deficit, low, high = sample
            print(f"  t={t:>4} {side:>12}: f={fringe}, a/c={ratio}, "
                  f"a={a}, pi={pi}, G={deficit}, low={low}, high={high}")
    if params == (3, 2, 2):
        print(f"canonical zero-deficit omega-2 mid states checked="
              f"{canonical_mid_times}")
        if canonical_profiles:
            ratios = [ratio for ratio, _ in canonical_profiles]
            print(f"canonical index-1 profile types={len(canonical_profiles)}, "
                  f"a/c range=({min(ratios)}, {max(ratios)})")
        print(f"boundary-profile transitions checked="
              f"{sum(boundary_transition_counts.values())} "
              f"by omega delta={dict(boundary_transition_counts)}")
        if canonical_profile_exceptions:
            stages = [t for t, _, _ in canonical_profile_exceptions]
            print(f"nonminimal boundary profiles={len(stages)} "
                  f"(stages {min(stages)}..{max(stages)})")
    print(f"minimum nonzero quota 2-adic valuation by role={min_quota_v2}")
    print(f"odd-m send-all classes by role={odd_sendall_by_role}")
    print("odd-m send-all classes with no later ordinary cut by role="
          f"{odd_sendall_no_future_ordinary_by_role}")
    print(f"odd-m send-all locations by role={odd_sendall_locations}")
    print(f"minimum v2 of capped ordinary allocations="
          f"{min_capped_ordinary_v2}")
    print(f"three-sort core={core_depth}, stage/log={stage_rate}, "
          f"conditional coefficient={core_depth * stage_rate}")
    max_native = max(terminal_native, default=1)
    print(f"max terminal native bits={(max_native - 1).bit_length()}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=50)
    ap.add_argument("--row-bits", type=int, default=14)
    ap.add_argument("--params", type=int, nargs=3, default=(3, 2, 2))
    ap.add_argument("--cleanup-tail", type=int, default=0,
                    help="screen the last L stages for replacement by exact local bag sorts")
    args = ap.parse_args()
    screen(args.depth, args.row_bits, tuple(args.params), args.cleanup_tail)


if __name__ == "__main__":
    main()
