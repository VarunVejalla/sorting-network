#!/usr/bin/env python3
"""Finite D2 screen for the static crossing-mass term in local area bounds.

At each stage, only one native interval per level can contain the global
threshold q. For that active sender, `min(P_B, a_B-P_B)` counts the static
zeros/ones mixture in its bag, where P_B is the number of bag wires below q.
All other senders have this structural term zero. This is a finite flow
diagnostic, not an all-depth schedule proof or a sorting bound.
"""
import argparse
from fractions import Fraction

from flow_dag import FlowDAG
from oracle import Par


def screen(depth=30, scale=8192, params=(3, 3, 2), threshold=Fraction(1, 3),
           audit_schedule_allocation=False):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    N = flow.p.k**depth * scale
    q = (threshold.numerator * N) // threshold.denominator
    stages = []
    schedule_caps = []

    for t, row in enumerate(flow.rows):
        crossing_mass = crossing_bags = 0
        formula_cap_sum = Fraction(0)
        for lev in range(depth + 1):
            active = (lev == 0 if t == 0 else flow.p.active(depth, lev, t))
            if not active:
                continue
            formula_cap_sum += Fraction(flow.p.alloc(depth, lev, t))
            native = flow.native(lev)
            idx = q // native
            node = flow.lookup(t, lev, idx)
            if node not in row:
                continue
            allocation = flow.allocation(node)
            if allocation <= 0:
                continue
            intervals = flow.bag_intervals(node, idx)
            P = sum(max(0, min(hi, q) - lo) for lo, hi in intervals)
            minority = min(P, allocation - P)
            if minority:
                crossing_mass += minority
                crossing_bags += 1
        stages.append((t, crossing_mass, crossing_bags))
        schedule_caps.append(formula_cap_sum)

    assert all(0 <= mass <= N for _, mass, _ in stages)
    allocation_audit = None
    if audit_schedule_allocation:
        worst = (Fraction(0), None)
        checked = 0
        zero_cap_violations = []
        for t, row in enumerate(flow.rows):
            for node in flow.reachable(t):
                lev = flow.nodes[node][0]
                active = (lev == 0 if t == 0 else
                          flow.p.active(depth, lev, t))
                if not active or node not in row:
                    continue
                actual = Fraction(flow.allocation(node), scale)
                formula = Fraction(flow.p.alloc(depth, lev, t))
                if formula == 0:
                    if actual:
                        zero_cap_violations.append((t, lev, actual))
                    continue
                checked += 1
                ratio = actual / formula
                if ratio > worst[0]:
                    worst = (ratio, (t, lev))
        allocation_audit = (checked, worst, zero_cap_violations)
        recurrence_cases = {-1: 0, 1: 0, 3: 0}
        for t in range(2, len(schedule_caps) - 3):
            alpha = flow.p.alpha(depth, t)
            alpha_next = flow.p.alpha(depth, t + 3)
            delta = alpha_next - alpha
            omega = flow.p.omega(depth, t)
            assert flow.p.omega(depth, t + 3) == omega + 1
            assert delta in recurrence_cases
            recurrence_cases[delta] += 1
            c_alpha = Fraction(flow.p.cap(depth, alpha, t))
            if delta == -1:
                assert alpha == 1
                correction = Fraction(63, 32768) * c_alpha
            elif delta == 1:
                correction = Fraction(0)
            else:
                assert omega - alpha >= 4
                correction = -Fraction(63, 512) * c_alpha
            assert schedule_caps[t + 3] == schedule_caps[t] / 8 + correction
        if len(schedule_caps) > 4:
            assert schedule_caps[3] / schedule_caps[0] == Fraction(79, 8192)
            assert schedule_caps[4] / schedule_caps[1] == Fraction(4159, 32768)
        allocation_audit += (recurrence_cases,)
    return N, stages, schedule_caps, allocation_audit


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=30)
    parser.add_argument("--scale", type=int, default=8192)
    parser.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    parser.add_argument("--threshold", default="1/3")
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument("--all-stages", action="store_true")
    parser.add_argument("--audit-schedule-allocation", action="store_true",
                        help="compare every reachable sender type with Par.alloc")
    args = parser.parse_args()
    N, stages, schedule_caps, allocation_audit = screen(
        args.depth, args.scale, tuple(args.params), Fraction(args.threshold),
        args.audit_schedule_allocation
    )
    print(f"depth={args.depth} N_bits={N.bit_length()} stages={len(stages)}")
    chosen = stages if args.all_stages else sorted(
        stages, key=lambda entry: entry[1], reverse=True
    )[:args.top]
    for t, mass, bags in chosen:
        if mass:
            print(f"t={t} crossing_mass={mass} ratio={mass/N:.12g} bags={bags}")
    total = sum(mass for _, mass, _ in stages)
    print(f"max_stage_ratio={max(mass for _, mass, _ in stages)/N:.12g}")
    print(f"sum_stage_ratio={total/N:.12g}")
    by_stage = {t: mass for t, mass, _ in stages}
    period_ratios = [(Fraction(by_stage[t + 3], mass), t)
                     for t, mass, _ in stages
                     if mass and by_stage.get(t + 3, 0)]
    if period_ratios:
        ratio, t = max(period_ratios)
        print(f"max_C[t+3]/C[t]={float(ratio):.12g} at t={t}; "
              f"exact={ratio}")
    cap_ratios = [(schedule_caps[t + 3] / cap, t)
                  for t, cap in enumerate(schedule_caps[:-3])
                  if cap and schedule_caps[t + 3]]
    if cap_ratios:
        ratio, t = max(cap_ratios)
        print(f"max_Par.alloc_sum[t+3]/sum[t]={float(ratio):.12g} at t={t}; "
              f"exact={ratio}")
    if allocation_audit is not None:
        checked, (ratio, where), zero_violations, recurrence_cases = allocation_audit
        print(f"schedule-allocation-types={checked} "
              f"max_actual_over_Par.alloc={float(ratio):.12g} at={where}; "
              f"exact={ratio}; zero-cap-violations={len(zero_violations)}")
        print(f"exact_three_stage_sum_recurrence_cases={recurrence_cases}")
