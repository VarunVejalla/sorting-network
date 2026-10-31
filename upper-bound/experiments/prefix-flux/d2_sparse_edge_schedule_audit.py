#!/usr/bin/env python3
"""Schedule-only case audit for the sparse-bottom (3,2,2) edge-floor proof."""
import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F

from oracle import Par


def audit(max_depth: int) -> tuple[Counter, list, F | None]:
    p = Par(3, 2, 2)
    cases = Counter()
    failures = []
    min_startup_native = None
    for depth in range(3, max_depth + 1):
        tf = p.tf(depth)
        active_history = [[] for _ in range(depth + 2)]
        for stage in range(1, tf + 1):
            lo, hi = p.alpha(depth, stage), p.omega(depth, stage)
            for level in range(max(1, lo), min(depth, hi) + 1):
                if level % 2 == stage % 2 and p.active(depth, level, stage):
                    active_history[level].append(
                        (stage, p.role(depth, level, stage)))
        for t in range(1, tf + 1):
            alpha, omega = p.alpha(depth, t), p.omega(depth, t)
            for level in range(max(1, alpha), min(depth, omega) + 1):
                if level % 2 != t % 2 or not p.active(depth, level, t):
                    continue
                role = p.role(depth, level, t)
                if role not in ("topRise", "mid", "botDesc"):
                    continue
                cases[role] += 1
                if role == "mid" and t >= 2:
                    prev_bot_desc = (
                        p.active(depth, level, t - 2)
                        and p.role(depth, level, t - 2) == "botDesc"
                    )
                    child_bot_desc = (
                        p.active(depth, level + 1, t - 1)
                        and p.role(depth, level + 1, t - 1) == "botDesc"
                    )
                    if prev_bot_desc and child_bot_desc:
                        parent_role = (
                            p.role(depth, level - 1, t - 1)
                            if p.active(depth, level - 1, t - 1) else "inactive"
                        )
                        cases[("mid-hard", "ancestor-" + parent_role)] += 1
                        if parent_role not in ("mid", "topRise"):
                            failures.append((depth, t, level,
                                             "unexpected hard-case ancestor role",
                                             parent_role))
                if p.active(depth, level, t - 1):
                    failures.append((depth, t, level, role, "parent active at t-1"))

                # For (k,A,nu)=(8,4,1/4), c(i+1,t-1)/c(i,t)=A/nu=16;
                # ordinary non-bottom and bottom-descending quotas are 7c/1024.
                native_exponent = 2 * t - 5 * level

                child_active = p.active(depth, level + 1, t - 1)
                child_role = (p.role(depth, level + 1, t - 1)
                              if child_active else None)
                if role in ("topRise", "mid"):
                    if child_role in ("mid", "botDesc"):
                        cases[(role, "child-" + child_role)] += 1
                    elif not child_active:
                        cases[(role, "startup-child") ] += 1
                        native_ratio = (F(2 ** native_exponent) if native_exponent >= 0
                                        else F(1, 2 ** -native_exponent))
                        min_startup_native = (native_ratio if min_startup_native is None
                                              else min(min_startup_native, native_ratio))
                        if native_ratio < F(7, 64):
                            failures.append((depth, t, level, role,
                                             "startup child native floor", native_ratio))
                    else:
                        failures.append((depth, t, level, role,
                                         "unexpected child role", child_role))
                else:
                    if child_role is None:
                        cases[(role, "child-inactive")] += 1
                        # The inactive child has never entered the schedule.
                        prior = bisect_left(active_history[level + 1], (t - 1, ""))
                        if prior:
                            failures.append((depth, t, level, role,
                                             "inactive child has prior activity",
                                             active_history[level + 1][prior - 1]))
                    elif child_role == "botRise":
                        cases[(role, "child-botRise")] += 1
                        if p.active(depth, level + 2, t - 1):
                            failures.append((depth, t, level, role,
                                             "grandchild active below botRise"))
                        # The botRise child and its grandchildren are virgin
                        # before this stage, so it sends zero and stays native.
                        prior = bisect_left(active_history[level + 1], (t - 1, ""))
                        if prior:
                            failures.append((depth, t, level, role,
                                             "botRise child has prior activity",
                                             active_history[level + 1][prior - 1]))
                        grandchild_prior = bisect_right(
                            active_history[level + 2], (t - 1, "\uffff"))
                        if grandchild_prior:
                            failures.append((depth, t, level, role,
                                             "botRise grandchild has prior activity",
                                             active_history[level + 2][grandchild_prior - 1]))
                    else:
                        failures.append((depth, t, level, role,
                                         "unexpected botDesc child role", child_role))
                    if native_exponent < -9:
                        failures.append((depth, t, level, role,
                                         "botDesc child native floor",
                                         native_exponent))
    return cases, failures, min_startup_native


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-depth", type=int, default=200)
    args = ap.parse_args()
    counts, failures, startup_floor = audit(args.max_depth)
    print(f"schedule cases through depth {args.max_depth}: {dict(counts)}")
    print(f"minimum startup native/parent capacity: {startup_floor}")
    print(f"violations: {len(failures)}")
    if failures:
        print("first violations:", failures[:10])
        raise SystemExit(1)
