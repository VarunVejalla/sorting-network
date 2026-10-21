#!/usr/bin/env python3
"""Necessary paper-level budget for a sorted-packet mixing stage.

This is not a network certificate. It instantiates the UB-25 L1 rounding
bound for a hypothetical 3-matching expander cycle and checks whether its
bulk error can fit the 36x UB-37 tolerance screen under the 789.75 scheduler.
"""
TARGET = 36 / 105_000  # optimistic UB-37 bulk-tolerance gate
DEPTH_CAP = 400        # 300 / (3/4), current R1 stage/log rate
MATCHINGS_PER_CYCLE = 3


def error_bound(q, cycles, rho):
    m = 1 << q
    return rho**cycles / 2 + MATCHINGS_PER_CYCLE / (2 * m * (1 - rho))


def rho_limit(q, cycles):
    lo, hi = 0.0, 0.999999
    for _ in range(100):
        mid = (lo + hi) / 2
        if error_bound(q, cycles, mid) <= TARGET:
            lo = mid
        else:
            hi = mid
    return lo if error_bound(q, cycles, lo) <= TARGET else None


print(f"optimistic target={TARGET:.9g}; stage depth cap={DEPTH_CAP}")
print("q packet_height rounds cycles depth coefficient rho_max rho_floor gate")
for q in range(10, 19):
    rounds = DEPTH_CAP // (q + 1)
    cycles = rounds // MATCHINGS_PER_CYCLE
    if cycles == 0:
        continue
    used_rounds = cycles * MATCHINGS_PER_CYCLE
    depth = used_rounds * (q + 1)
    rho = rho_limit(q, cycles)
    rho_floor = 2 ** (-MATCHINGS_PER_CYCLE / 2)
    if rho is None:
        rho_text, gate = "none", "rounding"
    elif rho < rho_floor:
        rho_text, gate = f"{rho:.6f}", "support-impossible"
    else:
        rho_text, gate = f"{rho:.6f}", "possible"
    print(f"{q:2d} {1<<q:13d} {used_rounds:6d} {cycles:6d} {depth:5d} "
          f"{depth*0.75:11.3f} {rho_text:>8s} {rho_floor:.6f} {gate}")
