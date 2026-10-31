#!/usr/bin/env python3
"""Exact SMT feasibility gate for a large output range in the cyclic core."""
import argparse
from math import gcd
import time

import z3


def solve(n=64, a=1, b=35, offset=17, threshold=20, timeout_ms=120000,
          delta=None, fixed_q=None, third_slope=None, third_offset=0):
    slopes = [a, b] + ([] if third_slope is None else [third_slope])
    if any(gcd(slope, n) != 1 for slope in slopes):
        raise ValueError("all slopes must be coprime to the column count")
    ia, ib = pow(a, -1, n), pow(b, -1, n)
    t = [z3.Int(f"t_{j}") for j in range(n)]
    q = z3.Int("q")
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(q >= 0, q < n)
    if fixed_q is not None:
        if not 0 <= fixed_q < n:
            raise ValueError("fixed_q must be in 0,...,n-1")
        solver.add(q == fixed_q)
    for value in t:
        solver.add(value >= 0, value < n)
    R = [z3.Sum([z3.If(((ia * (c - j)) % n) < t[j], 1, 0)
                 for j in range(n)]) for c in range(n)]
    residues = [(q + R[c]) % n for c in range(n)]
    S = [z3.Sum([z3.If(((ib * (d - c - offset)) % n) < residues[c], 1, 0)
                 for c in range(n)]) for d in range(n)]
    profile = S
    if third_slope is not None:
        ic = pow(third_slope, -1, n)
        second_quotient_sum = z3.Sum([(q + R[c]) / n for c in range(n)])
        second_residues = [(second_quotient_sum + S[c]) % n
                           for c in range(n)]
        profile = [z3.Sum([
            z3.If(((ic * (d - c - third_offset)) % n) < second_residues[c],
                  1, 0)
            for c in range(n)]) for d in range(n)]

    if delta is None:
        high_index, low_index = z3.Int("high_index"), z3.Int("low_index")
        high, low = z3.Int("high"), z3.Int("low")
        solver.add(high_index >= 0, high_index < n,
                   low_index >= 0, low_index < n)
        solver.add(high == z3.Sum([z3.If(high_index == d, profile[d], 0)
                                   for d in range(n)]))
        solver.add(low == z3.Sum([z3.If(low_index == d, profile[d], 0)
                                  for d in range(n)]))
        solver.add(high - low >= threshold)
    else:
        if not 1 <= delta < n:
            raise ValueError("delta must be in 1,...,n-1")
        # Rotation equivariance lets the high output position be fixed at0.
        solver.add(profile[0] - profile[delta] >= threshold)

    start = time.perf_counter()
    result = solver.check()
    report = {"n": n, "a": a, "b": b, "offset": offset,
              "third_slope": third_slope, "third_offset": third_offset,
              "threshold": threshold, "result": str(result),
              "seconds": time.perf_counter() - start,
              "reason_unknown": solver.reason_unknown() if result == z3.unknown else None}
    if result == z3.sat:
        model = solver.model()
        tv = [model.eval(value).as_long() for value in t]
        qv = model.eval(q).as_long()
        output = [model.eval(value).as_long() for value in profile]
        report.update({"q": qv, "range": max(output) - min(output),
                       "input_residues": tv, "output_profile": output})
    return report


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--first-slope", type=int, default=1)
    ap.add_argument("--second-slope", type=int, default=35)
    ap.add_argument("--offset", type=int, default=17)
    ap.add_argument("--threshold", type=int, default=20)
    ap.add_argument("--delta", type=int,
                    help="fix the low output at this offset from the high output")
    ap.add_argument("--fixed-q", type=int,
                    help="fix the shared first-round quotient residue")
    ap.add_argument("--third-slope", type=int,
                    help="add a third cyclic shuffle/sort round")
    ap.add_argument("--third-offset", type=int, default=0)
    ap.add_argument("--timeout-ms", type=int, default=120000)
    args = ap.parse_args()
    print(solve(args.columns, args.first_slope, args.second_slope,
                args.offset, args.threshold, args.timeout_ms,
                args.delta, args.fixed_q, args.third_slope,
                args.third_offset), flush=True)
