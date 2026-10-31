#!/usr/bin/env python3
"""Bit-vector feasibility search for a large range in a cyclic core.

All counts use bounded bit-vectors, so modulo-64 residue extraction is a
literal low-bit operation rather than nonlinear integer div/mod.
"""
import argparse
import json
from math import gcd

import z3


def count(bits, width):
    zero, one = z3.BitVecVal(0, width), z3.BitVecVal(1, width)
    total = zero
    for bit in bits:
        total = total + z3.If(bit, one, zero)
    return total


def interval_coverage_endpoint(residues, n, width):
    """Encode cyclic interval coverage by its endpoint histogram."""
    k = n.bit_length() - 1
    endpoints = [(z3.BitVecVal(j, k) + residues[j]) for j in range(n)]
    start_zero = count([
        z3.UGT(residues[j], z3.BitVecVal((-j) % n, k))
        for j in range(n)
    ], width)
    values = [start_zero]
    for x in range(1, n):
        ends_here = count([
            endpoint == z3.BitVecVal(x, k) for endpoint in endpoints
        ], width)
        values.append(values[-1] + z3.BitVecVal(1, width) - ends_here)
    return values


def solve(n=64, slopes=(1, 35, 17), offsets=(0, 0, 0), delta=1,
          min_range=20, timeout_ms=60000, all_separations=False,
          endpoint_encoding=False):
    if n < 2 or n & (n - 1):
        raise ValueError("columns must be a power of two")
    if len(slopes) < 2 or len(offsets) != len(slopes):
        raise ValueError("provide matching lists of at least two slopes/offsets")
    if any(gcd(a, n) != 1 for a in slopes):
        raise ValueError("each slope must be coprime to the column count")
    if not 1 <= delta < n:
        raise ValueError("delta must be in 1,...,n-1")
    k = n.bit_length() - 1
    cw = k + 1
    inv = [pow(a, -1, n) for a in slopes]
    t = [z3.BitVec(f"t_{j}", k) for j in range(n)]
    q = z3.BitVec("q", k)
    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=timeout_ms)
    residues = t
    base = q
    final = None
    for stage, (slope_inv, offset) in enumerate(zip(inv, offsets)):
        residual = []
        if endpoint_encoding:
            slope = slopes[stage]
            transformed = [residues[(slope * x - offset) % n]
                           for x in range(n)]
            coverage = interval_coverage_endpoint(transformed, n, cw)
            residual = [None] * n
            for x, value in enumerate(coverage):
                residual[(slope * x) % n] = value
        else:
            for d in range(n):
                residual.append(count([
                    z3.UGT(residues[c], z3.BitVecVal(
                        (slope_inv * (d - c - offset)) % n, k))
                    for c in range(n)], cw))
        final = residual
        if stage + 1 < len(slopes):
            sums = [z3.ZeroExt(1, base) + value for value in residual]
            residues = [z3.Extract(k - 1, 0, value) for value in sums]
            carries = [z3.Extract(k, k, value) == z3.BitVecVal(1, 1)
                       for value in sums]
            # The true common quotient may differ by a multiple of n. Its
            # residue is all later rounds need, so truncate this carry sum.
            base = z3.Extract(k - 1, 0, count(carries, cw))
    if all_separations:
        # The cyclic transition is translation-equivariant in the column
        # index, so any witness can be rotated until a maximum is at 0.
        layer = final
        while len(layer) > 1:
            layer = [z3.If(z3.ULT(layer[i], layer[i + 1]),
                           layer[i], layer[i + 1])
                     for i in range(0, len(layer) - 1, 2)] + (
                         layer[-1:] if len(layer) % 2 else [])
        minimum = layer[0]
        solver.add(z3.UGE(
            final[0], minimum + z3.BitVecVal(min_range, cw)))
    else:
        solver.add(z3.UGE(final[0], final[delta] + z3.BitVecVal(min_range, cw)))
    result = solver.check()
    report = {"columns": n, "slopes": list(slopes),
              "offsets": list(offsets), "delta": delta,
              "min_range": min_range, "all_separations": all_separations,
              "endpoint_encoding": endpoint_encoding,
              "result": str(result)}
    if result == z3.unknown:
        report["reason_unknown"] = solver.reason_unknown()
    if result == z3.sat:
        model = solver.model()
        residues = [model.eval(v).as_long() for v in t]
        qvalue = model.eval(q).as_long()
        report.update({"q": qvalue, "input_residues": residues})
        # Reconstruct a row-height 512 representative and independently
        # recompute all rounds in unbounded Python integers.
        quotas = [0] * n
        remaining = qvalue
        for j, residue in enumerate(residues):
            cap = (512 - residue) // n
            take = min(cap, remaining)
            quotas[j] = take
            remaining -= take
        if remaining:
            raise AssertionError("512-row representative capacity failed")
        profile = [n * quotas[j] + residues[j] for j in range(n)]
        for a, b in zip(slopes, offsets):
            base = sum(h // n for h in profile)
            rem = [h % n for h in profile]
            profile = [base + sum(
                (((pow(a, -1, n) * (d - c - b)) % n) < rem[c])
                for c in range(n)) for d in range(n)]
        actual_range = max(profile) - min(profile)
        report.update({"checked_range": actual_range,
                       "output_profile": profile,
                       "witness_checks": actual_range >= min_range})
        if actual_range < min_range:
            raise AssertionError("bit-vector witness failed direct recomputation")
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--slopes", type=int, nargs="+", default=(1, 35, 17))
    ap.add_argument("--offsets", type=int, nargs="+", default=(0, 0, 0))
    ap.add_argument("--delta", type=int, default=1)
    ap.add_argument("--min-range", type=int, default=20)
    ap.add_argument("--timeout-ms", type=int, default=60000)
    ap.add_argument("--all-separations", action="store_true",
                    help="search for any output pair separated by min-range")
    ap.add_argument("--endpoint-encoding", action="store_true",
                    help="encode each cyclic interval sum via endpoint counts")
    args = ap.parse_args()
    print(json.dumps(solve(args.columns, args.slopes, args.offsets,
                           args.delta, args.min_range, args.timeout_ms,
                           args.all_separations, args.endpoint_encoding),
                     separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
