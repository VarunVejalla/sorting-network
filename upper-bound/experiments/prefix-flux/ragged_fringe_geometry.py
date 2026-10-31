#!/usr/bin/env python3
"""Finite exact screen for heterogeneous 13-row D2 separator columns.

Given a sender with `a` wires and `pi` up wires, seek n columns with per-column
fringe f_j >= 13 and bulk group count b_j >= 0 such that
  a = sum_j (2*f_j + 64*b_j), pi = 2*sum_j f_j,
  and every column height 2*f_j + 64*b_j <= 8192.
This is a shape-feasibility screen only; it does not prove the local provider
works for heterogeneous columns or that the resulting networks sort globally.
"""
import argparse
from collections import Counter


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def realize(a: int, pi: int, rows: int = 8192, tail: int = 13,
            groups: int = 64, min_columns: int = 16):
    """Return a constructive integer column realization, or a failure tag."""
    if pi % 2:
        return "odd-up"
    F = pi // 2
    remainder = a - pi
    if remainder < 0 or remainder % groups:
        return "bulk-divisibility"
    B = remainder // groups

    # Each column contributes b_j <= floor((rows-2*f_j)/groups).
    # Since f_j >= tail, b_j <= 127 for rows=8192, tail=13.
    bmax = (rows - 2 * tail) // groups
    n = max(min_columns, ceil_div(B, bmax),
            ceil_div(F + (groups // 2) * B,
                     rows // 2))
    # The closed-form lower bound above is intentionally followed by exact
    # construction/checks, so a mistaken bound cannot yield a false pass.
    if F < tail * n:
        return ("too-few-fringe", F, B, n)
    q, r = divmod(B, n)
    fq, fr = divmod(F, n)
    # The balanced construction sorts b_j increasingly and f_j decreasingly.
    # Both sequences have only two values, so their joint profile is the
    # overlap of four index intervals and can be checked without O(n) memory.
    f_ranges = ((fq + 1, 0, fr), (fq, fr, n))
    b_ranges = ((q, 0, n - r), (q + 1, n - r, n))
    profile = Counter()
    for fj, flo, fhi in f_ranges:
        for bj, blo, bhi in b_ranges:
            count = max(0, min(fhi, bhi) - max(flo, blo))
            if count:
                profile[(fj, bj)] += count
    if max((bj for _, bj in profile), default=0) > bmax:
        return ("bulk-per-column", F, B, n,
                max((bj for _, bj in profile), default=0))
    if F < tail * n:
        return ("too-few-fringe", F, B, n)
    if any(fj < tail for fj, _ in profile):
        return ("too-few-fringe", F, B, n)
    if any(fj > rows // 2 - groups // 2 * bj for fj, bj in profile):
        return ("balanced-fringe-fit", F, B, n, profile)
    heights = {2 * fj + groups * bj for fj, bj in profile}
    if 2 * F + groups * B != a:
        return ("sum-check", F, B, n)
    if max(heights, default=0) > rows:
        return ("range-check", F, B, n, max(heights))
    fcounts = Counter()
    bcounts = Counter()
    for (fj, bj), count in profile.items():
        fcounts[fj] += count
        bcounts[bj] += count
    fmin = min(fcounts, default=tail)
    fmax = max(fcounts, default=tail)
    hmin = min(heights, default=0)
    hmax = max(heights, default=0)
    if sum(fj * count for fj, count in fcounts.items()) != F:
        return ("sum-check", F, B, n)
    if sum(bj * count for bj, count in bcounts.items()) != B:
        return ("sum-check", F, B, n)
    return n, fmin, fmax, hmin, hmax, fcounts, bcounts, profile


def port_misalignment(profile: Counter, rows: int = 8192, groups: int = 64):
    """Exact cell symmetric differences from the majority column type.

    Each live column is a suffix of height 2*f + groups*b.  The returned
    boundary error compares the cumulative live prefix after the lower fringe
    and q middle groups with one uniform row cut.  The port error compares an
    individual q-th middle group with the corresponding uniform row band.
    """
    ref_f, ref_b = max(profile, key=profile.get)

    def cut(f: int, b: int, q: int) -> int:
        return rows - f - (groups - q) * b

    boundary_errors = []
    port_errors = []
    for q in range(groups + 1):
        ref_cut = cut(ref_f, ref_b, q)
        boundary_errors.append(sum(
            count * abs(cut(f, b, q) - ref_cut)
            for (f, b), count in profile.items()
        ))
    for q in range(1, groups + 1):
        ref_lo, ref_hi = cut(ref_f, ref_b, q - 1), cut(ref_f, ref_b, q)
        mismatch = 0
        for (f, b), count in profile.items():
            lo, hi = cut(f, b, q - 1), cut(f, b, q)
            overlap = max(0, min(hi, ref_hi) - max(lo, ref_lo))
            mismatch += count * ((hi - lo) + (ref_hi - ref_lo) - 2 * overlap)
        port_errors.append(mismatch)
    return (max(boundary_errors), boundary_errors.index(max(boundary_errors)),
            max(port_errors), port_errors.index(max(port_errors)) + 1,
            (ref_f, ref_b))


def audit(a: int, pi: int, rows: int, tail: int) -> None:
    result = realize(a, pi, rows=rows, tail=tail)
    if isinstance(result, tuple) and isinstance(result[0], str):
        raise SystemExit(f"no realization: {result}")
    n, fmin, fmax, hmin, hmax, fringe_counts, bulk_counts, profile = result
    print(f"a={a}; up={pi}; down-groups={(a-pi)//64}; rows={rows}; tail>={tail}")
    print(f"columns={n}; fringe range=[{fmin},{fmax}]; height range=[{hmin},{hmax}]")
    print(f"fringe multiplicities={dict(sorted(fringe_counts.items()))}")
    print(f"bulk-group multiplicities={dict(sorted(bulk_counts.items()))}")
    boundary_err, boundary_q, port_err, port_q, ref_type = port_misalignment(
        profile, rows=rows, groups=64
    )
    print(f"majority reference column type={ref_type}; maximum cumulative-cut "
          f"misalignment={boundary_err} cells at q={boundary_q}")
    print(f"maximum single-port symmetric difference={port_err} cells "
          f"at group={port_q}")
    print(f"exact sums: 2*sum(f)={2*sum(k*v for k,v in fringe_counts.items())}; "
          f"sum(64*b_j+2*f_j)={a}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--a", type=int, default=67764224)
    ap.add_argument("--up", type=int, default=245760)
    ap.add_argument("--rows", type=int, default=8192)
    ap.add_argument("--tail", type=int, default=13)
    args = ap.parse_args()
    audit(args.a, args.up, args.rows, args.tail)


if __name__ == "__main__":
    main()
