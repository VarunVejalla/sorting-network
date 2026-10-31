#!/usr/bin/env python3
"""Finite exact geometry screen for uniform Chvatal flow (x,y,z)=(3,2,2)."""
import argparse
from collections import Counter
from fractions import Fraction as F

from oracle import Par


SCALE = 1 << 14
GEOMETRY = {
    "topDesc": (8, 0, 1),
    "topRise": (8192, 32, 1016),
    "mid": (8184, 28, 1016),
    "botDesc_1": (8184, 28, 1016),
    "botDesc_1/2": (8176, 56, 1008),
    "botDesc_1/4": (4080, 56, 496),
    "botDesc_1/8": (8128, 224, 960),
    "botDesc_1/16": (8064, 448, 896),
    "botDesc_1/32": (7936, 896, 768),
    "botDesc_1/64": (7680, 1792, 512),
}


def check(depth, delta=F(1, 10**5)):
    p = Par(3, 2, 2)
    counts, minimum_columns, zero_support = Counter(), {}, Counter()
    bottom_ratios = set()
    max_bits = 0
    for d in range(3, depth + 1):
        for t in range(p.tf(d)):
            for i in range(d + 1):
                active = (i == 0) if t == 0 else p.active(d, i, t)
                if not active:
                    continue
                role = "topDesc" if t == 0 else p.role(d, i, t)
                a = p.alloc(d, i, t)
                up, down = p.up(d, i, t, a), p.down(d, i, t)
                aa, uu, dd = SCALE * a, SCALE * up, SCALE * down
                if role == "botRise":
                    assert uu == aa and dd == 0
                    counts["botRise_bypass"] += 1
                    continue
                geom_role = role
                if role == "botDesc":
                    native_over_cap = F(p.k ** (d - i), 1) / p.cap(d, i, t)
                    bottom_ratios.add(native_over_cap)
                    geom_role = f"botDesc_{native_over_cap}"
                m, f, b = GEOMETRY[geom_role]
                assert m == 2 * f + p.k * b
                assert aa.denominator == uu.denominator == dd.denominator == 1
                assert aa % m == 0, (d, t, i, geom_role, aa, m)
                n = aa // m
                assert n >= 16, (d, t, i, geom_role, n)
                assert uu == 2 * f * n, (d, t, i, geom_role, uu, f, n)
                assert dd == b * n, (d, t, i, geom_role, dd, b, n)
                assert aa == uu + p.k * dd
                counts[geom_role] += 1
                minimum_columns[geom_role] = min(minimum_columns.get(geom_role, n), n)
                max_bits = max(max_bits, (m - 1).bit_length())
                if f and delta * f * n < 1:
                    zero_support[geom_role] += 1
    assert bottom_ratios == {F(1, 2**j) for j in range(7)}, bottom_ratios
    return counts, minimum_columns, zero_support, max_bits


def bottom_period_certificate():
    """Exact ten-residue reduction for bottom roles, matching the paper note."""
    p = Par(3, 2, 2)
    rows = []
    for t in range(2, 12):
        omega = p.omega(3, t)
        threshold = -((-(2 * t - 2 * omega + 14)) // 3)
        d0 = max(3, omega, threshold)
        assert p.alpha(d0, t) < omega
        role = p.role(d0, omega, t)
        exponent = 2 * t - 5 * omega + 3
        if role == "botRise":
            rows.append((t, omega, d0, 3 * d0 + 2 * omega - 2 * t - 3,
                         exponent, role, None))
        else:
            residue = F(2**exponent) if exponent >= 0 else F(1, 2**(-exponent))
            geom_role = f"botDesc_{residue}"
            m, _, _ = GEOMETRY[geom_role]
            scaled_a = SCALE * p.alloc(d0, omega, t)
            assert scaled_a % m == 0
            n = scaled_a // m
            rows.append((t, omega, d0, 3 * d0 + 2 * omega - 2 * t - 3,
                         exponent, geom_role, n))
        assert p.omega(3, t + 10) == omega + 4
        d1 = max(3, p.omega(3, t + 10),
                 -((-(2 * (t + 10) - 2 * p.omega(3, t + 10) + 14)) // 3))
        assert d1 == d0 + 4
        assert 3 * d1 + 2 * p.omega(3, t + 10) - 2 * (t + 10) - 3 == rows[-1][3]
        assert p.role(d1, p.omega(3, t + 10), t + 10) == role
        if rows[-1][6] is not None:
            m = GEOMETRY[rows[-1][5]][0]
            assert SCALE * p.alloc(d1, p.omega(3, t + 10), t + 10) // m == rows[-1][6]
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--depth", type=int, default=100)
    ap.add_argument("--delta", default="1/100000")
    args = ap.parse_args()
    delta = F(args.delta)
    counts, minimum_columns, zero_support, bits = check(args.depth, delta)
    period_rows = bottom_period_certificate()
    local_depth = 3 * bits * (bits + 1) // 2
    stage_rate = F(3 + 2, 3 * 2)
    print(f"finite depths=3..{args.depth}, roles={dict(counts)}")
    print(f"minimum columns by role: {minimum_columns}")
    print(f"positive-fringe roles with floor(delta*f*n)=0: {dict(zero_support)}")
    print(f"botDesc native/c residues: {[F(1, 2**j) for j in range(7)]}")
    print(f"max padded bits={bits}, three-sort depth={local_depth}, "
          f"stage/log rate={stage_rate}, conditional coefficient={local_depth*stage_rate}")
    print("bottom ten-residue certificate (t, omega, d0, C, e, role, n_min):")
    for row in period_rows:
        print("  " + repr(row))
    print("Finite exact geometry checks only; probability and global sorting gates remain open.")


if __name__ == "__main__":
    main()
