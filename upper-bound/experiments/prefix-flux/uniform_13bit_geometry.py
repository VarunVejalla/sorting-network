#!/usr/bin/env python3
"""Finite exact geometry screen for uniform Chvatal flow at (3,3,2).

The screen tests role-dependent row heights on the exact Par formulas. It is
not a local separator existence proof or a global sorting-network proof.
"""
import argparse
from collections import Counter
from fractions import Fraction as F

from oracle import Par


SCALE = 16384
GEOMETRY = {
    "topDesc": (8, 0, 1),
    "topRise": (8192, 16, 1020),
    "mid": (8190, 15, 1020),
    "botDesc_native": (8190, 15, 1020),
    "botDesc_small": (8160, 240, 960),
}


def check(depth):
    p = Par(3, 3, 2)
    counts = Counter()
    min_columns = {}
    max_bits = 0
    botdesc_native_ratios = set()
    for d in range(3, depth + 1):
        for t in range(p.tf(d)):
            for i in range(d + 1):
                if t == 0:
                    active = i == 0
                else:
                    active = p.active(d, i, t)
                if not active:
                    continue
                role = "topDesc" if t == 0 else p.role(d, i, t)
                a = p.alloc(d, i, t)
                up = p.up(d, i, t, a)
                down = p.down(d, i, t)
                aa, uu, dd = SCALE * a, SCALE * up, SCALE * down
                if role == "botRise":
                    assert uu == aa and dd == 0
                    counts["botRise_bypass"] += 1
                    continue
                geom_role = role
                if role == "botDesc":
                    native_over_cap = F(p.k ** (d - i), 1) / p.cap(d, i, t)
                    botdesc_native_ratios.add(native_over_cap)
                    if native_over_cap == 1:
                        geom_role = "botDesc_native"
                    else:
                        assert native_over_cap == F(1, 16), (d, t, i, native_over_cap)
                        geom_role = "botDesc_small"
                m, f, b = GEOMETRY[geom_role]
                assert m == 2 * f + p.k * b
                assert aa.denominator == uu.denominator == dd.denominator == 1
                assert aa % m == 0, (d, t, i, geom_role, aa, m)
                n = aa // m
                assert n >= 16, (d, t, i, geom_role, n)
                assert uu == 2 * f * n, (d, t, i, geom_role, uu, f, n)
                assert dd == b * n, (d, t, i, geom_role, dd, b, n)
                assert aa == uu + p.k * dd, (d, t, i, geom_role)
                bits = (m - 1).bit_length()
                max_bits = max(max_bits, bits)
                min_columns[geom_role] = min(min_columns.get(geom_role, n), n)
                counts[geom_role] += 1
    assert botdesc_native_ratios == {F(1), F(1, 16)}, botdesc_native_ratios
    return counts, min_columns, max_bits


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=100)
    args = ap.parse_args()
    counts, min_columns, bits = check(args.depth)
    depth = 3 * bits * (bits + 1) // 2
    stage_rate = F(3 + 3, 3 * 2)
    print(f"finite depths=3..{args.depth}: {dict(counts)}")
    print(f"minimum column counts by geometry role: {min_columns}")
    print(f"uniform up-flow botDesc native/c values: 1 and 1/16")
    print(f"max padded row bits={bits}, three-sort depth={depth}, "
          f"stage/log rate={stage_rate}, conditional coefficient={depth*stage_rate}")
    print("Exact finite geometry checks passed; local probability and global sorting proofs remain open.")


if __name__ == "__main__":
    main()
