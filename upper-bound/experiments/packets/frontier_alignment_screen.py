#!/usr/bin/env python3
"""Exact rational screen of 4096-packet alignment across Chvatal stage ports.

Mirrors Schedule7/FlowTable/FlowSizes7 for ordinary times 2 <= t < tf7(d).
It enumerates every active level for d in a finite range and checks each
source register size, down block, up half-fringe, and receiver flow identity.
This is an executable model, not a proof for all d or Lean wireSets.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


K = 64
M = 4096


def parity_ceil(x: int, parity: int) -> int:
    return x if x % 2 == parity % 2 else x + 1


def frontiers(d: int, t: int) -> tuple[int, int]:
    alpha_raw = 0 if t + 5 <= d else (t + 6 - d) // 2
    omega_raw = (t + 4) // 3
    return parity_ceil(alpha_raw, t), parity_ceil(omega_raw, t)


def active(d: int, i: int, t: int) -> bool:
    alpha, omega = frontiers(d, t)
    return alpha <= i <= omega and i % 2 == t % 2


def capacity(d: int, i: int, t: int) -> Fraction:
    exponent = d + 2 * i - t - 2
    if exponent < 0:
        return Fraction(1, K ** (-exponent))
    return Fraction(K**exponent)


def allocation(d: int, i: int, t: int) -> Fraction:
    if not active(d, i, t) or t > 3 * d - 20:
        return Fraction(0)
    c = capacity(d, i, t)
    alpha, omega = frontiers(d, t)
    if i == alpha:
        return c
    if i == omega:
        return Fraction(K**d, K**i) - c / K**6
    return (1 - Fraction(1, K**6)) * c


def up(d: int, i: int, t: int) -> Fraction:
    if not active(d, i, t):
        return Fraction(0)
    alpha, omega = frontiers(d, t)
    c = capacity(d, i, t)
    if i == alpha:
        if frontiers(d, t + 1)[0] > alpha:
            return Fraction(0)
        return c / K**4
    if i == omega and frontiers(d, t + 1)[1] <= omega:
        return allocation(d, i, t)
    return Fraction(4095) * c / K**6


def down(d: int, i: int, t: int) -> Fraction:
    if not active(d, i, t):
        return Fraction(0)
    alpha, omega = frontiers(d, t)
    c = capacity(d, i, t)
    if i == alpha:
        if frontiers(d, t + 1)[0] > alpha:
            return c / K
        return (Fraction(4096 * 64) - Fraction(1, 64)) * c / (4096 * K**2)
    if i == omega:
        if frontiers(d, t + 1)[1] > omega:
            return allocation(d, omega + 1, t + 1)
        return Fraction(0)
    return (Fraction(4096 * 64) - Fraction(1, 64)) * c / (4096 * K**2)


def integer(x: Fraction, label: str) -> int:
    if x.denominator != 1:
        raise AssertionError(f"{label} is not integral: {x}")
    return x.numerator


def main() -> None:
    residue_counts: Counter[str] = Counter()
    bad_examples: list[dict[str, int | str]] = []
    stages = 0
    active_bags = 0
    for d in range(7, 41):
        tf = 3 * d - 20
        for t in range(2, tf):
            stages += 1
            for i in range(d + 1):
                a = integer(allocation(d, i, t), "allocation")
                u = integer(up(d, i, t), "up")
                n = integer(down(d, i, t), "down")
                if a:
                    active_bags += 1
                    for label, value in (("bag", a), ("up_half", u // 2), ("down", n)):
                        if label == "up_half" and u % 2:
                            raise AssertionError(f"odd up at d={d}, t={t}, i={i}")
                        residue = value % M
                        residue_counts[f"{label}:{residue}"] += 1
                        if residue and len(bad_examples) < 30:
                            bad_examples.append({"kind": label, "d": d, "t": t, "i": i, "residue": residue})

            # Check the exact receiving-flow identity at every non-root,
            # non-leaf node: parent sends one down block; 64 children send up.
            for level in range(1, d):
                lhs = allocation(d, level, t + 1)
                rhs = down(d, level - 1, t) + K * up(d, level + 1, t)
                if lhs != rhs:
                    raise AssertionError(
                        f"flow identity fails d={d},t={t},level={level}: {lhs} != {rhs}"
                    )

    result = {
        "claim_level": "finite exact-rational model screen; not a universal theorem",
        "packet_wires": M,
        "depths": [7, 40],
        "ordinary_stages_checked": stages,
        "active_bag_instances": active_bags,
        "residue_counts": dict(sorted(residue_counts.items())),
        "first_alignment_failures": bad_examples,
        "receiving_flow_identity": "passed for every enumerated non-root/non-leaf level",
    }
    Path(__file__).with_name("frontier-alignment-screen.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
