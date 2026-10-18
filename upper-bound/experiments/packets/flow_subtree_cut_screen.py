#!/usr/bin/env python3
"""Exact bag-density cut screen for actual flowA7 schedule parameters.

This mirrors Schedule7/FlowTable/FlowSizes7 with Fraction arithmetic. For an
interior active bag at level k, take the source error density to be one on
that bag and all its active descendants, zero elsewhere. Its only outgoing
mass from this subtree is the root bag's up-flow. The next-stage descendant
subtree has exactly the remaining mass. This screens the bag-constant density
transfer operator; it is not a Lean proof or a packet-profile realizability
claim.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F

BR = 64
CAPACITY_RATIO = BR**6


def ceil_parity(value: int, parity: int) -> int:
    return value if value % 2 == parity % 2 else value + 1


def alpha(d: int, t: int) -> int:
    if t == 0:
        return 0
    if t == 1:
        return 1
    raw = 0 if t + 5 <= d else (t + 6 - d) // 2
    return ceil_parity(raw, t)


def omega(t: int) -> int:
    if t == 0:
        return 0
    if t == 1:
        return 1
    return ceil_parity((t + 4) // 3, t)


def active(d: int, level: int, t: int) -> bool:
    return alpha(d, t) <= level <= omega(t) and level % 2 == t % 2


def capacity(d: int, level: int, t: int) -> F:
    return F(BR**d * 4096**level, BR**t * 4096)


def allocation(d: int, level: int, t: int) -> F:
    if not active(d, level, t):
        return F(0)
    c = capacity(d, level, t)
    if level == alpha(d, t):
        return c
    if level == omega(t):
        return F(BR**d, BR**level) - c / CAPACITY_RATIO
    return (1 - F(1, CAPACITY_RATIO)) * c


def up_flow(d: int, level: int, t: int) -> F:
    if not active(d, level, t):
        return F(0)
    c = capacity(d, level, t)
    if level == alpha(d, t):
        return F(0) if alpha(d, t) < alpha(d, t + 1) else c / BR**4
    if level == omega(t):
        return (
            F(4095) * c / CAPACITY_RATIO
            if omega(t) < omega(t + 1)
            else allocation(d, level, t)
        )
    return F(4095) * c / CAPACITY_RATIO


def screen(d: int, t: int, root: int) -> dict[str, object]:
    source_levels = [i for i in range(d + 1) if active(d, i, t)]
    receiver_levels = [i for i in range(d + 1) if active(d, i, t + 1)]
    if root not in source_levels or root in (alpha(d, t), omega(t)):
        raise ValueError("root must be an interior active level")

    source_mass = sum(
        (F(BR ** (i - root)) * allocation(d, i, t)
         for i in source_levels if i >= root),
        F(0),
    )
    all_source_mass = sum(
        (F(BR**i) * allocation(d, i, t) for i in source_levels), F(0)
    )
    leak = up_flow(d, root, t)  # one root bag; all descendant up-flows stay inside
    receiver_mass = sum(
        (F(BR ** (i - root)) * allocation(d, i, t + 1)
         for i in receiver_levels if i >= root + 1),
        F(0),
    )
    assert all_source_mass == BR**d
    assert receiver_mass == source_mass - leak

    p = source_mass / all_source_mass
    leak_fraction = leak / source_mass
    # Center 1_subtree by its conserved global mean p. Every output register in
    # the next descendant subtree still has density 1 before centering.
    centered_l2_ratio_sq_lower = (1 - p) * (1 - leak_fraction)
    return {
        "depth": d,
        "stage": t,
        "active_source_levels": source_levels,
        "active_receiver_levels": receiver_levels,
        "subtree_root_level": root,
        "subtree_mass_fraction": f"{float(p):.8e}",
        "root_up_leak_fraction_of_subtree": f"{float(leak_fraction):.8e}",
        "receiver_subtree_mass_identity": "verified exactly: mass_out = mass_in - root_up_flow",
        "centered_l2_norm_ratio_lower_bound": float(centered_l2_ratio_sq_lower ** F(1, 2)),
        "scope": "exact rational schedule arithmetic; bag-density operator only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=40)
    parser.add_argument("--stage", type=int, default=40)
    parser.add_argument("--root-level", type=int, default=6)
    args = parser.parse_args()
    print(json.dumps(screen(args.depth, args.stage, args.root_level), indent=2))


if __name__ == "__main__":
    main()
