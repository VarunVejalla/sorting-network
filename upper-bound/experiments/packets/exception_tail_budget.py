#!/usr/bin/env python3
"""Exact schedule-mass screen for the unmatched (<4096-wire) pool tail.

Uses the current Chvatal allocation formulas. It charges at most 4032 tail
wires per interior receiver bag and is a conditional budget, not a proof that
the tail has no additional profile-error amplification.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import frontier_alignment_screen as schedule  # noqa: E402


def main() -> None:
    tail_cap = 63 * 64
    # Uniform analytic envelope. At output time tau, active receiver levels
    # satisfy level <= omega(tau) <= (tau + 7) / 3. Summing the per-bag cap
    # over those levels and normalizing by 64**d gives at most
    # 64**(omega + 2 - d). Since tau <= 3*d - 20, summing backward from the
    # last possible output time yields sum_{k>=0} 64**floor((-7-k)/3)
    # = 1/(21*64**2).
    uniform_analytic_bound = Fraction(1, 21 * 64**2)
    grouped_geometric_sum = Fraction(3, 64**3) / (1 - Fraction(1, 64))
    assert grouped_geometric_sum == uniform_analytic_bound
    max_stage_fraction = Fraction(0)
    max_stage = None
    max_total_fraction = Fraction(0)
    max_total_depth = None
    for d in range(7, 81):
        n = 64**d
        stage_sum = Fraction(0)
        tf = 3 * d - 20
        for t in range(2, tf):
            tail_wires = Fraction(0)
            active_mass = Fraction(0)
            for level in range(1, d):
                cap = schedule.allocation(d, level, t + 1)
                if cap:
                    receiver_count = 64**level
                    active_mass += receiver_count * cap
                    tail_wires += receiver_count * min(cap, tail_cap)
            if active_mass > n:
                raise AssertionError(f"interior receiver mass exceeds N at d={d}, t={t}")
            stage_fraction = tail_wires / n
            if stage_fraction > max_stage_fraction:
                max_stage_fraction = stage_fraction
                max_stage = {"depth": d, "time": t, "fraction": str(stage_fraction)}
            stage_sum += stage_fraction
        if stage_sum > uniform_analytic_bound:
            raise AssertionError(
                f"analytic uniform envelope fails at d={d}: {stage_sum}"
            )
        if stage_sum > max_total_fraction:
            max_total_fraction = stage_sum
            max_total_depth = {"depth": d, "sum_fraction": str(stage_sum)}

    print(json.dumps({
        "status": "exact allocation-formula upper bound only; not a Lean theorem",
        "per_interior_receiver_tail_cap_wires": tail_cap,
        "depths_checked": [7, 80],
        "worst_single_stage": {
            **max_stage,
            "fraction_decimal": float(max_stage_fraction),
        },
        "largest_time_sum_over_checked_depths": {
            **max_total_depth,
            "fraction_decimal": float(max_total_fraction),
        },
        "uniform_all_depths_analytic_envelope": {
            "fraction": str(uniform_analytic_bound),
            "decimal": float(uniform_analytic_bound),
            "derivation": "sum_{k>=0} 64^floor((-7-k)/3) = 1/(21*64^2)",
        },
        "limitation": "does not bound how tail errors couple into the rank-profile invariant",
    }, indent=2))


if __name__ == "__main__":
    main()
