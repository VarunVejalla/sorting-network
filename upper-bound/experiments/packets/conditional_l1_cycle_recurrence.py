#!/usr/bin/env python3
"""Conditional centered-L1 recurrence for 15-round 4096-block mixing.

Assumes ordinal mixing contracts each c<=130 centered block-error vector by
rho<=1/16 and reblocking does not transfer coarse mean error into the centered
component. The constant mean mode is not contracted. Unmatched pool-tail mass
is separately summed from exact allocation formulas for finite d; none of the
assumptions is yet an end-to-end Lean theorem.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import frontier_alignment_screen as schedule  # noqa: E402


def main() -> None:
    lam = Fraction(713, 1000)
    assert Fraction(130, 256) <= lam * lam  # sqrt(130)/16 <= 0.713
    fresh = Fraction(15, 8192)  # (15/2)*(N/4096)*K, normalized by N*K
    tail_cap = 63 * 64
    rows = []
    worst_tail_sum = Fraction(0)
    worst_tail_depth = 0
    worst_final = Fraction(0)
    worst_final_depth = 0

    for d in range(7, 81):
        n = 64**d
        error = Fraction(2)  # safe bound after centering errors in each cohort
        tail_sum = Fraction(0)
        tf = 3 * d - 20
        stages = 0
        for t in range(2, tf):
            tail_wires = Fraction(0)
            interior_mass = Fraction(0)
            for level in range(1, d):
                size = schedule.allocation(d, level, t + 1)
                if size:
                    bags = 64**level
                    interior_mass += bags * size
                    tail_wires += bags * min(size, tail_cap)
            if interior_mass > n:
                raise AssertionError(f"receiver mass exceeds N at d={d}, t={t}")
            tail = tail_wires / n
            error = lam * error + fresh
            tail_sum += tail
            stages += 1
        row = {
            "depth": d,
            "ordinary_stages": stages,
            "tail_time_sum_over_N": float(tail_sum),
            "zero_coarse_drift_centered_L1_over_NK": round(float(error), 9),
        }
        if d in (8, 20, 40, 80):
            rows.append(row)
        if tail_sum > worst_tail_sum:
            worst_tail_sum, worst_tail_depth = tail_sum, d
        if stages > 0 and error > worst_final:
            worst_final, worst_final_depth = error, d

    steady = fresh / (1 - lam)
    uniform_tail_mass = Fraction(1, 21 * 64**2)
    print(json.dumps({
        "status": "conditional centered-error screen; finite scheduler arithmetic, not a proof",
        "assumed_normalized_recurrence": "v_next <= (713/1000)*v + 15/8192 + kappa_t",
        "v_definition": "L1 error after removing each matching cohort's constant mode, normalized by N*K",
        "contraction_check": "130/256 <= (713/1000)^2",
        "zero_tail_steady_state": str(steady),
        "zero_tail_steady_state_decimal": float(steady),
        "conditional_limit_if_tail_mass_is_unit_error_input": {
            "assumption": "each unmatched tail wire contributes at most one normalized L1 error unit and the cycle contracts thereafter",
            "fraction": str(steady + uniform_tail_mass),
            "decimal": float(steady + uniform_tail_mass),
        },
        "separate_unmatched_tail_mass_time_sum_d7_to_80": {
            "depth": worst_tail_depth,
            "fraction_decimal": float(worst_tail_sum),
        },
        "max_conditional_final_error_nonempty_d7_to_80": {
            "depth": worst_final_depth,
            "fraction_decimal": round(float(worst_final), 9),
        },
        "samples": rows,
        "still_unproved": [
            "the block targets define the actual cohort-centered error state",
            "coarse mean errors are transported without creating uncontrolled centered error (kappa_t)",
            "port repartition/reblocking is nonexpansive on the centered component",
            "tail mass converts to profile error by at most its wire mass",
            "centered plus coarse error suffices for the final sorting induction",
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
