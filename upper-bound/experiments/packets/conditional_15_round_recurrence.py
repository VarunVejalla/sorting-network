#!/usr/bin/env python3
"""Exact arithmetic for the conditional centered 15-round recurrence.

This is a sensitivity calculation, not a theorem about the scheduler. It
assumes (1) the checked squared WireFlow factor 65 applies to the same
centered error state, (2) each matching cohort's error has zero mean, (3) the
exact c<=130 screen contracts the matching part by 1/16, and (4) blocks total
N/4096 with at most N tracked thresholds. The constant mean mode, port/target
drift, exceptions, sortedness, and a repeatable packet-ID schedule are omitted.
"""

from __future__ import annotations

import json
from fractions import Fraction


def main() -> None:
    rounds = 15
    block_wires = 4096
    # sqrt(65)/16 <= 63/125, checked without floating point.
    lam = Fraction(63, 125)
    assert Fraction(65, 256) <= lam * lam

    # E' <= lam E + (rounds/2)*sqrt((N/block_wires)*K) + drift.
    # With K<=N, normalize by N; after centering, E_0<=2*sqrt(m)*N=128N.
    initial = Fraction(block_wires, 32)  # 2*sqrt(block_wires) = 128
    fresh = Fraction(rounds, 2 * 64)  # sqrt(block_wires) = 64

    rows = []
    for depth in (20, 40, 80, 160):
        # Ordinary stages are t=2,...,3d-21, hence 3d-22 stages.
        stages = max(0, 3 * depth - 22)
        lam_pow = lam**stages
        normalized = initial * lam_pow + fresh * (1 - lam_pow) / (1 - lam)
        rows.append({
            "depth": depth,
            "ordinary_stages": stages,
            "initial_centered_error_over_N": float(initial),
            "fresh_centered_error_per_stage_over_N": float(fresh),
            "zero_drift_final_centered_error_over_N": round(float(normalized), 9),
        })

    limit = fresh / (1 - lam)
    print(json.dumps({
        "status": "conditional centered exact-rational recurrence screen; not a scheduler proof",
        "assumed_recurrence": "centered_E_next <= (63/125) centered_E + (15/128) N + drift",
        "contraction_certificate": "65/256 <= (63/125)^2",
        "assumptions": [
            "factor-65 WireFlow energy transfer and 1/16 matching contraction compose on one centered error state",
            "each matched cohort's count-error vector has zero mean (the constant mode is excluded)",
            "4096-wire blocks have total count N/4096",
            "number of tracked thresholds K is at most N",
            "no port/target drift, exceptions, or frontier terms",
        ],
        "zero_drift_asymptotic_centered_error_over_N": str(limit),
        "zero_drift_asymptotic_centered_error_over_N_decimal": float(limit),
        "drift_sensitivity": "a uniform additive drift eta*N per stage contributes at most (125/62)*eta*N",
        "rows": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
