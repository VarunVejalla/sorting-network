#!/usr/bin/env python3
"""Check active packet mass and derive the conditional aggregate cycle budget.

The finite loop mirrors the exact rational allocation used by the Chvatal
port screen. The displayed recurrence is conditional on a common certified
matching-cycle contraction for every active packet count; this script does
not certify such a family or the port-repartition term.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import frontier_alignment_screen as schedule  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-depth", type=int, default=7)
    parser.add_argument("--max-depth", type=int, default=40)
    parser.add_argument("--packet-wires", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=26)
    parser.add_argument("--save", help="optional JSON output path")
    args = parser.parse_args()
    schedule.M = args.packet_wires

    checked_stages = 0
    rows = []
    for d in range(args.min_depth, args.max_depth + 1):
        total_stages = 0
        for t in range(2, 3 * d - 20):
            active_wire_mass = sum(
                Fraction(64**level) * schedule.allocation(d, level, t)
                for level in range(d + 1)
            )
            if active_wire_mass != 64**d:
                raise AssertionError(f"active allocations do not partition N at d={d}, t={t}")
            total_stages += 1
            checked_stages += 1
        rows.append({
            "depth": d,
            "ordinary_stages_checked": total_stages,
            "active_packet_count_per_stage": str(Fraction(64**d, args.packet_wires)),
            "one_threshold_additive_L2_coefficient": args.rounds / (2 * args.packet_wires**0.5),
            "one_threshold_fresh_spill_fraction_bound": args.rounds / (4 * args.packet_wires),
            "naive_stage_sum_spill_fraction_bound": total_stages * args.rounds / (4 * args.packet_wires),
        })

    result = {
        "status": "exact finite allocation-mass check plus conditional analytic budget",
        "depth_range": [args.min_depth, args.max_depth],
        "checked_ordinary_stages": checked_stages,
        "conditional_cycle_recurrence": "sqrt(V_mix) <= rho*sqrt(V_in) + (s/2)*sqrt(N/m)",
        "conditional_multi_threshold_recurrence": "sqrt(W_mix) <= rho*sqrt(W_in) + (s/2)*sqrt((N/m)*K)",
        "port_repartition_term": "not bounded; prevents a closed stage recurrence",
        "results": rows,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.save:
        Path(args.save).write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
