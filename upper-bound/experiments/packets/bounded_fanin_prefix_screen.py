#!/usr/bin/env python3
"""Exact Frobenius check of 14-round prefixes of the 15-round fan-in cycles."""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).parent))
from bounded_fanin_cycle import frobenius_certificate, product_numerator  # noqa: E402


def main() -> None:
    source = Path(__file__).with_name("bounded-fanin-15-exact.json")
    data = json.loads(source.read_text())
    if data["rounds"] != 15 or data["max_packet_count"] != 130:
        raise ValueError("expected the checked 15-round c<=130 certificate")

    prefix_rounds = 14
    target = Fraction(2, 25)
    worst_rho_sq = Fraction(0)
    worst_c = 0
    for row in data["matching_cycles"]:
        c, seed = int(row["c"]), int(row["seed"])
        matrix, _ = product_numerator(c, seed, prefix_rounds)
        numerator, denominator = frobenius_certificate(matrix, c, prefix_rounds)
        rho_sq = Fraction(numerator, denominator)
        if rho_sq > worst_rho_sq:
            worst_rho_sq, worst_c = rho_sq, c

    passed = worst_rho_sq <= target**2
    print(json.dumps({
        "status": "exact finite Frobenius screen; not Lean-checked",
        "source_certificate": source.name,
        "prefix_rounds": prefix_rounds,
        "fan_in_range": [1, 130],
        "max_centered_frobenius_norm_squared": str(worst_rho_sq),
        "worst_fan_in": worst_c,
        "certified_rho_upper_bound": str(target),
        "all_fan_ins_pass": passed,
    }, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
