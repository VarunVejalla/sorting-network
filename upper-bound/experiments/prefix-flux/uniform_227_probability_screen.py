#!/usr/bin/env python3
"""Screen the existing generalized F2 interval envelope for the (3,2,2) flow."""
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "walk-bound"))
from fringe_cert_v2 import certify


def main() -> None:
    delta = F(1, 10**5)
    for f in (28, 32, 56, 224, 448, 896, 1792):
        g1, g2 = 2 * f // 5, 4 * f // 5
        result = certify(
            f, g1, g2, F(1, 2), 5, 30, delta,
            exact_small=True, failure_budget=F(1, 10**4),
        )
        print(f"f={f}, g1={g1}, g2={g2}, delta={delta}: "
              f"{'PASS' if result['ok'] else 'FAIL'} {result['fail']}")
        assert result["ok"]


if __name__ == "__main__":
    main()
