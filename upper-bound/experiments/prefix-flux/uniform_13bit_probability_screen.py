#!/usr/bin/env python3
"""Numerically screen the existing F2 envelope at the candidate f=15 fringe."""
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "walk-bound"))
from fringe_cert_v2 import certify


def main() -> None:
    print("f=15, g1=6, g2=12, c=1/2, b=5, J=17, exact E=2 support")
    for exponent in range(3, 14):
        delta = F(1, 10**exponent)
        try:
            result = certify(15, 6, 12, F(1, 2), 5, 17, delta, exact_small=True)
        except AssertionError as error:
            print(f"delta=1e-{exponent}: outside envelope ({error})")
            continue
        print(f"delta=1e-{exponent}: envelope={'PASS' if result['ok'] else 'FAIL'}; "
              f"failed checks={result['fail']}")


if __name__ == "__main__":
    main()
