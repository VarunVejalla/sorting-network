"""Exact scalar audit of the existing rounded Paterson parameters.

Run from any directory: python path/to/audit_budget.py
This checks arithmetic, not existence or correctness of replacement networks.
"""
from fractions import Fraction as F
from math import log


def report(name, value):
    print(f"{name}: {value} (~{float(value):.10g})")


def main():
    A, mu, delta, nu = F(19, 4), F(199, 10000), F(1, 57), F(707, 1000)
    alpha, split = F(81773, 89250), F(1, 62)
    tail = sum((F(1, d) for d in (199, 110, 109, 106, 90)), F(0))
    refinement = tail - F(1, 199)
    first_base = (2 * mu * delta * A**2
                  + 2 * mu * delta * A**2 / (1 - 4 * delta**2 * A**2)
                  + 1 / (8 * A**2 - 2) + mu)
    tail_ceiling = nu * A * delta - 2 * A**2 * delta**2
    split_ceiling = 2 * (nu * mu * A - first_base)
    fresh = (1 - alpha + split) / (2 * A) + tail * mu / A
    rounded_slack = nu * mu - 2 * mu * delta * A - fresh - F(10, 300000)
    assert tail < tail_ceiling
    assert split < split_ceiling
    assert rounded_slack >= 0
    assert (2 * A)**2 * nu**13 < 1
    for name, value in (
        ("tail error", tail), ("partial-bag tail error", split + refinement),
        ("tail error strict ceiling", tail_ceiling),
        ("split error strict ceiling", split_ceiling),
        ("rounded first-stranger slack", rounded_slack),
        ("shrink certificate", (2 * A)**2 * nu**13),
        ("current coefficient", F(13, 2) * 989 + 561 + 1),
        ("current additive term", F(13, 2) * 989 + 561),
    ):
        report(name, value)
    print(f"Ideal real stage ratio (not a rational certificate): {log(float(2*A))/-log(float(nu)):.10g}")
    print("Conditional coefficient examples (separator, repair -> coefficient):")
    for separator, repair in ((100, 100), (60, 80), (30, 4), (24, 43)):
        report(f"  {separator}, {repair}", F(13, 2) * separator + repair + 1)
    print("Root-repair cumulative bin-error limits at minimum root capacity:")
    for level in (2, 3, 4):
        deep_bound = (64 * mu * delta**(6-level) * 300000 * A**6
                      / (1 - 4 * delta**2 * A**2))
        limit = F(3, 16) * deep_bound
        report(f"  level {level}", limit)
        print(f"    integer cumulative limit: {limit.numerator // limit.denominator}")
    print("First-split structure at maximum root capacity:")
    root_ceiling = F(300000) / nu**2
    report("  root plus cold register ceiling", root_ceiling + 32 + root_ceiling/(4*A**2-1))
    for level in (2, 4):
        bound = mu * delta**(level-1) * root_ceiling * A**level
        report(f"  level {level} per-bag wrong-half bound", bound)
        print(f"    integer per-bag limit: {bound.numerator // bound.denominator}")


if __name__ == "__main__":
    main()
