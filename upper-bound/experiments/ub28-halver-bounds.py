#!/usr/bin/env python3
"""Exact rational checks for the elementary constants in UB28-LOCAL-HALVER.md."""

from fractions import Fraction as Q


def ln_upper(q: Q, terms: int = 64) -> Q:
    """Upper bound ln(q), q >= 1, from the atanh series and a geometric tail."""
    z = (q - 1) / (q + 1)
    partial = 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return partial + tail


def ln_lower(q: Q, terms: int = 64) -> Q:
    """Lower bound ln(q), q >= 1, by truncating its positive atanh series."""
    z = (q - 1) / (q + 1)
    return 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))


def exp_lower(x: Q, terms: int = 16) -> Q:
    """Lower bound exp(x), x >= 0, by a finite positive Taylor sum."""
    total = Q(0)
    term = Q(1)
    for k in range(terms + 1):
        if k:
            term *= x / k
        total += term
    return total


def main() -> None:
    # Logarithm bounds used in the small-set expansion estimate.
    assert ln_upper(Q(10)) < 3  # ln(10) < 3, using exp(3) > 10 below.
    assert Q(1, 5) <= Q(1, 4) / (1 + Q(1, 4))  # ln(5/4) >= x/(1+x).

    # Entropy at x=2/25: H(x)=x ln(1/x)+(1-x) ln(1/(1-x)).
    entropy_upper = Q(2, 25) * ln_upper(Q(25, 2)) + Q(23, 25) * ln_upper(Q(25, 23))
    assert entropy_upper < Q(27888, 100000)
    assert Q(2, 25) + Q(1, 2) * Q(2, 25) ** 2 == Q(52, 625)  # -ln(1-x) >= x+x^2/2.
    assert Q(52, 625) == Q(832, 10000)
    assert ln_upper(Q(23, 2)) < 3
    assert ln_upper(Q(101)) < Q(49, 10)

    # exp(3) > 20 implies both ln(10)<3 and exp(18/5)>20.
    assert exp_lower(Q(3), 8) > 20
    assert exp_lower(Q(3, 10), 2) > Q(4, 3), "therefore exp(-0.3) < 3/4"
    # The rectangle exponent at (2/25,2/25) is strictly below -0.101.
    rectangle_upper = 2 * entropy_upper - Q(99 * 2, 25) * Q(832, 10000)
    assert rectangle_upper < -Q(101, 1000)
    # For h >= 100, (h+1)^2 exp(-.101h) decreases; at h=100 it is < exp(-.3).
    assert 2 * Q(49, 10) - Q(101, 10) == -Q(3, 10)
    # Combined failure bound: 2/(exp(3.6)-1)+exp(-.3) < 2/19+3/4 < 1.
    assert Q(2, 19) + Q(3, 4) < 1

    # Sharper 70-matching construction: an 8-fold expansion through size h/10
    # and no edge-free h/10-by-h/10 rectangle give a 1/9-halver.
    expansion_exponent = 9 + 62 * ln_upper(Q(8)) - 61 * ln_lower(Q(10))
    assert expansion_exponent < -Q(249, 100)
    assert exp_lower(Q(249, 100), 5) > 11
    entropy_tenth = Q(1, 10) * ln_upper(Q(10)) + Q(9, 10) * ln_upper(Q(10, 9))
    assert entropy_tenth < Q(3251, 10000)
    # -ln(9/10) >= .1 + .1^2/2 = .105.
    assert Q(1, 10) + Q(1, 2) * Q(1, 10) ** 2 == Q(105, 1000)
    assert 2 * entropy_tenth - 70 * Q(1, 10) * Q(105, 1000) < -Q(84, 1000)
    # The rectangle exponent is decreasing on x,y >= .1. For h >= 200,
    # (h+1)^2 exp(-.084h) decreases and at h=200 is < exp(-4.8) < .01.
    assert exp_lower(Q(6), 6) > 201  # ln(201) < 6.
    assert exp_lower(Q(24, 5), 7) > 100  # exp(4.8) > 100.
    assert 2 * Q(6) - Q(84, 1000) * 200 == -Q(24, 5)
    assert Q(1, 5) + Q(1, 100) < 1
    print("UB-28 halver rational bounds: PASS")
    print(f"entropy upper = {float(entropy_upper):.8f}")
    print(f"rectangle exponent upper = {float(rectangle_upper):.8f}")
    print(f"70-round expansion exponent upper = {float(expansion_exponent):.8f}")
    print(f"70-round rectangle exponent upper = {float(2 * entropy_tenth - 70 * Q(1, 10) * Q(105, 1000)):.8f}")


if __name__ == "__main__":
    main()
