"""Shared emitters for `ExpCert` certificates (AKS/Sub800/ExpCert.lean).

A certificate for `exp x <= u` (resp. `l <= exp x`) is `⟨k, [v_k, ..., v_0]⟩`: `v_k` bounds
`exp (x / 2^k)` by the six-term Taylor value, each next value bounds the square of the previous.
The rounding is the same as the tactic emitters of `gen_r1_cells.py` (25 significant digits), so the
certified values are identical to the ones the tactic proofs used.
"""
from fractions import Fraction as Fr

from gen_r1_cells import DIG, kfor, round_dn, round_up, taylor


def Q(x):
    """A rational literal in `ℚ`."""
    x = Fr(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


def C(k, vs):
    return "⟨" + str(k) + ", [" + ", ".join(Q(v) for v in vs) + "]⟩"


def cert_up(x):
    """Certificate for `exp x <= u`: returns (cert literal, u)."""
    x = Fr(x)
    k = kfor(x)
    us = [round_up(taylor(x / 2 ** k, True), DIG)]
    for _ in range(k):
        us.append(round_up(us[-1] ** 2, DIG))
    return C(k, us), us[-1]


def cert_lo(x):
    """Certificate for `l <= exp x`: returns (cert literal, l)."""
    x = Fr(x)
    k = kfor(x)
    ls = [round_dn(taylor(x / 2 ** k, False), DIG)]
    assert ls[0] > 0
    for _ in range(k):
        ls.append(round_dn(ls[-1] ** 2, DIG))
    return C(k, ls), ls[-1]


XCAP = Fr(-230)


def cert_up_capped(x):
    """Certificate for `exp x <= u` at `xr = max(x, XCAP)` (checked by `ExpCert.expUpLe`): for very
    negative `x` the exact values would have tens of thousands of digits. Returns (cert, u, xr)."""
    x = Fr(x)
    xr = max(x, XCAP)
    cert, u = cert_up(xr)
    return cert, u, xr
