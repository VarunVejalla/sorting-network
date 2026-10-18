#!/usr/bin/env python3
"""UB-15 screen: smallest two-round fringe height f certified by the F2ROUND proof route at a given precision.

Uses fringe_cert_param.certify (interval arithmetic, outward rounding), a parametrized copy of
upper-bound/best/notes/two-round/f2round/cert.py.  J = 1/eps_F is the target fringe precision
(escapes must be zero for ranks j <= J); delta is the fringe fraction delta_F.

Two acceptance levels are reported:
  exact  : every precondition and the exact-route failure bounds (2 P1, 2 P2 <= 1/1000) pass;
  closed : additionally the Lean-friendly closed forms pass (what the existing Lean plan uses).
A pass is a certified sufficient condition for this proof route only; a failure says nothing about
the separator itself.

Run:  python -I fringe_floor_search.py
"""
import itertools
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fringe_cert_param as FC  # noqa: E402

CLOSED_NAMES = ("crude", "closed", "regime I valid", "regime I slope", "regime II slope")


def run(f, a, bfrac, c, bmult, J, delta):
    g1 = max(1, int(a * f))
    g2 = max(g1 + 1, int(bfrac * f))
    if g2 >= f:
        return None
    b = Fr(math.ceil(bmult * J / (g1 + 1)))
    try:
        st = FC.certify(f, g1, g2, c, b, J, delta)
    except (AssertionError, ZeroDivisionError, ValueError, OverflowError):
        return None
    exact_ok = all(any(k in n for k in CLOSED_NAMES) for n in st["fail"])
    return exact_ok, st["ok"], (g1, g2, c, b)


GRID = list(itertools.product((0.3, 0.4), (0.75, 0.9), (Fr(1, 3),), (1.0, 4.0)))


def passes(f, J, delta, level):
    """Best result over the parameter grid at height f: (exact_ok, closed_ok, params)."""
    for a, bf, c, bm in GRID:
        r = run(f, a, bf, c, bm, J, delta)
        if r is None:
            continue
        ex, cl, par = r
        if (cl if level == "closed" else ex):
            return par
    return None


def floor_for(J, delta, level, lo=16, hi=2 ** 26):
    """Bisection on f, assuming the route's checks improve with f (F2ROUND.md sec. 5)."""
    if passes(hi, J, delta, level) is None:
        return None
    while hi - lo > max(1, lo // 64):
        mid = (lo + hi) // 2
        if passes(mid, J, delta, level) is not None:
            hi = mid
        else:
            lo = mid
    return hi, passes(hi, J, delta, level)


def main():
    deltas = [("128/4095", Fr(128, 4095)), ("1/2", Fr(1, 2))]
    Js = [int(x) for x in sys.argv[1:]] or [2 ** 8, 2 ** 10, 2 ** 12, 2 ** 14, 2 ** 16, 2 ** 20]
    print("J = 1/eps_F | delta    | smallest f, exact route (params)          | smallest f, with Lean closed forms")
    for J in Js:
        for dname, d in deltas:
            ex = floor_for(J, d, "exact")
            cl = floor_for(J, d, "closed")
            fe = f"{ex[0]:8d}  g1,g2={ex[1][0]},{ex[1][1]} c={ex[1][2]} b={ex[1][3]}" if ex else "   none <= 2^26"
            fc = f"{cl[0]:8d}" if cl else "   none <= 2^26"
            print(f" 2^{math.log2(J):<5.1f}    | {dname:8s} | {fe:42s} | {fc}", flush=True)


if __name__ == "__main__":
    main()
