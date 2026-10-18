#!/usr/bin/env python3
"""Precision of one- and two-round sort-based separators under the walk-maximum bound (WALK-BOUND.md).

Constants after review (WALK-BOUND.md sec. 6): swap-Lipschitz constant 1, explicit n and eta.

  one round :  E1_new(m) = 2 (K1(n, eta) sqrt(m) + 2/3) / m,
               K1 = max_p [ sqrt(pi/2) sqrt(p(1-p)) + sqrt( p' (H(p) + ln(2n/eta)/n) / 2 ) ]
               (1.043 as n -> infinity; 1.174 at n = 16, eta = 1/100)
  two rounds:  d_new(m) = 2 sqrt( E1_new(m) * K2 / m ),
               K2 = ln(2 log2 m) + 1 + 2 ln 2 + (ln m + ln(1/eta)) / n     (union over S and base row i)
               (sketch: the concentration of the peeled sum is not yet proved)

Certification uses the worst case n = 16 (the package's smallest column count), eta = 1/100.
Compared with Lemma 6.1's E1_old = sqrt(2(1+ln m)/m) and BULK2's two-round threshold
(../tapered/exchange_rate.py, eps2_scalar).

Run:  python -I walk_precision.py
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
import exchange_rate as E  # noqa: E402

N_CERT = 16
ETA = 1e-2


def H(p):
    return -p * math.log(p) - (1 - p) * math.log(1 - p)


def K1(n=N_CERT, eta=ETA):
    best = 0.0
    for k in range(1, 200):
        p = k / 200
        pp = min(p, 1 - p)
        v = math.sqrt(math.pi / 2) * math.sqrt(p * (1 - p)) + math.sqrt(pp * (H(p) + math.log(2 * n / eta) / n) / 2)
        best = max(best, v)
    return best


_K1 = K1()


def e1_new(L, n=N_CERT, eta=ETA):
    m = 2.0 ** L
    k1 = _K1 if (n, eta) == (N_CERT, ETA) else K1(n, eta)
    return 2 * (k1 * math.sqrt(m) + 2 / 3) / m


def d_new(L, n=N_CERT, eta=ETA):
    m = 2.0 ** L
    K2 = math.log(2 * L) + 1 + 2 * math.log(2) + (math.log(m) + math.log(1 / eta)) / n
    return 2 * math.sqrt(e1_new(L, n, eta) * K2 / m)


def need(fn, target):
    lo, hi = 4.0, 120.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if fn(mid) <= target:
            hi = mid
        else:
            lo = mid
    return hi


def main():
    print(f"K1(n=16, eta=1/100) = {_K1:.3f};  K1(n=inf) = {K1(10**12, ETA):.3f}")
    print("  lg m | one round: old      new      ratio | two rounds: old (BULK2)   new        ratio")
    for L in (16, 20, 25, 30, 35, 42):
        o1, n1 = float(E.eps1(L)), e1_new(L)
        o2, n2 = E.eps2_scalar(L), d_new(L)
        print(f"  {L:4d} |        {o1:.3e} {n1:.3e}  {o1 / n1:5.2f} |          {o2:.3e}      {n2:.3e}  {o2 / n2:5.2f}")
    t = 1 / 59e6
    print(f"\ncolumn height for the 1419 package's bulk target d = 1/59e6:")
    print(f"  two rounds, BULK2 route : lg m = {need(E.eps2_scalar, t):.2f}   (BULK2.md: 41.66)")
    print(f"  two rounds, walk bound  : lg m = {need(d_new, t):.2f}")
    print(f"  one round,  Lemma 6.1   : lg m = {need(lambda L: float(E.eps1(L)), t):.2f}")
    print(f"  one round,  walk bound  : lg m = {need(e1_new, t):.2f}")


if __name__ == "__main__":
    main()
