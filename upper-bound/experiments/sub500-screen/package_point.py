#!/usr/bin/env python3
"""Exact (4.2-c3) check at the sub-500 package point (CENTRED-SHIFT.md v3), and what each component
must deliver there.

Point: (k, A, nu) = (16, 16, 1/8) [schedule (4,4,3)], delta_F = 1/8, rows m <= 2^24.
  (4.2-c3)  (mu (A nu + 1) + eps_B eta / 2)/(2 A nu - 1) + (k-1) mu sib / 2 + mu delta A^2 k + ROUND
            + eps_B eta  <=  mu A nu          (sided invariant, centred chain, sib centred; no r*)
  (4.3), (4.4), (4.5) as in r1_point.py; eta = 1 + 7/4096-type occupancy (design with end deficits,
  bounded here conservatively by 1 + 2^-8).
Outputs, for each delta on a grid: the largest admissible eps_B, J = 1/eps_F, then the bulk precision
the walk bound gives at m = 2^24 (float, na_precision.d_na) and the fringe ceiling f + 1 <= pi/(2n) rows.
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "walk-bound"))

k, A, nu = 16, 16, Fr(1, 8)
dF = Fr(1, 8)
Anu = A * nu
p = (Anu * k - 1) / Fr(A * A * k * k)
mu43 = nu / (A * k * k)
mu44 = dF * (Anu * k - 1) / (2 * A * A * k * k)
mu = (1 - Fr(1, 1024)) * min(mu43, mu44)
ROUND = Fr(1, 10) * mu
# occupancy (R1-PROOF (I3)): a/c <= p (1/nu^2 + k A/nu) + g* / nu^2. Sided design: the end child gets
# theta = pi/2 + G + o with |o| <= w c / 2, w/2 = (mu (A nu + 1) + eps_B eta/2)/(2 A nu - 1) (eps_B <= 1e-4 here),
# so g' = (p/2 + g + w/2)/(A nu) and g* = (p/2 + w/2)/(A nu - 1)
whalf = (mu * Anu + Fr(1, 10 ** 4) / 2 * Fr(11, 10)) / (2 * (Anu - 1))
gstar = (p / 2 + whalf) / (Anu - 1)
eta = max(p * (1 / nu ** 2 + k * A / nu) + gstar / nu ** 2, Fr(1))


def max_epsB(delta):
    sib = delta * k * A * A / (1 - delta ** 2 * k ** 2 * A ** 2)
    fixed = mu * Anu / (2 * (Anu - 1)) + (k - 1) * mu * sib / 2 + mu * delta * A * A * k + ROUND
    coef = eta / (4 * (Anu - 1)) + eta
    return (mu * Anu - fixed) / coef


def main():
    import na_precision as NP
    q = 24
    L = float(q)
    d_bulk = NP.d_na(L, NP.e1_na(L, uniform=True), uniform=True)[0]
    f_ceiling = float(p) * 2 ** q / 2 - 1                    # f + 1 <= pi/(2n) = p m / 2 rows
    print(f"eta = {float(eta):.6f}, g* = {float(gstar):.4e}; (I2) theta <= (p/2 + g*) c = {float(p / 2 + gstar):.3e} c vs child G >= p A/nu c = {float(p * A / nu):.3e} c")
    print(f"(4,4,3): mu = {float(mu):.4e} (4.3: {float(mu43):.4e}, 4.4: {float(mu44):.4e}), p = {float(p):.4e}, "
          f"A nu = {float(Anu)}")
    print(f"bulk at m = 2^{q}: walk-bound two-round precision d = {d_bulk:.4e}; fringe ceiling f <= {f_ceiling:.0f}")
    for num in (1, 2, 3, 5, 8, 12, 20, 30, 50):
        delta = Fr(num, 10 ** 6)
        if delta * k * A >= 1:
            break
        eB = max_epsB(delta)
        eF = Anu * delta - A * A * k * delta ** 2
        if eB <= 0 or eF <= 0:
            print(f"  delta = {float(delta):.1e}: infeasible")
            continue
        J = 1 / eF
        print(f"  delta = {float(delta):.1e}: max eps_B = {float(eB):.4e} ({'bulk OK' if d_bulk <= eB else 'bulk SHORT'}"
              f", margin {float(eB) / d_bulk:.3f}), J = {float(J):.0f}, route-(d)-type fringe needs f(J) <= {f_ceiling:.0f}")


if __name__ == "__main__":
    main()
