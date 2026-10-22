#!/usr/bin/env python3
"""Exact check at the dynamic-O_L point (INDUCTION.md section 13): schedule (4,4,3) = (k, A, nu) = (8, 8, 1/4),
delta_F = 1/8, rows m <= 2^19, sided centred design, outsider term bounded dynamically (no P cap, no r*).

  (4.2-dyn)  2 cross/(A nu - 1) + (k-1) mu sib/2 + mu delta A^2 k + ROUND + eps_B eta  <=  mu A nu
             cross = far crossings over half a child range, as a fraction of a (walk-bound tail at d0 = 0.026 m,
             float from screen.tail_frac; to be certified)
  (4.3), (4.4), (4.5) as in r1_point.py; eta from (I3) with the end-deficit steady state.
Prints the largest admissible eps_B and J per delta, the walk-bound two-round bulk precision at m = 2^19,
and the fringe ceiling f <= p m/2 - 1 (to compare with the certified fringe f(J), which scales ~ 18 sqrt(J)).
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "walk-bound"))

k, A, nu = 16, 16, Fr(1, 8)
q = 24
dF = Fr(1, 8)
Anu = A * nu
p = (Anu * k - 1) / Fr(A * A * k * k)
mu43 = nu / (A * k * k)
mu44 = dF * (Anu * k - 1) / (2 * A * A * k * k)
mu = (1 - Fr(1, 1024)) * min(mu43, mu44)
ROUND = Fr(1, 10) * mu


def main():
    import na_precision as NP
    import screen as Sc
    cross = Fr(2 * Sc.tail_frac(q, 0.026 * 2 ** q)).limit_denominator(10 ** 12)
    whalf = 2 * cross / (Anu - 1) / 2
    gstar = (p / 2 + whalf) / (Anu - 1)
    eta = max(p * (1 / nu ** 2 + k * A / nu) + gstar / nu ** 2, Fr(1))
    d_bulk = NP.d_na(float(q), NP.e1_na(float(q), uniform=True), uniform=True)[0]
    f_ceiling = float(p) * 2 ** q / 2 - 1
    print(f"(4,4,3): mu = {float(mu):.4e} (4.3 {float(mu43):.4e}, 4.4 {float(mu44):.4e}), p = {float(p):.4e}, A nu = {float(Anu)}, "
          f"cross = {float(cross):.3e}, g* = {float(gstar):.3e}, eta = {float(eta):.5f}")
    print(f"bulk at m = 2^{q}: d = {d_bulk:.4e}; fringe ceiling f <= {f_ceiling:.0f}")
    for num in (1, 2, 5, 10, 20, 50, 100, 200, 500):
        delta = Fr(num, 10 ** 6)
        if delta * k * A >= 1:
            break
        sib = delta * k * A * A / (1 - delta ** 2 * k ** 2 * A ** 2)
        fixed = 2 * cross / (Anu - 1) + (k - 1) * mu * sib / 2 + mu * delta * A * A * k + ROUND
        eB = (mu * Anu - fixed) / eta
        eF = Anu * delta - A * A * k * delta ** 2
        if eB <= 0 or eF <= 0:
            print(f"  delta = {float(delta):.1e}: infeasible")
            continue
        J = 1 / eF
        print(f"  delta = {float(delta):.1e}: max eps_B = {float(eB):.4e} (bulk margin {float(eB) / d_bulk:.3f}), J = {float(J):.0f}, "
              f"fringe f ~ 18 sqrt(J) = {18 * math.sqrt(float(J)):.0f} vs ceiling {f_ceiling:.0f}")


if __name__ == "__main__":
    main()
