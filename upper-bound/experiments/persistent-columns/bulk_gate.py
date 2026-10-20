#!/usr/bin/env python3
"""UB-41 necessary bulk-only screen; floats, no bound or existence theorem.

Hypothesis: a uniform promised-input column theorem has fixed point
C^2 D^(1/(2^r-1)), where D=k A/nu+1/(A nu), and r fresh sorts per stage.
Deliberately omit fringe construction and terminal/small-bag geometry: passing
is only permission to examine the mathematical hypothesis, never a forecast.
Uses the generic design-P scalar inequalities of sub800/r1_point.py.
"""
import math
from itertools import product


def point(x, y, z, c, rounds):
    k, a, nu = 2**x, 2**y, 2.0**-z
    if y <= z:
        return None
    an = a * nu
    p = (an*k-1)/(a*a*k*k)
    mu = (1-2**-10)*min(nu/(a*k*k), p/16)  # delta_F=1/8
    residual = (k-1)/(2*a*a*k*k)
    eta = 1+residual/(nu*nu)
    best = None
    for j in range(120):
        delta = 10**(-6+j*6/119)/(k*a)
        t = delta*k*a
        if t >= 1:
            continue
        sib = delta*k*a*a/(1-t*t)
        eps_b = (mu*an-1.1*mu-(k-1)*mu*sib-mu*delta*a*a*k-residual)/eta
        eps_f = an*delta-a*a*k*delta*delta
        if eps_b <= 0 or eps_f <= 0:
            continue
        degree = k*a/nu+1/(a*nu)
        equilibrium = c*c*degree**(1/(2**rounds-1))
        # +1 is the provisional allowance for a partial row, not its proof.
        q = math.ceil(math.log2((equilibrium+1)/eps_b))
        stage = rounds*q*(q+1)/2
        ratio = (x+y)/(x*z)
        row = (stage*ratio, x, y, z, q, delta, eps_b, eps_f,
               degree, equilibrium, rounds, c)
        if best is None or row < best:
            best = row
    return best


def main():
    print('MODEL: bulk-only necessary gate, no fringe/terminal/provider certificate')
    print('C sorts cost (x,y,z) q delta epsB J=1/epsF D e_star')
    for c, rounds in product((1, 1.25, 1.5, 2, 2.35, 3), (1, 2, 3)):
        rows = (point(x,y,z,c,rounds)
                for x,y,z in product(range(2,9),range(2,13),range(1,9)))
        best = min((r for r in rows if r is not None), default=None)
        if best is None:
            print(c, rounds, 'infeasible')
            continue
        cost,x,y,z,q,delta,eb,ef,d,e,_,_ = best
        print(f'{c:g} {rounds} {cost:.3f} ({x},{y},{z}) {q} '
              f'{delta:.3g} {eb:.3g} {1/ef:.3g} {d:.3g} {e:.3g}')


if __name__ == '__main__':
    main()
