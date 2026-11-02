#!/usr/bin/env python3
"""Floors and certified tails for a sender-wide three-sort stage.

Model: an m-by-n sender, column sort, independent uniform row permutations,
column sort, a second such round, column sort. This is three vertical sorts and
two scramble rounds, the most that fits below depth 300 at m = 4096 (3*78 = 234;
four sorts cost 312).

Mean field. As n grows, a column's height after a round is a sum of independent
Bernoulli(p_r), with p_r the fraction of columns taller than r before the round.
This is the exact limit for a fixed input profile, so it gives a FLOOR: no tail
bound valid for random scrambles can be smaller. It says nothing about what can
be certified for every input; that is what the certified columns report.

For a mass of i rows per column, the input family has fraction i/L of columns at
height L and the rest empty. Any one input gives a valid floor; the script takes
the worst over L.

    python d2_sender_tail_gate.py
    python d2_sender_tail_gate.py --budget-gate
"""
import argparse
import math
import os
import sys

import numpy as np

from moderate_tail import bound as moderate_bound


def round_step(height_dist):
    """One scramble-and-sort: height distribution to height distribution."""
    tail = np.cumsum(height_dist[::-1])[::-1][1:]
    p = np.clip(tail, 0, 1)
    p = p[p > 1e-300]
    out = np.zeros(len(height_dist))
    out[0] = 1.0
    for q in p:
        out[1:] = out[1:] * (1 - q) + out[:-1] * q
        out[0] *= 1 - q
    return out


def after_two_rounds(i, L, m):
    start = np.zeros(m + 1)
    start[L] = i / L
    start[0] = 1 - i / L
    return round_step(round_step(start))


def excess(dist, f):
    heights = np.arange(len(dist))
    return float(np.sum(dist * np.maximum(heights - f, 0)))


def worst_escape(i, f, m, cap):
    """Largest mean-field escape beyond f rows, per column, over the family."""
    worst = (0.0, None)
    L = max(1, math.ceil(i))
    while L <= cap:
        value = excess(after_two_rounds(i, L, cap), f)
        if value > worst[0]:
            worst = (value, L)
        L = max(L + 1, int(L * 1.5))
    return worst


def bulk_floor(m, cap=None):
    """Mean-field wrong-side mass per wire at a balanced threshold."""
    cap = cap or m
    best = 0.0
    for L in (m,):
        dist = after_two_rounds(m / 2, L, cap)
        mean = float(np.sum(dist * np.arange(len(dist))))
        best = max(best, excess(dist, mean))
    return best / m


def budget_gate():
    """Evaluate E(a)/a <= 1/128 at a = B/2, with B the certified bulk leak."""
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    '..', 'walk-bound'))
    import na_precision as NP
    for bits, rows, columns, fringes in ((12, 4096, 8000, (6, 7, 8)),
                                         (13, 8192, 4000, (13, 14, 15))):
        e1 = NP.e1_na(bits, n=columns, uniform=True)
        d, _ = NP.d_na(bits, e1, n=columns, uniform=True)
        leak = d / 2
        mass = leak * rows / 2
        print(f'm={rows}: certified B={leak:.5f}, mean-field '
              f'B={bulk_floor(rows):.2e}, gate mass {mass:.2f} rows')
        for f in fringes:
            floor, _ = worst_escape(mass, f, rows, 500)
            certified = moderate_bound(round(mass), f, columns, rows)[0]
            print(f'  f={f}: floor E/a={floor / mass:.3e}, one-round certified '
                  f'E/a={certified / round(mass):.3f}, '
                  f'pyramid J<={(f + 1) * (f + 2) * (f + 3) // 6}, need 1/128')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--budget-gate', action='store_true')
    ap.add_argument('--rows', type=int, default=4096)
    ap.add_argument('--columns', type=int, default=8000)
    ap.add_argument('--fringes', type=int, nargs='+', default=[6, 7, 8])
    ap.add_argument('--masses', type=float, nargs='+',
                    default=[0.25, 0.5, 1, 2, 4, 8, 12, 16])
    ap.add_argument('--cap', type=int, default=400)
    args = ap.parse_args()
    if args.budget_gate:
        budget_gate()
        return
    m, n = args.rows, args.columns
    print(f'bulk floor B (fraction of sender, one side): {bulk_floor(m):.3e}')
    print('i rows | ' + ' | '.join(
        f'f={f}: floor E/i, certified E/i' for f in args.fringes))
    for i in args.masses:
        cells = []
        for f in args.fringes:
            floor, _ = worst_escape(i, f, m, args.cap)
            certified = ''
            if float(i).is_integer():
                value = moderate_bound(int(i), f, n, m)
                value = value[0] if isinstance(value, tuple) else value
                certified = f'{value / i:.3f}'
            cells.append(f'{floor / i:.2e}, {certified or "-"}')
        print(f'{i:6} | ' + ' | '.join(cells))


if __name__ == '__main__':
    main()
