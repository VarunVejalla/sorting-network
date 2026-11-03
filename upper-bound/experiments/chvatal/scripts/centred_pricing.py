#!/usr/bin/env python3
"""Price the centred sided invariant (sub500-screen/INDUCTION-v6.md) at ideal separators.

Drives sub500-screen/width_sim.py (per-node width certificate on Chvatal's exact schedule)
at integer (x, y, z), with: far-crossing tails set to 0 and ROUNDF = 0 (optimistic), delta
from (4.5) at the attack eps_F of the structural fringe, and eps_B(m) from tree_pricing.py's
bulk models. For each triple, scans integer L >= 2(x+y) and reports the least L at which every
sender's order-0 ratio is <= 1, and the slope s S(L) (x+y)/(xz).

    python centred_pricing.py --sim <path to sub500-screen> [--depth 14]
"""
import argparse
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ideal_limit_screen import attack_table  # noqa: E402
from tree_pricing import bulk_models  # noqa: E402
import numpy as np  # noqa: E402


def ratio(Sim, Par, x, y, z, d, q, dF, epsB, epsF):
    k, A, nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
    Anu = A * nu
    mu = min(nu / (A * k * k), Fr(dF) * (Anu * k - 1) / (2 * A * A * k * k))
    a_, b_ = float(A * k / nu), epsF / float(Anu)
    disc = 1 - 4 * a_ * b_
    if disc < 0:
        return math.inf
    delta = (1 - math.sqrt(disc)) / (2 * a_)
    if delta * k * A >= 1:
        return math.inf
    ofrac = mu * Anu / (2 * (Anu - 1))
    P = Par(x, y, z)
    S = Sim(P, d, ofrac, epsB, q, delta, float(mu))
    S.A2 = float(A) ** 2
    S.Anu = Anu
    root = S.initial()
    for t in range(P.tf(d)):
        root = S.step(root, t)
    return max(r['order0_ratio_max'][0] for r in S.stats.values() if 'order0_ratio_max' in r)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sim', required=True)
    ap.add_argument('--depth', type=int, default=14)
    ap.add_argument('--triples', default='2,3,2 2,4,2 2,4,3 3,4,3 3,5,3 3,5,4 3,6,4 4,4,3 4,5,3 4,5,4 4,6,4 5,6,4 5,6,5')
    ap.add_argument('--dfs', default='0.5,0.75,1.0')
    ap.add_argument('--sorts', type=int, default=3)
    a = ap.parse_args()
    os.environ.setdefault('CERT_TAIL', '0')
    os.environ.setdefault('CERT_TAIL_W', '0')
    os.environ.setdefault('ROUNDF', '0')
    sys.path.insert(0, a.sim)
    sys.path.insert(0, os.path.join(a.sim, '..', 'slackfree'))
    from width_sim import Sim
    from flowsim import Par
    models = bulk_models(os.environ.get('BULK_CACHE'))
    for tr in a.triples.split():
        x, y, z = map(int, tr.split(','))
        for dF in map(float, a.dfs.split(',')):
            for bname in ('attack', 'certified'):
                found = None
                for L in range(2 * (x + y), 41):
                    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
                    f = 2.0 ** L * (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
                    if f < 4:
                        continue
                    epsF = float(attack_table(np.array([f]), dF)[0])
                    epsB = float(models[bname](L))
                    try:
                        r = ratio(Sim, Par, x, y, z, a.depth, L, dF, epsB, epsF)
                    except Exception as e:  # noqa: BLE001
                        print(f'({tr}) dF={dF} {bname}: error {type(e).__name__}: {e}', flush=True)
                        break
                    if r <= 1:
                        found = (L, r, f)
                        break
                if found:
                    L, r, f = found
                    s = a.sorts * L * (L + 1) / 2 * (x + y) / (x * z)
                    print(f'({tr}) dF={dF} {bname:9s}: L={L} ratio {r:.3f} f {f:.0f} slope {s:.1f}', flush=True)
                else:
                    print(f'({tr}) dF={dF} {bname:9s}: no L <= 40', flush=True)


if __name__ == '__main__':
    main()
