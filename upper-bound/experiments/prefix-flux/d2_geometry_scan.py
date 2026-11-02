#!/usr/bin/env python3
"""Which D2 geometries give a sender-wide three-sort stage room to close.

For Par(x, y, z) with k = 2^x, A = 2^y, nu = 2^-z and sender height m = 2^mu, the up
quota is fixed by mass balance at (k*A*nu - 1) c / (k*A)^2. A bag near capacity
therefore has fringe, feed and return gain

    f = m (k*A*nu - 1) / (2 (k*A)^2),   feed = 1/(A*nu),   gain = 1/nu^2,

whatever quota scaling is chosen: raising the quota raises allocations in proportion.
The price is (x+y)/(x*z) * 3 * mu(mu+1)/2. The formula fringe holds only if the
allocation ratio a/c stays bounded, so the flow check measures the worst `mid`
fringe on the real FlowDAG at two depths, and reports a failed flow assertion.

    python d2_geometry_scan.py
    python d2_geometry_scan.py --flow 3 2 2 13 --depths 12 20 30
"""
import argparse
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..',
                                'slackfree'))
from flowsim import Par  # noqa: E402

from flow_dag import FlowDAG  # noqa: E402


def formula_rows(limit):
    out = []
    for x in range(1, 6):
        for y in range(1, 6):
            for z in range(1, 4):
                k, A, nu = 2 ** x, 2 ** y, F(1, 2 ** z)
                if k * A * nu <= 1:
                    continue
                for mu in range(9, 15):
                    m = 2 ** mu
                    price = F(x + y, x * z) * 3 * mu * (mu + 1) / 2
                    if price >= limit:
                        continue
                    f = m * (k * A * nu - 1) / (2 * (k * A) ** 2)
                    out.append((float(price), (x, y, z), mu, float(f),
                                float(1 / (A * nu)), 4 ** z))
    return sorted(out)


def worst_mid_fringe(params, mu, depth):
    """Smallest mid fringe among senders of at least 4000 columns, or the failure."""
    m = 2 ** mu
    p = Par(*params)
    try:
        flow = FlowDAG(depth, scale=m, p=p, sparse_bottom=True).build()
    except AssertionError:
        return None
    best = None
    for t in range(1, len(flow.rows)):
        for node, (a, pi, _) in flow.rows[t].items():
            if a < 4000 * m or p.role(depth, flow.nodes[node][0], t) != 'mid':
                continue
            f = float(F(m * pi, 2 * a))
            best = f if best is None else min(best, f)
    return best


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit', type=float, default=300)
    ap.add_argument('--min-fringe', type=float, default=12)
    ap.add_argument('--flow', type=int, nargs=4, metavar=('X', 'Y', 'Z', 'MU'))
    ap.add_argument('--depths', type=int, nargs='+', default=[10, 20])
    args = ap.parse_args()
    if args.flow:
        x, y, z, mu = args.flow
        for depth in args.depths:
            print(depth, worst_mid_fringe((x, y, z), mu, depth))
        return
    print('price  (x,y,z)  m     formula f  feed  gain  worst mid f by depth')
    for price, params, mu, f, feed, gain in formula_rows(args.limit):
        if f < args.min_fringe:
            continue
        real = [worst_mid_fringe(params, mu, depth) for depth in args.depths]
        shown = ', '.join('flow fails' if r is None else f'{r:.1f}' for r in real)
        print(f'{price:6.1f} {params} 2^{mu}  {f:6.1f}  {feed:4.1f}  {gain:4d}  {shown}',
              flush=True)


if __name__ == '__main__':
    main()
