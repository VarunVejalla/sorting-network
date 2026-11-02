#!/usr/bin/env python3
"""First-moment limits for the two-round bulk leak, the best a union proof can give.

Round 1. For a middle half S, input column u's walk has i.i.d. +-1/2 steps, and its
best height gains X_u = 0.5 max(0, M_up, M_down): two independent simple-walk
maxima of length m/2, with exact law from the reflection principle. The middle
spread (mean |d|) is 2 * mean X. A union over the 2^n halves is vacuous below the
level x with rate I(x) = ln 2.

Round 2. For a final half T, take any middle profile with mean |d| <= D. Each
middle column's walk has i.i.d. +-1/2 steps, so with a multiplier mu the leak is at
most mean_v max_d (W_v(d) - mu |d|) + mu D. The union over T uses the same ln 2
level, estimated by Monte Carlo. Columns are treated as independent given S or T.

At D = 192, the certified round-1 budget, round 2 reproduces the certified leak
(17.4 against 17.7 rows). Heuristic: independence is assumed, not proved.

    python d2_bulk_limits.py --rows 8192 --budgets 80 95 123 192
"""
import argparse
import math

import numpy as np
from scipy.special import logsumexp
from scipy.stats import binom

LN2 = math.log(2)


def union_level(log_p, x, theta_max, count=2000):
    thetas = np.linspace(theta_max / count, theta_max, count)
    lam = np.array([float(logsumexp(log_p + t * x)) for t in thetas])

    def rate(level):
        return float(np.max(thetas * level - lam))
    lo, hi = float(np.exp(log_p) @ x), float(x.max())
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if rate(mid) >= LN2 else (mid, hi)
    return hi


def round_one(rows):
    """Typical and union-limit middle spread, in rows."""
    half = rows // 2
    a = np.arange(half + 1)

    def at_least(v):
        return binom.sf(np.ceil((v + half) / 2) - 1, half, 0.5)

    ge = at_least(a) + at_least(a + 1)
    ge[0] = 1.0
    cdf = np.cumsum(ge - np.append(ge[1:], 0.0)) ** 2
    pmf = np.diff(np.concatenate([[0.0], cdf]))
    keep = pmf > 0
    x = 0.5 * a[keep]
    log_p = np.log(pmf[keep])
    typical = float(np.exp(log_p) @ x)
    return 2 * typical, 2 * union_level(log_p, x, 0.5)


def round_two(budgets, samples=400_000, radius=600, seed=1):
    rng = np.random.default_rng(seed)
    mus = [0.01, 0.02, 0.03, 0.05, 0.07, 0.1, 0.15]
    levels = {}
    steps = np.arange(1, radius + 1)
    for mu in mus:
        parts = []
        for _ in range(samples // 20000):
            up = np.cumsum(rng.choice([-0.5, 0.5], (20000, radius)), axis=1) - mu * steps
            dn = np.cumsum(rng.choice([-0.5, 0.5], (20000, radius)), axis=1) - mu * steps
            parts.append(np.maximum(0, np.maximum(up.max(axis=1), dn.max(axis=1))))
        x = np.concatenate(parts)
        log_p = np.full(len(x), -math.log(len(x)))
        levels[mu] = (union_level(log_p, x, 3.0, 300), float(x.mean()))
    out = []
    for budget in budgets:
        union = min(levels[mu][0] + mu * budget for mu in mus)
        typical = min(levels[mu][1] + mu * budget for mu in mus)
        out.append((budget, union, typical))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--rows', type=int, default=8192)
    ap.add_argument('--budgets', type=float, nargs='+', default=[80, 95, 123, 192])
    args = ap.parse_args()
    typical, union = round_one(args.rows)
    print(f'round 1: typical spread {typical:.1f} rows, union limit {union:.1f} rows')
    for budget, u, t in round_two(args.budgets):
        print(f'round 2 at spread {budget:.0f}: union limit {u:.2f} rows, typical final '
              f'half {t:.2f} rows')


if __name__ == '__main__':
    main()
