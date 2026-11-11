#!/usr/bin/env python3
"""Floor on spectral (quadratic-majorant) certificates of the bulk leak.

Each column's contribution is F(sigma) = max_k (x_k - mu k), where x_k = 1_[0,k) . sigma
and sigma lies in {+-1/2}. A spectral certificate bounds F <= sigma^T Q sigma + c0 on
R^K. By the S-lemma this needs Q >= g_k 1_k 1_k^T for every k, where
g_k = 1/(4(mu k + c0)). Summed over columns, lambda_max(sum Q) is at least the average
trace, so the certificate is at least c0 + tr(Q)/4 per side of the walk.

By weak duality, min tr Q >= (tr sqrt(Sigma_rho))^2 for any distribution rho over k,
where Sigma_rho = sum rho_k g_k 1_k 1_k^T. Multiplicative-weights ascent picks rho.
Rows are grouped into blocks of b. That drops constraints, so the result is still a
lower bound, and it rises as b shrinks.

This is the regime n >> m, where each walk visits distinct columns. Round 2 adds
mu * D for a round-1 spread D, in rows. Round 1 has no penalty (mu = 0).

    python d2_spectral_floor.py --block 16
"""
import argparse
from fractions import Fraction

import numpy as np


def min_trace_floor(g, b, iters):
    """Lower bound on min tr Q with Q >= g[k] 1 1^T over prefixes (k+1)*b rows."""
    L = len(g)
    idx = np.maximum.outer(np.arange(L), np.arange(L))
    rho = np.ones(L) / L
    best = 0.0
    best_rho = rho.copy()
    for it in range(iters):
        tail = np.cumsum((rho * g)[::-1])[::-1]
        w, V = np.linalg.eigh(b * tail[idx])
        w = np.clip(w, 1e-300, None)
        value = np.sqrt(w).sum() ** 2
        if value > best:
            best = value
            best_rho = rho.copy()
        root_inv = (V / np.sqrt(w)) @ V.T
        quad = np.diag(np.cumsum(np.cumsum(root_inv, axis=0), axis=1))
        grad = 0.5 * g * b * quad
        rho = rho * np.exp(2.0 / np.sqrt(it + 1) * grad / grad.max())
        rho /= rho.sum()
    return best, best_rho


def rational_distribution(rho, denominator=10**9):
    """Round a numerical distribution to an exact normalized rational one."""
    weights = [max(0, int(round(float(x) * denominator))) for x in rho]
    if sum(weights) == 0:
        raise ValueError("cannot rationalize a zero distribution")
    total = sum(weights)
    return [Fraction(x, total) for x in weights]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--rows', type=int, default=8192)
    ap.add_argument('--block', type=int, default=16)
    ap.add_argument('--spreads', type=float, nargs='+', default=[95, 123])
    ap.add_argument('--mus', type=float, nargs='+', default=[0.1, 0.12, 0.14, 0.17, 0.2, 0.25])
    ap.add_argument('--c0s', type=float, nargs='+', default=[0.0, 0.02, 0.05, 0.1, 0.2])
    args = ap.parse_args()
    K, b = args.rows // 2, args.block
    L = K // b
    k = np.arange(1, L + 1) * b
    unit, _ = min_trace_floor(np.ones(L), b, 400)
    print(f'round 1: T_unit/K = {unit / K:.3f}, spectral spread floor '
          f'{np.sqrt(2 * unit):.1f} rows', flush=True)
    for D in args.spreads:
        best = min((mu * D + c0 + min_trace_floor(
                    1 / (4 * (mu * k + c0)), b, 200)[0] / 2, mu, c0)
                   for mu in args.mus for c0 in args.c0s)
        print(f'round 2 at spread {D:.0f}: numerical spectral floor '
              f'{best[0]:.2f} rows (mu {best[1]}, c0 {best[2]})', flush=True)


if __name__ == '__main__':
    main()
