#!/usr/bin/env python3
"""Brute-force check of the walk-maximum bound for one scramble round (WALK-BOUND.md).

Setting (BULK2.md notation).  A Boolean m x n matrix whose columns are sorted, column j holding c_j
ones in its bottom rows 0..c_j-1.  A row scramble applies an independent permutation sigma_r of the
n columns to each row r; output column T then holds count(T) = #{r : c_{sigma_r^{-1}(T)} > r} ones,
and after the final column sort onesAboveBottom(c, sigma, i) = sum_T (count(T) - i)_+.

Claim (deterministic, for every sigma).  If total(c) <= n i then

    onesAboveBottom(c, sigma, i) <= B(sigma) := max_S sum_j max_{0<=h<=m} W_j^S(h),
    W_j^S(h) = sum_{r<h} ( [sigma_r(j) in S] - |S|/n ).

B does not depend on c or i.  The script checks the inequality exhaustively over all c (and all i
with total(c) <= n i) for random sigma at small (m, n), and reports how close the true worst case
max_c onesAboveBottom comes to B.

Run:  python -I check_walk_bound.py
"""
import itertools

import numpy as np


def ones_above_bottom(c, sig_inv, i):
    m, n = sig_inv.shape
    # count(T) = #{ r : c[sig_inv[r, T]] > r }
    cnt = (c[sig_inv] > np.arange(m)[:, None]).sum(axis=0)
    return int(np.maximum(cnt - i, 0).sum())


def walk_bound(sig):
    m, n = sig.shape
    best = 0.0
    for s in range(1, n + 1):
        for S in itertools.combinations(range(n), s):
            inS = np.zeros(n, bool)
            inS[list(S)] = True
            # increments for column j at row r: [sig[r, j] in S] - s/n
            inc = inS[sig].astype(float) - s / n            # shape (m, n), sig[r, j] = sigma_r(j)
            W = np.vstack([np.zeros(n), np.cumsum(inc, axis=0)])
            best = max(best, float(W.max(axis=0).sum()))
    return best


def main():
    rng = np.random.default_rng(29)
    for m, n in ((4, 4), (5, 5), (6, 5), (6, 6), (8, 5)):
        worst_ratio = 0.0
        for trial in range(6):
            sig = np.array([rng.permutation(n) for _ in range(m)])        # sig[r, j] = sigma_r(j)
            sig_inv = np.argsort(sig, axis=1)                             # sig_inv[r, T] = sigma_r^{-1}(T)
            B = walk_bound(sig)
            true_max = 0
            for c in itertools.product(range(m + 1), repeat=n):
                c = np.array(c)
                tot = int(c.sum())
                i0 = -(-tot // n)                                         # smallest i with tot <= n i
                for i in range(max(i0, 0), m + 1):
                    v = ones_above_bottom(c, sig_inv, i)
                    assert v <= B + 1e-9, (m, n, trial, c, i, v, B)
                    true_max = max(true_max, v)
            worst_ratio = max(worst_ratio, true_max / B if B > 0 else 0)
            print(f"m={m} n={n} trial {trial}: max_c onesAboveBottom = {true_max:3d}  <=  B = {B:6.2f}", flush=True)
        print(f"  ok: inequality holds for every c and i; max ratio true/B = {worst_ratio:.2f}")


if __name__ == "__main__":
    main()
