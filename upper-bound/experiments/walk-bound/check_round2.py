#!/usr/bin/env python3
"""Checks for the round-2 proof (ROUND2.md).

(1) Exhaustive, small (m, n): for every state c' of exact mass n i and every S,
        sum_{T in S} (count(T) - i) <= lam * sum_j |c'_j - i'| + sum_j Y_j^{S,i'}(lam)
    for every base row i' and several lam (deterministic: reduction + weak duality).
(2) Simulation: the tail of Y_j^+ = sup_h (W(h) - lam h) against Ville's e^{-theta* x}.
(3) Simulation at moderate (m, n): sum_j Y_j for a fixed S against its NA Chernoff quantile, and the
    exact primal  sup { sum_j X_j(delta_j) : sum |delta_j| <= R }  (DP) against the dual bound.

Run:  python -I check_round2.py
"""
import itertools
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import na_precision as NA  # noqa: E402


def walks(sig, inS):
    m, n = sig.shape
    p = inS.sum() / n
    inc = inS[sig].astype(float) - p                  # inc[r, j]: row r, column j
    return np.vstack([np.zeros(n), np.cumsum(inc, axis=0)])   # W[h, j], h = 0..m


def Y_cols(W, base, lam):
    m = W.shape[0] - 1
    h = np.arange(m + 1)
    X = W - W[base]                                   # X[h, j] = W(h) - W(base), delta = h - base
    return (X - lam * np.abs(h - base)[:, None]).max(axis=0)


def part1():
    rng = np.random.default_rng(1)
    print("(1) exhaustive deterministic check")
    for m, n in ((4, 4), (5, 4), (6, 5), (5, 5), (8, 4)):
        C = np.array(list(itertools.product(range(m + 1), repeat=n)))
        C = C[C.sum(axis=1) % n == 0]                  # exact mass n i
        I = C.sum(axis=1) // n
        worst, ncheck = -np.inf, 0
        for trial in range(4):
            sig = np.array([rng.permutation(n) for _ in range(m)])
            sig_inv = np.argsort(sig, axis=1)
            cnt = (C[:, sig_inv] > np.arange(m)[None, :, None]).sum(axis=1)    # (states, n)
            for s in range(1, n):
                for S in itertools.combinations(range(n), s):
                    inS = np.zeros(n, bool); inS[list(S)] = True
                    W = walks(sig, inS)
                    lhs = (cnt[:, inS] - I[:, None]).sum(axis=1)
                    for base in range(m + 1):
                        dist = np.abs(C - base).sum(axis=1)
                        for lam in (0.0, 0.1, 0.3, 1.0):
                            rhs = lam * dist + Y_cols(W, base, lam).sum()
                            gap = (lhs - rhs).max()
                            assert gap <= 1e-9, (m, n, S, base, lam, gap)
                            worst = max(worst, gap)
                            ncheck += len(C)
        print(f"  m={m} n={n}: ok over {ncheck} (state, S, base, lam) cases; max lhs - rhs = {worst:.3f}",
              flush=True)


def part2():
    rng = np.random.default_rng(2)
    print("(2) tail of Y+ = sup_h (W(h) - lam h) vs exp(-theta* x)")
    for p, lam, m in ((0.5, 0.02, 4000), (1 / 16, 0.01, 4000), (15 / 16, 0.01, 4000)):
        th = NA.theta_star(p, lam)
        trials = 4000
        inc = (rng.random((trials, m)) < p) - p - lam
        Y = np.maximum(np.cumsum(inc, axis=1).max(axis=1), 0)
        row = []
        for q in (0.5, 1, 2, 3):
            x = q / th
            row.append(f"x={q:.1f}/th: emp {np.mean(Y >= x):.3f} <= {math.exp(-q):.3f}")
        print(f"  p={p:.4f} lam={lam}: " + ";  ".join(row), flush=True)


def part3():
    rng = np.random.default_rng(3)
    print("(3) moderate (m, n): sum_j Y_j at the theorem's lam vs NA Chernoff, and primal vs bound")
    for m, n in ((4096, 16),):
        E1 = NA.e1_na(math.log2(m), n=n)
        R = E1 * m * n
        base = m // 2
        sums, prim, dual = [], [], []
        for s in (n // 2, 1):
            p = s / n
            lnN = math.log(1 / 0.05)                  # a single S and base: 95% quantile
            bound, lam = NA.round2_size(p, n, R, lnN)
            vals, pv = [], []
            for t in range(200):
                sig = np.array([rng.permutation(n) for _ in range(m)])
                inS = np.zeros(n, bool); inS[:s] = True
                W = walks(sig, inS)
                Y = Y_cols(W, base, lam)
                vals.append(lam * R + Y.sum())
                if t < 12:
                    pv.append(primal_exact(W, base, R))
            vals, pv = np.array(vals), np.array(pv)
            print(f"  m={m} n={n} s={s}: R={R:.0f}  95% bound {bound:7.1f};  dual lam R + sum Y: "
                  f"q95 {np.quantile(vals, 0.95):7.1f} mean {vals.mean():7.1f};  primal mean "
                  f"{pv.mean():7.1f} max {pv.max():7.1f}", flush=True)


def primal_exact(W, base, R):
    """Exact primal value via (max,+) convolution of the per-column best-at-cost curves."""
    m = W.shape[0] - 1
    Rint = int(R)
    best = np.zeros(Rint + 1)
    for j in range(W.shape[1]):
        X = W[:, j] - W[base, j]
        up = X[base:base + Rint + 1]
        dn = X[max(base - Rint, 0):base + 1][::-1]
        L = Rint + 1
        cur = np.full(L, -np.inf)
        cur[:len(up)] = up
        cur[:len(dn)] = np.maximum(cur[:len(dn)], dn)
        cur = np.maximum.accumulate(cur)
        # (max,+) convolution: new[w] = max_{u<=w} best[w-u] + cur[u]
        new = np.full(L, -np.inf)
        for u in range(L):
            new[u:] = np.maximum(new[u:], best[:L - u] + cur[u])
        best = new
    return best[-1]


if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3"]
    if "1" in which:
        part1()
    if "2" in which:
        part2()
    if "3" in which:
        part3()
