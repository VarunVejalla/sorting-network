#!/usr/bin/env python3
"""Calibrate the UB-20 lateral residual: two-round scramble+sort of an extreme set, then cross-sibling merge.

Simulation only (finite, seeded); not a worst-case certificate.

Model.  Sibling v_j holds P misplaced keys that are its largest keys (an extreme set S); sibling
v_{j+1} holds Q = P misplaced keys that are its smallest.  Each sibling runs the two-round separator
on an m x n matrix: independent row permutations sigma1, column sort, independent row permutations
sigma2, column sort.  For an extreme set only the per-column counts matter:

  round 1: cnt1[c] = #S in column c after sigma1 (adversary chooses the input positions);
  sorted columns hold those keys in rows 0..cnt1[c]-1;
  round 2: row i of column c moves to column sigma2_i(c), so
           p[T] = #{ i : cnt1[sigma2_i^{-1}(T)] > i }.

The lateral step merges column c's top band of v_j with column c's bottom band of v_{j+1}; the
residual misplaced mass is sum_c |p_c - q_c| (band height assumed large enough), reported as
rho = residual / P.  The heuristic model in lateral_selfconsistent.py predicts
rho ~ 2*sqrt(C/(pi*lam)) with lam = P/n.

Inputs for v_j:
  random    : S placed uniformly at random among the m*n input positions;
  adversary : spends its budget making a chosen set of target columns receive h keys each after
              round 2 (cost about h^2/2 keys per target), for the h maximising the induced residual;
              the rest of S is random.  v_{j+1} is always random (independent permutations).

Run:  python -I sim_lateral_residual.py
"""
import numpy as np


def round2_counts(cnt1, inv2):
    """cnt1: (n,) round-1 column counts; inv2: (m, n) with inv2[i, T] = sigma2_i^{-1}(T)."""
    m = inv2.shape[0]
    rows = np.arange(m)[:, None]
    return (cnt1[inv2] > rows).sum(axis=0)


def random_cnt1(rng, m, n, P):
    pos = rng.choice(m * n, size=P, replace=False)
    # sigma1 is a uniformly random bijection per row, so a uniformly random placement of S maps to a
    # uniformly random placement in the round-1 matrix: column = pos % n after relabelling.
    return np.bincount(pos % n, minlength=n)


def adversary_cnt1(rng, m, n, P, inv2, h, targets):
    """Make each target column receive >= h keys after round 2; fill the rest randomly."""
    cnt1 = np.zeros(n, dtype=np.int64)
    for T in targets:
        for i in range(h):
            c = inv2[i, T]
            cnt1[c] = max(cnt1[c], i + 1)
    used = int(cnt1.sum())
    if used > P:
        return None
    if P - used > 0:
        cap = m - cnt1
        extra = np.bincount(rng.choice(np.repeat(np.arange(n), cap), size=P - used, replace=False), minlength=n)
        cnt1 = cnt1 + extra
    return cnt1


def trial(rng, m, n, P, mode):
    inv2_a = np.argsort(np.array([rng.permutation(n) for _ in range(m)]), axis=1)
    inv2_b = np.argsort(np.array([rng.permutation(n) for _ in range(m)]), axis=1)
    q = round2_counts(random_cnt1(rng, m, n, P), inv2_b)
    if mode == "random":
        p = round2_counts(random_cnt1(rng, m, n, P), inv2_a)
        return np.abs(p - q).sum() / P, int(p.max())
    lam = P / n
    best = (0.0, 0)
    for h in sorted({int(lam + s * np.sqrt(lam)) for s in (2, 3, 4, 6, 8, 12, 16)} | {int(2 * lam), int(4 * lam)}):
        if h <= lam or h > m:
            continue
        per = h * (h + 1) // 2
        nt = max(1, min(n, int(0.5 * P / per)))
        targets = rng.choice(n, size=nt, replace=False)
        cnt1 = adversary_cnt1(rng, m, n, P, inv2_a, h, targets)
        if cnt1 is None:
            continue
        p = round2_counts(cnt1, inv2_a)
        r = np.abs(p - q).sum() / P
        if r > best[0]:
            best = (r, int(p.max()))
    return best


def main():
    rng = np.random.default_rng(20261018)
    m, n = 2048, 512
    print(f"m={m} rows, n={n} columns per sibling; rho = sum|p_c - q_c| / P;  model 2*sqrt(C/(pi*lam))")
    print("   lam        P   mode        rho(mean)  rho(max)   max p_c   implied C = pi*lam*rho^2/4")
    for lam in (4, 16, 64, 256, 1024):
        P = lam * n
        if P > m * n // 2:
            continue
        for mode in ("random", "adversary"):
            rs, mx = [], 0
            for _ in range(4):
                r, pm = trial(rng, m, n, P, mode)
                rs.append(r)
                mx = max(mx, pm)
            rmean, rmax = float(np.mean(rs)), float(np.max(rs))
            C = np.pi * lam * rmax ** 2 / 4
            print(f" {lam:5d} {P:8d}   {mode:10s} {rmean:9.4f} {rmax:9.4f}   {mx:7d}   {C:8.2f}", flush=True)


if __name__ == "__main__":
    main()
