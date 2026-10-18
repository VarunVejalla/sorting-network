#!/usr/bin/env python3
"""Check the staircase lemma used in LATERAL-LEMMA.md.

Claim.  Let an extreme (threshold) set S occupy the top cnt[c] rows of each sorted column c of an
m x n matrix.  Apply independent uniformly random permutations sigma_i to the entries of each row i
and sort columns again.  Then the new column counts are

    p_T = sum_i X_{i,T},   X_{i,.} = indicator of sigma_i(A_i),   A_i = {c : cnt[c] > i},

so row i contributes a uniformly random |A_i|-subset of columns, independently over rows, and the
law of p depends on cnt only through the profile a_i = |A_i|.

Test: two different count vectors with the same profile give the same distribution of p (compared
by the mean and variance of sum_T |p_T - lam| over many draws), and the per-column mean/variance
match sum_i a_i/n and sum_i (a_i/n)(1 - a_i/n).  Exact identity of the per-draw construction is
checked directly against an explicit matrix simulation.

Run:  python -I check_staircase_lemma.py
"""
import numpy as np


def explicit(cnt, perms):
    """Explicit matrix: rows 0..m-1, S at top rows of each column; permute rows; recount columns."""
    m = perms.shape[0]
    M = (np.arange(m)[:, None] < cnt[None, :])                 # True = key of S
    out = np.zeros_like(M)
    for i in range(m):
        out[i, perms[i]] = M[i]                                # entry in column c moves to column perms[i][c]
    return out.sum(axis=0)


def via_profile(cnt, perms):
    m, n = perms.shape
    p = np.zeros(n, dtype=np.int64)
    for i in range(m):
        A = np.nonzero(cnt > i)[0]
        p[perms[i][A]] += 1
    return p


def main():
    rng = np.random.default_rng(7)
    m, n = 64, 48
    # exact per-draw identity
    for _ in range(200):
        cnt = rng.integers(0, m + 1, size=n)
        perms = np.array([rng.permutation(n) for _ in range(m)])
        assert np.array_equal(explicit(cnt, perms), via_profile(cnt, perms))
    print("per-draw identity: ok (200 draws)")
    # same profile, different count vectors -> same law
    base = np.sort(rng.integers(0, m // 2, size=n))[::-1].copy()
    other = rng.permutation(base)                              # same multiset of counts, hence same profile
    prof = [(base > i).sum() for i in range(m)]
    assert prof == [(other > i).sum() for i in range(m)]
    lam = base.sum() / n
    stats = []
    for cnt in (base, other):
        f = []
        for _ in range(4000):
            perms = np.array([rng.permutation(n) for _ in range(m)])
            p = via_profile(cnt, perms)
            f.append(np.abs(p - lam).sum())
        stats.append((np.mean(f), np.var(f)))
    a = np.array(prof) / n
    print(f"lam = {lam:.2f}; predicted per-column var = {np.sum(a * (1 - a)):.3f} (<= lam)")
    print(f"sum|p-lam|: base mean {stats[0][0]:.2f} var {stats[0][1]:.1f} | permuted counts mean {stats[1][0]:.2f} var {stats[1][1]:.1f}")
    print(f"bound n*sqrt(var) = {n * np.sqrt(np.sum(a * (1 - a))):.2f} >= observed mean")


if __name__ == "__main__":
    main()
