#!/usr/bin/env python3
"""Sanity simulation: how far (in blocks) does a sort-scramble-sort separator misplace keys?

m x n matrix, keys = ranks 0..mn-1.  One round: sort columns, row scramble (row r: entry in column c
moves to column perm[r][c]), sort columns.  Two rounds: one more scramble + sort.  Output rows are cut
into k equal bands (the blocks B_j); a key's correct band is (rank // n) // (m/k).  We report the
misplaced mass by band distance and the row displacement.

Inputs: 'random' (uniform permutation) and 'adv' (adversary chosen AFTER the scramble, the backward
closure of docs/chvatal-fringe-obstruction.md aimed at band boundary R: for s target output columns t,
mark in each row r < H the input cell mapped into t, close upward (small keys sit at the top), give
the marked cells the smallest ranks; s as large as the budget R*n allows).  H = R + 2*m/k + 1 aims
at band distance 2.  Also a fringe test: the j = dF*f*n smallest keys vs the top f rows.
"""
import sys
import numpy as np


def scramble_sort(M, perms):
    for P in perms:
        M = np.sort(M, axis=0)
        out = np.empty_like(M)
        out[np.arange(M.shape[0])[:, None], P] = M
        M = out
    return np.sort(M, axis=0)


def stats(out, m, n, k):
    band_rows = m // k
    rows = np.broadcast_to(np.arange(m)[:, None], out.shape)
    true_row = out // n
    disp = rows - true_row
    bd = np.abs(rows // band_rows - true_row // band_rows)
    tot = m * n
    return dict(mis=(bd >= 1).sum() / tot, far=(bd >= 2).sum() / tot, far_n=int((bd >= 2).sum()),
                maxdisp=int(np.abs(disp).max()), q999=float(np.quantile(np.abs(disp), 0.999)))


def adversary(m, n, k, perm, R, H, rng):
    inv = np.argsort(perm, axis=1)            # inv[r, t] = input column mapped to t in row r
    h = np.zeros(n, dtype=np.int64)
    budget = R * n
    used_t = 0
    for t in rng.permutation(n):
        h2 = h.copy()
        cols = inv[:H, t]
        np.maximum.at(h2, cols, np.arange(H) + 1)
        if h2.sum() > budget:
            break
        h = h2
        used_t += 1
    # marked cells: rows < h[c] of column c get the smallest ranks; everything else random
    M = np.empty((m, n), dtype=np.int64)
    mask = np.arange(m)[:, None] < h[None, :]
    nm = int(mask.sum())
    small = rng.permutation(nm)
    rest = nm + rng.permutation(m * n - nm)
    M[mask] = small
    M[~mask] = rest
    return M, used_t, nm


def main(m=1024, n=1024, k=8, trials=3, seed=1):
    rng = np.random.default_rng(seed)
    print(f"m={m} n={n} k={k} band={m//k} rows; Lemma 6.1 eps_B(m)={np.sqrt(2*(1+np.log(m))/m):.4f}, "
          f"1/sqrt(m)={1/np.sqrt(m):.4f}")
    for rounds in (1, 2):
        for trial in range(trials):
            perms = [np.argsort(rng.random((m, n)), axis=1) for _ in range(rounds)]
            M = rng.permutation(m * n).reshape(m, n)
            s = stats(scramble_sort(M, perms), m, n, k)
            print(f"rounds={rounds} random : misplaced {s['mis']:.2e} (per boundary {s['mis']/(k-1):.2e}) "
                  f"dist>=2 {s['far']:.1e} ({s['far_n']} keys) max|disp|={s['maxdisp']} q99.9={s['q999']:.0f}")
            for R in (m // k, m // 2):
                H = R + 2 * (m // k) + 1
                Ma, used, nm = adversary(m, n, k, perms[0], R, H, rng)
                s = stats(scramble_sort(Ma, perms), m, n, k)
                print(f"rounds={rounds} adv R={R:4d} H={H:4d} targets={used:4d} marks={nm:7d}: misplaced {s['mis']:.2e} "
                      f"dist>=2 {s['far']:.2e} ({s['far_n']} keys) max|disp|={s['maxdisp']}")
            # fringe test: top f rows, j = dF f n smallest keys, uniform and adversarial (concentrated) inputs
            f = m // 32
            for dF in (128 / 4095, 0.5, 0.9):
                j = int(dF * f * n)
                Mf = rng.permutation(m * n).reshape(m, n)
                o = scramble_sort(Mf, perms)
                esc_r = int(((o < j) & (np.arange(m)[:, None] >= f)).sum())
                Mfa, used, nm = adversary(m, n, k, perms[0], max(1, j // n), 2 * f + 1, rng)
                # adversary builds marks with budget j: re-rank so that exactly ranks < j are 'small'
                o = scramble_sort(Mfa, perms)
                esc_a = int(((o < min(j, nm)) & (np.arange(m)[:, None] >= f)).sum())
                print(f"   fringe f={f} dF={dF:.3f} j={j}: escapes random {esc_r}, adversarial {esc_a} "
                      f"(targets {used}, j_used {min(j, nm)})")


if __name__ == "__main__":
    a = [int(v) for v in sys.argv[1:]]
    main(*a)
