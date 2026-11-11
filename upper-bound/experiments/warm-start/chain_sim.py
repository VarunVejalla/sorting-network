#!/usr/bin/env python3
"""Back-to-back warm-start stages at one threshold, carrying strays (WARM-START.md, kill test 2).

State: deviations (from the bag mean, in rows) of N middle columns at one threshold.
Each stage:
  1. re-bag: every new column stacks fragments of F distinct old middle columns (F independent
     random permutations of the pool, so each old column feeds F new ones and N stays fixed);
     its deviation is the sum of theirs (fragments taller than the window, so no clamping);
  2. full column sort: a column's height is H + its deviation (strays are absorbed);
  3. row scramble, simulated exactly on the rows where any input column differs;
  4. band of half-width X: the far-cell leak is sum_u (|dev_u| - X)_+ / N rows per column. The strays
     stay in the middle counts, which is pessimistic (no export to other bags).
Stage-0 input: random heights in a window D0, or the aggregated climb attack of
aggregation_attack.py aimed at the stage-1 columns. The adversary acts only through the input.
Exact runs at the modelled threshold; the reuse of each old column F times is a modelling choice.

    python chain_sim.py F N D0 stages
"""
import sys
import numpy as np


def scramble(dev, rng):
    """Middle deviations after one row scramble of sorted columns with heights H + dev."""
    n = len(dev)
    d = np.rint(dev).astype(np.int64)
    lo, hi = int(d.min()), int(d.max())
    if hi == lo:
        return np.zeros(n)
    mid = np.zeros(n)
    for r in range(lo, hi):                       # row r (relative to H): cell is 1 iff d_u > r
        ones = d > r
        perm = rng.permutation(n)
        mid[perm[ones]] += 1                      # row permutation: column u's cell -> perm[u]
    base = np.sum(d > -10 ** 9) * 0               # rows below lo are full in every column
    mid = mid + lo
    return mid - mid.mean()


def aggregate(pool, F, rng):
    n = len(pool)
    out = np.zeros(n)
    for _ in range(F):
        out += pool[rng.permutation(n)]
    return out


def stage0_attack(F, N, D0, rng, p=0.02):
    """Climb inside the window, aimed at the stage-1 columns of a random set J."""
    s1 = np.stack([rng.permutation(N) for _ in range(2 * D0)])
    perms = [rng.permutation(N) for _ in range(F)]   # the stage-1 aggregation, fixed in advance
    J = rng.random(N) < p
    S = np.zeros(N, bool)
    for pm in perms:                                 # new column j stacks old columns pm[j]
        S[pm[J]] = True
    q = S.mean()
    price = np.where(S, 1.0, -q / (1 - q))
    walk = np.vstack([np.zeros(N), np.cumsum(price[s1], axis=0)])
    h = np.argmax(walk, axis=0)
    rows = np.arange(2 * D0)[:, None]
    mid = np.bincount(s1.ravel()[(rows < h[None, :]).ravel()], minlength=N).astype(float)
    mid -= mid.mean()
    return mid, perms


def main():
    F, N, D0, T = (int(a) for a in sys.argv[1:5])
    Wfac = (4, 8, 16)
    for mode in ('random', 'attack'):
        rng = np.random.default_rng(1)
        if mode == 'random':
            pool = scramble(rng.integers(-D0, D0 + 1, N).astype(float), rng)
            perms = None
        else:
            pool, perms = stage0_attack(F, N, D0, rng)
        print(f'{mode}: F={F} N={N} D0={D0}', flush=True)
        for t in range(1, T + 1):
            if perms is not None and t == 1:
                dev = sum(pool[pm] for pm in perms)
            else:
                dev = aggregate(pool, F, rng)
            leaks = [float(np.maximum(np.abs(dev) - F * w, 0).mean()) for w in Wfac]
            print(f'  t={t:2d} input sd {dev.std():7.2f} max {np.abs(dev).max():7.1f} | leak rows at X = F*'
                  + '/'.join(str(w) for w in Wfac) + ': ' + ' '.join(f'{v:.4f}' for v in leaks)
                  + f' | middle sd {pool.std():6.2f}', flush=True)
            pool = scramble(dev, rng)


if __name__ == '__main__':
    main()
