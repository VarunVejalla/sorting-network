#!/usr/bin/env python3
"""Kill test: does any designed round-1 scramble beat the 1/W round-1 tail?

Model (as d2_bulk_attack.py): m rows x n columns, column-sorted 0-1 input given by heights h,
scramble s1[r, u] = middle column receiving cell (r, u); each row of s1 is a permutation.
Tail(W) = sum_c (mid_c - mean - W)_+ / (m n).

Attack (exact runs, so lower bounds on the worst case for that scramble): price middle
columns in a target set S at +1 and the rest at -neg*p/(1-p); every input column climbs to
the maximum of its walk. Target sets: random S (any fraction p), and the design-aware set
"first p n destinations of input column 0" (catches structured designs).

Designs: random (independent random row permutations), cyclic (u + r mod n), affine
(a_r u + b_r mod n, n prime), latin (blocks of n rows, each a randomly isotoped cyclic Latin
square, so every input column visits every middle column once per block), kronecker
(u + floor(n frac(r phi)) mod n, a low-discrepancy shift sequence).

    python designed_scramble_screen.py 1009 8192      # m > n
    python designed_scramble_screen.py 4099 1024      # n > m (top-level nodes)
"""
import math
import sys

import numpy as np

sys.path.insert(0, __import__('os').path.dirname(__file__))
from stage_screen import tail_frac  # noqa: E402


def design(name, n, m, seed=0):
    rng = np.random.default_rng(seed)
    r = np.arange(m)[:, None]
    u = np.arange(n)[None, :]
    if name == 'random':
        return np.stack([rng.permutation(n) for _ in range(m)])
    if name == 'cyclic':
        return (u + r) % n
    if name == 'affine':
        a = rng.integers(1, n, m)[:, None]
        b = rng.integers(0, n, m)[:, None]
        return (a * u + b) % n
    if name == 'latin':
        out = np.empty((m, n), dtype=np.int64)
        for start in range(0, m, n):
            k = min(n, m - start)
            pi, tau, sig = rng.permutation(n), rng.permutation(n), rng.permutation(n)
            out[start:start + k] = sig[(pi[:k, None] + tau[None, :]) % n]
        return out
    if name == 'kronecker':
        phi = (math.sqrt(5) - 1) / 2
        c = np.floor(n * ((np.arange(m) * phi) % 1.0)).astype(np.int64)[:, None]
        return (u + c) % n
    raise ValueError(name)


def tails(s1, Ws, ps=(0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5), seeds=3,
          negs=(1.0, 0.5, 0.2, 0.05)):
    m, n = s1.shape
    best = np.zeros(len(Ws))
    flat = s1.ravel()
    for p in ps:
        k = max(1, int(p * n))
        sets = [np.random.default_rng(100 + s).permutation(n) < k for s in range(seeds)]
        aware = np.zeros(n, bool)
        aware[s1[:, 0][:k]] = True                        # first destinations of column 0
        sets.append(aware)
        for S in sets:
            for neg in negs:
                price = np.where(S, 1.0, -neg * p / (1 - p))
                walk = np.vstack([np.zeros(n), np.cumsum(price[s1], axis=0)])
                h = np.argmax(walk, axis=0)
                filled = (np.arange(m)[:, None] < h[None, :]).ravel()
                mid = np.bincount(flat[filled], minlength=n)
                dev = mid - mid.mean()
                for i, W in enumerate(Ws):
                    best[i] = max(best[i], float(np.maximum(dev - W, 0).sum()) / (m * n))
    return best


def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    names = sys.argv[3].split(',') if len(sys.argv) > 3 else ['random', 'affine', 'latin',
                                                               'kronecker', 'cyclic']
    sq = math.sqrt(m)
    Ws = [int(round(f * sq)) for f in (0.5, 1, 2, 4, 8)]
    L = math.log2(m)
    cert = [float(tail_frac(np.array(L), np.array(float(W)))) for W in Ws]
    print(f'n={n} m={m}  W = {Ws}', flush=True)
    print(f'{"certified":10s} ' + ' '.join(f'{c:9.2e}' for c in cert), flush=True)
    for name in names:
        t = tails(design(name, n, m), Ws)
        slope = np.polyfit(np.log(Ws), np.log(np.maximum(t, 1e-12)), 1)[0]
        print(f'{name:10s} ' + ' '.join(f'{x:9.2e}' for x in t) + f'   log-log slope {slope:+.2f}',
              flush=True)


if __name__ == '__main__':
    main()
