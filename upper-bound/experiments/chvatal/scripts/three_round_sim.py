#!/usr/bin/env python3
"""Leak and column spread after 1, 2, 3 scramble rounds (random and two-level inputs).
Run from sub300 prefix-flux (imports d2_bulk_attack):  python three_round_sim.py 1000 8192"""
import sys, numpy as np
sys.path.insert(0, '.')
import d2_bulk_attack as B
def adv(h, perm, rows):
    idx = np.arange(rows)[:, None]
    return np.bincount(perm[idx < h[None, :]], minlength=len(h))
def leak(x): return float(np.maximum(x - x.mean(), 0).sum()) / len(x)
n, m = int(sys.argv[1]), int(sys.argv[2])
for seed in range(2):
    st = B.Stage(n, m, seed)
    rng = np.random.default_rng(seed + 99)
    s3 = np.stack([rng.permutation(n) for _ in range(m)]).astype(np.int32)
    for name, h in [('random', np.random.default_rng(seed).integers(0, m, n)),
                    ('two-level attack', None)]:
        if h is None:
            v, up = B.two_level(st, seed)
            h = B.climb(st, np.where(up, 1.0, -1.0))
        r1 = adv(h, st.s1, m); r2 = adv(r1, st.s2, m); r3 = adv(r2, s3, m)
        print(f'seed {seed} {name:17s} leak rows r1 {leak(r1):7.2f} r2 {leak(r2):6.2f} r3 {leak(r3):6.3f} | '
              f'spread (max-min) r1 {r1.max()-r1.min()} r2 {r2.max()-r2.min()} r3 {r3.max()-r3.min()}', flush=True)
