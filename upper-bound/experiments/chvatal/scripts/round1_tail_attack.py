#!/usr/bin/env python3
"""Attack on the round-1 tail beyond W rows: price +1 into a middle set of fraction p, climb.
Run from sub300 prefix-flux:  python round1_tail_attack.py 1000 8192 <path to these scripts>"""
import sys, numpy as np
sys.path.insert(0, '.')
import d2_bulk_attack as B
sys.path.insert(0, sys.argv[3])
import stage_screen as SS
n, m = int(sys.argv[1]), int(sys.argv[2])
st = B.Stage(n, m, 0)
L = np.log2(m)
for W in [64, 128, 256, 512, 1024]:
    best = 0.0
    for p in [0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5]:
        for seed in range(3):
            rng = np.random.default_rng(seed)
            S = rng.permutation(n) < max(1, int(p * n))
            for neg in [1.0, 0.5, 0.2, 0.05]:
                price = np.where(S, 1.0, -neg * p / (1 - p))
                h = B.climb(st, price)
                mid = st.advance(h, st.s1)
                t = float(np.maximum(mid - mid.mean() - W, 0).sum()) / (m * n)
                best = max(best, t)
    print(f'W={W:5d}: attack tail {best:.3e}   certified tail_frac {float(SS.tail_frac(np.array(L), np.array(float(W)))):.3e}', flush=True)
