"""Least f for the double-duality fringe route with the centred round-2 cost (model).

Round 2 with phi(h) = lam h + mu (h - b)_+^2:  sum_{v in S} w_v <= lam j + mu E_b + x'_s(lam, mu, b),
E_b = sum_u (z_u - b)_+^2 bounded from the round-1 profile s_k. Least f at j:
max_s [ min_{lam,mu,b} (lam j + mu E_b + x'_s) - allowed ] / s,  allowed = j/J (0 for j < J).
Usage: python -I dense_check2.py [n] [J]
"""
import importlib.util
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("fd", os.path.join(HERE, "fringe_duality.py"))
fd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fd)

n = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 ** 20
J = int(float(sys.argv[2])) if len(sys.argv) > 2 else 190000
delta = 1 / 8
logfail = math.log(n * 1e4 * 100 * 50)
lams1 = [float(v) for v in np.geomspace(1e-6, 0.5, 24)]
S_GRID = sorted(set([1, 2, 4, 8, 16, 64, 256] + [int(v) for v in np.geomspace(1024, n - 1, 8)]))
print(f"n = {n}, J = {J}", flush=True)
F_CAND = int(float(sys.argv[3])) if len(sys.argv) > 3 else 1200
for j in [J, 3 * J, 10 * J, 40 * J, int(delta * F_CAND * n) // 4, int(delta * F_CAND * n)]:
    sk = fd.s_profile(n, j, logfail, lams1)
    mean = j / n
    bs = sorted(set([0] + [int(mean * c) for c in (1.0, 1.2, 1.5, 2.0, 3.0)]))
    Eb = {b: fd.excess_energy(sk, b) for b in bs}
    need, arg = 0.0, None
    allowed = j / J if j >= J else 0.0
    for s in S_GRID:
        p = s / n
        best = math.inf
        for b in bs:
            for lam in [p * c for c in (0.0, 0.5, 1.0, 1.5)] + [1e-6, 1e-5]:
                for mu in np.geomspace(1e-10, 1e-2, 14):
                    v = lam * j + mu * Eb[b] + fd.x_round2c(n, s, float(lam), float(mu), b, logfail)
                    best = min(best, v)
        val = (best - allowed) / s
        if val > need:
            need, arg = val, s
    print(f"  j = {j:12d} (mean {mean:8.2f}): K = {len(sk)}, E_0 = {Eb[0]:.3e}; least f = {math.ceil(need)} "
          f"(binding s = {arg})", flush=True)
