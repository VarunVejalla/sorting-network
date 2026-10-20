"""Smallest f for the double-duality fringe route (model) across the whole range of j.

For each j: escapes(f) <= max_s [ g_s - f s ] with g_s = min_mu (mu Q(j) + x'_s(mu)); the contract
needs escapes < j/J (so zero for j < J). g_s does not depend on f, so the least admissible f at this
j is max_s (g_s - j/J) / s, rounded up. jmax = delta f n is checked against the resulting f.

Usage: python -I dense_check.py [n] [J]
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
logfail = math.log(n * 1e4 * 100)
lams = [float(v) for v in np.geomspace(1e-6, 0.5, 30)]
mus = [float(v) for v in np.geomspace(1e-12, 1e-1, 40)]
S_GRID = sorted(set([1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
                    + [int(v) for v in np.geomspace(256, n - 1, 24)]))
print(f"n = {n}, J = {J}, delta = {delta}", flush=True)
f_all = 0
for j in [J // 10, J // 2, J, 2 * J, 5 * J, 20 * J, 100 * J, 1000 * J, int(delta * 4000 * n)]:
    Q = fd.Q_bound(n, j, logfail, lams)
    need, arg = 0.0, None
    for s in S_GRID:
        g = min(mu * Q + fd.x_round2(n, s, mu, logfail) for mu in mus)
        allowed = j / J if j >= J else 0.0
        v = (g - allowed) / s
        if v > need:
            need, arg = v, s
    f_need = math.ceil(need + 1e-9)
    jmax_ok = j <= delta * max(f_need, 1) * n
    f_all = max(f_all, f_need if jmax_ok or j <= J else 0)
    print(f"  j = {j:12d}: Q <= {Q:.3e} (Q/j = {Q / j:8.1f}, Q n/j^2 = {Q * n / j ** 2:8.2f});"
          f" least f = {f_need:6d} (binding s = {arg})", flush=True)
print(f"least f over the checked j: {f_all}", flush=True)
