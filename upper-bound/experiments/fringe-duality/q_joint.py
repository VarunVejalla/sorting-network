"""Round-1 energy Q = sum z^2 from ONE joint inequality across dyadic levels (model).

Levels S_i = {u : 2^i <= z_u < 2^{i+1}}, s_i = |S_i|. Weighted duality with a = 2^i on S_i and one lambda:
  sum_i 2^i sum_{S_i} z <= lam j + sum_i 2^i x_{s_i}(lam / 2^i) + Delta,
with x_s the set statistic (union over sets of size s) and Delta the collision term, E Delta ~ Q' rho/(2 lam^2),
rho = sum_i 2^i s_i / n <= 2 j / n (modelled by its expectation, inflated 2x). Since sum_{S_i} z >= 2^i s_i
and z < 2^{i+1} on S_i:  Q <= sum_i 4^{i+1} s_i  subject to
  sum_i [ 4^i s_i (1 - 2 rho/(2 lam^2)) - 2^i x_{s_i}(lam/2^i) ] <= lam j.
Maximised per level with a Lagrange multiplier (levels are independent given the multiplier).
Usage: python -I q_joint.py [n]
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
logfail = math.log(n * 1e4 * 100 * 50)


LAMS1 = [float(v) for v in np.geomspace(1e-6, 0.5, 24)]
_SK = {}


def q_joint(j, lam):
    if j not in _SK:
        _SK[j] = fd.s_profile(n, j, logfail, LAMS1)      # per-level caps from the set bound
    sk = _SK[j]
    rho = 2 * j / n
    shrink = 1 - 2 * rho / (2 * lam ** 2)
    if shrink <= 0:
        return math.inf
    I = int(math.log2(4 * math.sqrt(j))) + 2
    sgrid = sorted(set([0] + [int(v) for v in np.geomspace(1, max(2, j), 60)]))
    levels = []
    for i in range(I + 1):
        opts = []
        cap = sk[2 ** i - 1] if 2 ** i - 1 < len(sk) else 0
        for s in sgrid:
            if s * 2 ** i > j or s > cap:
                break
            cost = 4 ** i * s * shrink - (2 ** i * fd.x_round1(n, s, lam / 2 ** i, logfail) if s > 0 else 0.0)
            val = 4 ** (i + 1) * s
            opts.append((cost, val))
        levels.append(opts)
    # weak duality: for every nu >= 0, max_{feasible} sum val <= sum_i max_s (val - nu cost) + nu lam j
    best = math.inf
    for nu in np.geomspace(1e-2, 1e3, 120):
        b = sum(max(v - nu * c for c, v in opts) for opts in levels) + nu * lam * j
        best = min(best, b)
    return best


for j in (1000, 10000, 100000, 190000):
    res = min((q_joint(j, lam), lam) for lam in (0.6, 0.75, 1.0, 1.3, 1.7))
    print(f"j = {j:8d}: joint Q <= {res[0]:.3e}  (Q/j = {res[0] / j:6.1f}) at lam = {res[1]}", flush=True)
