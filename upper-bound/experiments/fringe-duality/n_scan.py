"""n-dependence of the zero-escape fringe bound at j = J (model)."""
import importlib.util, math, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("fd", os.path.join(HERE, "fringe_duality.py"))
fd = importlib.util.module_from_spec(spec); spec.loader.exec_module(fd)
J = int(float(sys.argv[1])) if len(sys.argv) > 1 else 600000
lams = [float(v) for v in np.geomspace(1e-6, 0.5, 24)]
mus = [float(v) for v in np.geomspace(1e-12, 1e-2, 36)]
for e in (18, 20, 25, 30, 40):
    n = 2 ** e
    logfail = math.log(n * 1e4 * 100 * 50)
    Q = fd.Q_bound(n, J, logfail, lams)
    need = 0
    for s in (1, 2, 4, 8, 16, 64):
        g = min(mu * Q + fd.x_round2(n, s, mu, logfail) for mu in mus)
        need = max(need, g / s)
    print(f"n = 2^{e}: Q/J = {Q / J:7.1f}; zero escapes at j = J need f >= {math.ceil(need)}", flush=True)
