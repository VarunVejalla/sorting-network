"""Interval-certified regime (A) cover at the 731.25 point (rd_sparse_iv.worst_merged_iv, unchanged evaluator).

Same cells as rd_scaled_out/coverA_iv.py, parametrized: J = 1651190 (params731), boundary C (env C, default 800),
floor 2^FLOOR (env FLOOR, default 40). j-intervals of ratio 1.15 over [1, JTOP J] (env JTOP, default 1e6), split
at J, evaluated at j_b against the allowance j_a/J (1 for j_b <= J), for every n >= max(2^FLOOR, e^{j_a/(CJ)})
(certified lower bound of the exponent), every set size. Fringe f = 3329 (class A floor): in (A) b = j/n <=
JTOP J / 2^FLOOR < 2, so 8 b < 3329 and the class-aware f_eff is the class-A floor.

Usage:  python -I coverA731_iv.py part nparts      (env JFROM, JTOP in J units restrict the cells: ladder runs)
        python -I coverA731_iv.py near j1/J [j2/J ...]
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import rd_sparse_iv as A  # noqa: E402
from rd_scaled_iv import STATS  # noqa: E402
import params731 as P  # noqa: E402

C = float(os.environ.get('C', '800'))
FLOOR = float(os.environ.get('FLOOR', '40'))
JTOP = float(os.environ.get('JTOP', '1e6'))
JFROM = float(os.environ.get('JFROM', '0'))      # ladder runs: only the cells with j_b > JFROM J
J = P.J
CJ = C * J
f = P.F_MIN
assert P.f_eff(JTOP * J / 2 ** FLOOR, 1.0) == f
cells = []
ja = 1.0
while ja < JTOP * J:
    jb = min(JTOP * J, ja * 1.15)
    if ja < J < jb:
        jb = J
    cells.append((ja, jb))
    ja = jb


def run(ja, jb):
    ln0 = max(FLOOR * math.log(2), ja / CJ)
    x = A.ln_n0_lo(ja, CJ, FLOOR)
    allowed = 1.0 if jb <= J else ja / J
    allowed_fr = Fr(1) if jb <= J else Fr(ja) / P.J_FR
    t = time.time()
    wf, wc, s = A.worst_merged_iv(jb, f, ln0, x)
    ok = wc < math.inf and Fr(wc) < allowed_fr
    print("j in [%.4g, %.4g] J (n >= e^%.6g): worst float %.10g cert %.10g at s2 <= %d  allowed %.4g  margin float %.6g"
          " cert %.6g  %s [%.0fs] %s" % (ja / J, jb / J, ln0, wf, wc, s, allowed, allowed - wf, allowed - wc,
                                        "CERT-OK" if ok else "CERT-FAIL", time.time() - t, dict(STATS)), flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "near":
        for v in sys.argv[2:]:
            jj = float(v) * J
            for (a, b) in cells:
                if a < jj <= b:
                    run(a, b)
                    break
        sys.exit(0)
    part, nparts = int(sys.argv[1]), int(sys.argv[2])
    print(f"coverA731_iv: J = {J:.0f}, C = {C:g}, floor 2^{FLOOR:g}, j in [1, {JTOP:g} J], {len(cells)} cells, part {part}/{nparts}", flush=True)
    sel = [c for c in cells if c[1] > JFROM * J * (1 + 1e-12)]
    for idx, (a, b) in enumerate(sel):
        if idx % nparts == part:
            run(a, b)
