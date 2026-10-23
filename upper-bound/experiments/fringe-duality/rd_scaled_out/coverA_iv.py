"""Interval-certified regime (A) cover (rd_sparse_iv.worst_merged_iv), same cells as coverA.py: j-intervals
of ratio 1.15 over [1, 1e6 J] (split at J), evaluated at j_b against the allowance j_a/J (1 for j_b <= J),
every n >= max(2^40, e^{j_a/(100 J)}) (certified lower bound of the exponent), every set size.

Usage:  python -I coverA_iv.py part nparts             (all cells, round-robin as coverA.py)
        python -I coverA_iv.py near j1/J [j2/J ...]     (only the cell containing each j)
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import rd_sparse_iv as A  # noqa: E402
from rd_scaled_iv import STATS  # noqa: E402

f, J = 3967.0, 5e5
CJ = 100 * J
cells = []
ja = 1.0
while ja < 1e6 * J:
    jb = min(1e6 * J, ja * 1.15)
    if ja < J < jb:
        jb = J
    cells.append((ja, jb))
    ja = jb


def run(ja, jb):
    ln0 = max(40 * math.log(2), ja / CJ)
    x = A.ln_n0_lo(ja, CJ, 40)
    allowed = 1.0 if jb <= J else ja / J
    t = time.time()
    wf, wc, s = A.worst_merged_iv(jb, f, ln0, x)
    print("j in [%.4g, %.4g] J (n >= e^%.6g): worst float %.10g cert %.10g at s2 <= %d  allowed %.4g  margin float %.6g"
          " cert %.6g  %s [%.0fs] %s" % (ja / J, jb / J, ln0, wf, wc, s, allowed, allowed - wf, allowed - wc,
                                        "CERT-OK" if wc < math.inf and Fr(wc) < (1 if jb <= J else Fr(ja) / Fr(500000)) else "CERT-FAIL", time.time() - t, dict(STATS)),
          flush=True)


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
    for idx, (a, b) in enumerate(cells):
        if idx % nparts == part:
            run(a, b)
