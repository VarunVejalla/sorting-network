"""Interval-certified regime (B) cover (rd_scaled_iv.escapes_cell_iv), same cell logic as coverB.py:
C = 100 (S.CJ = 100 * 5e5), floor n >= 2^30 (pass NMIN_LOG2=24 env for the coverB24 floor), b-cells of
ratio 1.3, bottom cell [s0 * 1e-9, s0] with s0 = 1e-14 b_lo, sigma-cells of ratio 2 bisected geometrically
(depth <= 14), closure by the monotone average count(s_hi)/s_hi < f.  The float evaluation decides where
to split; every leaf, the bottom cell and the closing test are certified in interval arithmetic.

Usage:  python -I coverB_iv.py part nparts [b_from b_to]     (b-cells exactly as coverB.py / coverB24.py)
        python -I coverB_iv.py cell b_lo b_hi                 (one b-cell)
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import rd_scaled_iv as V  # noqa: E402
from fractions import Fraction as Fr  # noqa: E402

NMIN_LOG2 = float(os.environ.get('NMIN_LOG2', '30'))
V.configure(CJ=100 * 5e5, nmin=2.0 ** NMIN_LOG2)
J = 5e5


def run_cell(bl, bh):
    f = max(3967.0, 8 * bl)
    allowed = bl / J
    allowed_iv = V.I(Fr(bl) / Fr(500000))
    t = time.time()
    s0 = bl * 1e-14
    r0 = V.escapes_cell_iv(bl, bh, s0 * 1e-9, s0, f)
    cnt0, cnt0c = r0["total"], r0["total_c"]
    ok = cnt0c is not None and V.lt(cnt0c, allowed_iv)
    wf = cnt0 - allowed
    wc = (V.upf(cnt0c) - allowed) if cnt0c is not None else math.inf
    leaves = [0, 0]                               # certified, failed

    def check(sl, sh, depth):
        """returns (worst float e - allowed, worst certified e - allowed, closed) on [sl, sh]."""
        r = V.escapes_cell_iv(bl, bh, sl, sh, f, do_cert=False)
        if r["e"] >= allowed and depth < 14:
            return split(sl, sh, depth)
        r["certify"]()
        if r["e_c"] is not None and V.lt(r["e_c"], allowed_iv):
            leaves[0] += 1
            return r["e"] - allowed, V.upf(r["e_c"]) - allowed, V.lt(r["total_c"], V.I(sh) * f)
        if depth < 14:
            return split(sl, sh, depth)
        leaves[1] += 1
        ec = V.upf(r["e_c"]) - allowed if r["e_c"] is not None else math.inf
        return r["e"] - allowed, ec, False

    def split(sl, sh, depth):
        sm = math.sqrt(sl * sh)
        a = check(sl, sm, depth + 1)
        b = check(sm, sh, depth + 1)
        return max(a[0], b[0]), max(a[1], b[1]), b[2]

    sl = s0
    closed = False
    sh = sl
    while sl < bl / f:
        sh = min(2 * sl, bl / f)
        w_f, w_c, cl = check(sl, sh, 0)
        if w_c >= 0:
            ok = False
        wf, wc = max(wf, w_f), max(wc, w_c)
        if cl:
            closed = True
            break
        sl = sh
    good = ok and (closed or sl >= bl / f) and leaves[1] == 0
    print("b in [%.4g, %.4g] f=%.4g: bottom count float %.6e cert %.6e (allowed %.3e); worst esc - allowed: float %.6e"
          " cert %.6e (rel. to allowance %.4f / %.4f); closed at sigma %.3e: %s; leaves cert %d failed %d  %s [%.0fs] %s" % (
              bl, bh, f, cnt0, V.upf(cnt0c) if cnt0c is not None else math.inf, allowed, wf, wc, wf / allowed, wc / allowed,
              sh if closed else float('nan'), closed, leaves[0], leaves[1], "CERT-OK" if good else "CERT-FAIL",
              time.time() - t, dict(V.STATS)), flush=True)
    return good


if __name__ == "__main__":
    if sys.argv[1] == "cell":
        run_cell(float(sys.argv[2]), float(sys.argv[3]))
        sys.exit(0)
    part, nparts = int(sys.argv[1]), int(sys.argv[2])
    b_from = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-6
    b_to = float(sys.argv[4]) if len(sys.argv) > 4 else 1.25e6
    edges = []
    b = b_from
    while b < b_to:
        edges.append((b, min(b_to, b * 1.3)))
        b *= 1.3
    for idx, (bl, bh) in enumerate(edges):
        if idx % nparts == part:
            run_cell(bl, bh)
