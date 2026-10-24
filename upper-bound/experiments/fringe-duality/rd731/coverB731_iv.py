"""Interval-certified regime (B) cover at the 731.25 point (rd_scaled_iv.escapes_cell_iv, unchanged evaluator).

Same cell logic as rd_scaled_out/coverB_iv.py, parametrized:
  * J = 1651190 (params731), regime boundary C (env C, default 800): (B) is every n >= max(2^NMIN_LOG2, n0(b)),
    n0(b) = (CJ/b) ln(CJ/b), which contains every (n, j) with n >= 2^NMIN_LOG2 and j >= C J ln n;
  * floor 2^NMIN_LOG2 (env, default 30);
  * fringe class: f = params731.f_eff(b_lo n, n) (class-aware; escapes decrease in f);
  * b-cells of ratio BRATIO (env, default 1.1); bottom sigma-cell [s0 1e-9, s0], s0 = 1e-14 b_lo; sigma-cells of
    ratio 2 bisected geometrically to depth DEPTH (env, default 18); closure by the monotone average
    count(s_hi)/s_hi < f; the sigma range ends at b/f (at most j/f columns can be overloaded);
  * level ratio: each leaf tries RATIOS (env, default 1.6,3,4) in floats and certifies the best (any level
    partition is valid).
Every leaf, the bottom cell and the closing test are certified in interval arithmetic.

Usage:  python -I coverB731_iv.py part nparts [b_from b_to]
        python -I coverB731_iv.py cell b_lo b_hi
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import rd_scaled_iv as V  # noqa: E402
import params731 as P  # noqa: E402

C = float(os.environ.get('C', '800'))
NMIN_LOG2 = float(os.environ.get('NMIN_LOG2', '30'))
BRATIO = float(os.environ.get('BRATIO', '1.1'))
DEPTH = int(os.environ.get('DEPTH', '18'))
RATIOS = tuple(float(x) for x in os.environ.get('RATIOS', '1.6,3,4').split(','))
V.configure(CJ=C * P.J, nmin=2.0 ** NMIN_LOG2)
J = P.J


def run_cell(bl, bh):
    f = P.f_eff(bl, 1.0)               # j_lo / n = b_lo
    if f is None:
        print("b in [%.6g, %.6g]: above every class (b > f_max/8): nothing to cover" % (bl, bh), flush=True)
        return True
    allowed = bl / J
    allowed_iv = V.I(Fr(bl) / P.J_FR)
    t = time.time()
    s0 = bl * 1e-14
    r0 = V.escapes_cell_iv(bl, bh, s0 * 1e-9, s0, f)
    cnt0, cnt0c = r0["total"], r0["total_c"]
    ok = cnt0c is not None and V.lt(cnt0c, allowed_iv)
    wf = cnt0 - allowed
    wc = (V.upf(cnt0c) - allowed) if cnt0c is not None else math.inf
    leaves = [0, 0]
    worst_leaf = [None]

    def check(sl, sh, depth):
        rs = [(V.escapes_cell_iv(bl, bh, sl, sh, f, ratio=ra, do_cert=False), ra) for ra in RATIOS]
        r, ra = min(rs, key=lambda x: x[0]["e"])
        if r["e"] >= allowed and depth < DEPTH:
            return split(sl, sh, depth)
        r["certify"]()
        if r["e_c"] is not None and V.lt(r["e_c"], allowed_iv):
            leaves[0] += 1
            ec = V.upf(r["e_c"]) - allowed
            if worst_leaf[0] is None or ec > worst_leaf[0][0]:
                worst_leaf[0] = (ec, sl, sh, ra)
            return r["e"] - allowed, ec, V.lt(r["total_c"], V.I(sh) * f)
        if depth < DEPTH:
            return split(sl, sh, depth)
        leaves[1] += 1
        ec = V.upf(r["e_c"]) - allowed if r["e_c"] is not None else math.inf
        print("   FAIL leaf sigma in [%.6e, %.6e] ratio %g: float e - allowed %.6e cert %.6e" % (sl, sh, ra, r["e"] - allowed, ec), flush=True)
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
    wl = worst_leaf[0]
    print("b in [%.6g, %.6g] f=%.6g: bottom count cert %.6e (allowed %.4e); worst esc - allowed: float %.6e cert %.6e"
          " (rel. %.4f / %.4f; worst leaf sigma/b in [%.3e, %.3e] ratio %s); closed at sigma %.3e: %s; leaves cert %d"
          " failed %d  %s [%.0fs] %s" % (
              bl, bh, f, V.upf(cnt0c) if cnt0c is not None else math.inf, allowed, wf, wc, wf / allowed, wc / allowed,
              wl[1] / bl if wl else float('nan'), wl[2] / bl if wl else float('nan'), wl[3] if wl else '-',
              sh if closed else float('nan'), closed, leaves[0], leaves[1], "CERT-OK" if good else "CERT-FAIL",
              time.time() - t, dict(V.STATS)), flush=True)
    return good


def edges(b_from, b_to):
    out = []
    b = b_from
    while b < b_to:
        out.append((b, min(b_to, b * BRATIO)))
        b *= BRATIO
    return out


if __name__ == "__main__":
    if sys.argv[1] == "cell":
        run_cell(float(sys.argv[2]), float(sys.argv[3]))
        sys.exit(0)
    part, nparts = int(sys.argv[1]), int(sys.argv[2])
    b_from = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-6
    b_to = float(sys.argv[4]) if len(sys.argv) > 4 else P.F_MAX / 8
    print(f"coverB731_iv: J = {J:.0f}, C = {C:g}, floor 2^{NMIN_LOG2:g}, b-cells ratio {BRATIO} over [{b_from:g}, {b_to:g}],"
          f" part {part}/{nparts}, depth {DEPTH}, level ratios {RATIOS}", flush=True)
    for idx, (bl, bh) in enumerate(edges(b_from, b_to)):
        if idx % nparts == part:
            run_cell(bl, bh)
