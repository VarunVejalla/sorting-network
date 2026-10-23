"""Regime (B) cover: every b in [1e-6, 1.25e6] (cells ratio 1.3), every sigma in (0, b/f] (cells ratio 2, bottom
cell [0, sigma0], top closed by the monotone average L(s)/s < f). Floor n >= 2^30, C = 100. Floats."""
import sys, math, time
sys.path.insert(0, '..')
import rd_scaled as S
S.CJ = 100 * 5e5
o = S.n0_of_b
S.n0_of_b = lambda b, nm=2.0 ** 30: o(b, nm)
J = 5e5
part, nparts = int(sys.argv[1]), int(sys.argv[2])
edges = []
b = 1e-6
while b < 1.25e6:
    edges.append((b, min(1.25e6, b * 1.3)))
    b *= 1.3
for idx, (bl, bh) in enumerate(edges):
    if idx % nparts != part:
        continue
    f = max(3967.0, 8 * bl)
    allowed = bl / J
    t = time.time()
    s0 = bl * 1e-14
    cnt0, _ = S.escapes_cell(bl, bh, s0 * 1e-9, s0, f)
    ok = cnt0 <= allowed
    worst = cnt0 - allowed
    def check(sl, sh, depth):
        """returns (worst e - allowed, closed) for [sl, sh], bisecting (geometrically) failing cells."""
        cnt, e = S.escapes_cell(bl, bh, sl, sh, f)
        if e < allowed or depth >= 14:
            return e - allowed, cnt / sh < f
        sm = math.sqrt(sl * sh)
        w1, c1 = check(sl, sm, depth + 1)
        w2, c2 = check(sm, sh, depth + 1)
        return max(w1, w2), c2
    sl = s0
    closed = False
    while sl < bl / f:
        sh = min(2 * sl, bl / f)
        w, cl = check(sl, sh, 0)
        if w >= 0:
            ok = False
        worst = max(worst, w)
        if cl:
            closed = True
            break
        sl = sh
    print("b in [%.4g, %.4g] f=%.4g: bottom cell count %.3e (allowed %.3e); worst esc - allowed %.3e; closed by monotone average at sigma %.3e: %s  %s [%.0fs]" % (
        bl, bh, f, cnt0, allowed, worst, sh if closed else float('nan'), closed, "OK" if ok and (closed or sl >= bl / f) else "FAIL", time.time() - t), flush=True)
