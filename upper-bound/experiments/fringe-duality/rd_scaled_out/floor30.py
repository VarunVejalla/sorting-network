import sys, math, time
sys.path.insert(0, '..')
import rd_scaled as S
import rd_sparse as A
S.CJ = 100 * 5e5
f, J = 3967.0, 5e5
nmin = 2.0 ** 30
orig = S.n0_of_b
S.n0_of_b = lambda b, nmin_=nmin: orig(b, nmin_)
mode = sys.argv[1]
if mode == "B":
    for b in (1.0, 10.0, 100.0, 496.0):
        for r in (1e-12, 1e-9, 1e-6, 1e-3):
            sig = min(b * r, b / f)
            e = S.escapes_s(b, sig, f)
            print("B nmin=2^30 b=%g sigma=%.2e: esc/n %.3e allowed %.3e %s" % (b, sig, e, b / J, "OK" if e < b / J else "FAIL"), flush=True)
else:
    for jj in (1, 100, 1000, 2080):
        j = jj * J
        ln0 = max(30 * math.log(2), j / 1.15 / (100 * J))
        t = time.time(); e, s = A.worst_merged(j, f, ln0)
        al = 1.0 if jj <= 1 else jj / 1.15
        print("A n0=2^30 j=%gJ: worst %.4g at s2<=%d allowed %.3g %s [%.0fs]" % (jj, e, s, al, "OK" if e < al else "FAIL", time.time() - t), flush=True)
