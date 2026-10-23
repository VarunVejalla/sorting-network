import sys, math, time
sys.path.insert(0, '..')
import rd_scaled as S
S.CJ = 100 * 5e5
J = 5e5
orig = S.n0_of_b
S.n0_of_b = lambda b, nmin_=2.0 ** 30: orig(b, nmin_)
for b in [float(x) for x in sys.argv[1:]] or (1e3, 1e4, 1e5, 1.25e6):
    f = 8 * b
    for r in (1e-12, 1e-9, 1e-6, 1e-4):
        sig = min(b * r, b / f)
        t = time.time()
        e = S.escapes_s(b, sig, f)
        print("B f=8b b=%g sigma=%.2e: esc/n %.3e allowed %.3e  L/sigma=%.4g vs f=%.4g  %s [%.0fs]" % (
            b, sig, e, b / J, (e + f * sig) / sig, f, "OK" if e < b / J else "FAIL", time.time() - t), flush=True)
