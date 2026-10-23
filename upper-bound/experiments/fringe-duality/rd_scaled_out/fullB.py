import sys, math, time
sys.path.insert(0, '..')
import rd_scaled as S
S.CJ = 100 * 5e5
J = 5e5
orig = S.n0_of_b
S.n0_of_b = lambda b, nmin_=2.0 ** 30: orig(b, nmin_)
for b in (1e-6, 1e-4, 1e-2, 1, 10, 100, 496, 1e3, 1e4, 1e5, 1.25e6):
    f = max(3967.0, 8 * b)
    r = 1e-12
    while r <= 1.0 / f * 1.0001:
        sig = b * min(r, 1 / f)
        e = S.escapes_s(b, sig, f)
        L = (e + f * sig) / sig
        print("b=%g f=%g sigma=%.2e: esc/n %.3e allowed %.3e L/sigma %.4g %s" % (b, f, sig, e, b / J, L, "OK" if e < b / J else ("moot(L/s<f earlier)" if False else "FAIL")), flush=True)
        if L < f:
            print("   monotone average below f at sigma=%.2e: larger sigma covered" % sig, flush=True)
            break
        r *= 10
