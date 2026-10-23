import sys, time, math
sys.path.insert(0, '..')
import rd_scaled as S
f, J = 3967.0, 5e5
b = float(sys.argv[1])
smax = b / f
sig = 1e-12
while sig <= smax * 1.0001:
    t = time.time()
    e = S.escapes_s(b, min(sig, smax), f)
    print("b=%g sigma=%.3e: escapes/n %.4e  allowed %.4e  %s  [%.0fs]" % (b, min(sig, smax), e, b / J, "OK" if e < b / J else "FAIL", time.time() - t), flush=True)
    sig *= 10
