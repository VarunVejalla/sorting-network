import sys, math, time
sys.path.insert(0, '.')
import rd_scaled as S
J = 1651190.0
C = float(sys.argv[1]); nmin = 2.0**float(sys.argv[2])
S.CJ = C*J
orig = S.n0_of_b
S.n0_of_b = lambda b, nm=nmin: orig(b, nm)
for b in [float(x) for x in sys.argv[3].split(',')]:
    f = 3329.0 if 8*b <= 3329 else (8*b if 8*b <= 4023 else max(210012., 8*b))
    worst=-1e9
    for i in range(0, 41):
        tau = 10**(-13+ i*0.15)
        s = tau*b
        if s > b/f: break
        tot, e = S.escapes_cell(b, b, s, s, f)
        worst=max(worst, e/(b/J))
        print(f"C={C} b={b} tau={tau:.2e} count/b={tot/b:.3e} rel={e/(b/J):.3f}", flush=True)
        if e < -10*b/J: break
    print("WORST", b, worst)
