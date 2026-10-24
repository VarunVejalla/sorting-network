import sys, math, time
sys.path.insert(0, r'C:/Users/Varun/Documents/Projects/Math Research/sorting-network/.claude/worktrees/ub-43/upper-bound/experiments/fringe-duality')
import rd_scaled as S
J = 1651190.0
C = float(sys.argv[1]); nmin = 2.0**float(sys.argv[2])
S.CJ = C*J
orig = S.n0_of_b
S.n0_of_b = lambda b, nm=nmin: orig(b, nm)
for b in [float(x) for x in sys.argv[3].split(',')]:
    f = 3329.0 if 8*b <= 3329 else (8*b if 8*b <= 4023 else max(210012., 8*b))
    worst=(-1e9,0)
    for i in range(0, 60):
        tau = 10**(-13+ i*0.1)
        s = tau*b
        if s > b/f: break
        e = min(S.escapes_cell(b, b, s, s, f, ratio=r)[1] for r in (1.6,3,4))
        worst=max(worst, (e/(b/J), tau))
        if e < -3*b/J and tau > 1e-9: break
    print(f"floor 2^{sys.argv[2]} C={C} b={b} f={f}: worst rel {worst[0]:.3f} at tau {worst[1]:.2e}", flush=True)
