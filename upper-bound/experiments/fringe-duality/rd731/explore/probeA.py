import sys, math, time
sys.path.insert(0, '.')
import rd_sparse as A
J = 1651190.0; C=float(sys.argv[1]); fl=float(sys.argv[2]); f=3329.
for m in [float(x) for x in sys.argv[3].split(',')]:
    j=m*J; t=time.time()
    ln0=max(fl*math.log(2), j/(C*J))
    w,s=A.worst_merged(j,f,ln0)
    print(f"C={C} floor=2^{fl} j={m}J ln_n0={ln0:.1f}: worst {w:.1f} at s2<={s} allowed {max(1,m):.1f} {'OK' if w<max(1,m) else 'FAIL'} [{time.time()-t:.0f}s]",flush=True)
