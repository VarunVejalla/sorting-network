"""Brute-force sanity test of the deterministic reductions (heights from the F2 end, rows 1..m)."""
import random
def rnd(m,n,R):
    h=sorted([R.randint(0,m) for _ in range(n)],reverse=R.random()<.5)
    R.shuffle(h); return h
def round_(h,sig,m,n):   # sig[r] : column perm of row r (cell (r,c) -> (r,sig[r][c])); returns sorted heights
    z=[0]*n
    for r in range(1,m+1):
        for c in range(n):
            if h[c]>=r: z[sig[r][c]]+=1
    return z
def hits_above(h,sig,m,n,g):  # H_c: rows r>g with marked preimage
    H=[0]*n
    for r in range(g+1,m+1):
        for c in range(n):
            if h[c]>=r: H[sig[r][c]]+=1
    return H
R=random.Random(1); bad=0
for it in range(20000):
    m=R.randint(2,9); n=R.randint(1,7); f=R.randint(1,m); g1=R.randint(0,f); g2=R.randint(g1,f)
    h=rnd(m,n,R)
    s1={r:R.sample(range(n),n) for r in range(1,m+1)}; s2={r:R.sample(range(n),n) for r in range(1,m+1)}
    z=round_(h,s1,m,n); w=round_(z,s2,m,n)
    H=hits_above(h,s1,m,n,g1); D=g2-g1
    assert all(z[c]<=g1+H[c] for c in range(n))
    y=[max(0,H[c]-D) for c in range(n)]
    Dv=hits_above(y,{r:s2[r+g2] for r in range(1,m-g2+1)},m-g2,n,0) if m>g2 else [0]*n
    assert all(w[v]<=g2+Dv[v] for v in range(n)),(w,g2,Dv)
    # E_final <= sum over S={w>f} of D_v-(f-g2)
    S=[v for v in range(n) if w[v]>f]
    Ef=sum(w[v]-f for v in S)
    assert Ef<=sum(Dv[v] for v in S)-(f-g2)*len(S)
    # SR: H_c <= f-g1 for all c  => no escapes
    if max(H)<=f-g1: assert Ef==0
print("ok")
