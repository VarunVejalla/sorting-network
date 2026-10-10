"""Two-round analysis for f ~ 2^17.  (A) small ranks j<=J via first-round (g, eta); (B) heuristic first-moment margin for large ranks."""
import math
from fmin import lnx, coef
LN=math.log
eps=1/86e6; J=86e6; delta=128/4095

# ---------- (A) small ranks: first-round property "E_g(z) < eta*j" for all j<=min(J, delta f n),
# eta=(f-g)/J (so g+eta*j<=f).  One-round machinery with f_role=g, eps_role=eta, discard theta*g.
def S_small(f, g, theta, n, C=1.025, E0=4000):
    eta=(f-g)/J
    jmax=min(J, delta*f*n)
    K=math.ceil(eta*jmax)
    tot=0.0
    top=min(K,E0)
    for E in range(1,top+1):
        jp=min(E/eta, jmax)
        u=jp/(g*n); ee=E/jp
        if coef(g,ee,theta)<=0: return float('inf')
        t=E*lnx(g,ee,u,theta)
        if t>600: return float('inf')
        if t>-700: tot+=C*math.exp(t)
    if K>top:
        jp=jmax; u=jp/(g*n); ee=K/jp
        xs=math.exp(lnx(g,ee,u,theta))
        if xs>=1: return float('inf')
        tot+=C*xs**top*xs/(1-xs)
    return tot
NS=[16,32,100,1000,10**4,2*10**4,5*10**4,10**5,10**6,10**8]
def ok_small(f,g,theta,budget):
    return max(S_small(f,g,theta,n) for n in NS)<=budget
def fmin_small(budget=0.49,theta=0.5):
    res=None
    for f in [int(1e5*1.03**i) for i in range(0,60)]:
        best=None
        for gf in [0.3,0.4,0.5,0.6,0.7,0.8]:
            g=int(gf*f)
            if ok_small(f,g,theta,budget): best=gf;break
        if best: return f,best
    return None
# sup-style (x<=0.3223 at u=delta f/g) for comparison
def fmin_small_sup(xmax=0.3223,theta=0.5):
    for f in [int(1e5*1.01**i) for i in range(0,300)]:
        for gf in [0.3,0.4,0.5,0.6,0.7,0.8]:
            g=f*gf; eta=(f-g)/J; u=delta*f/g
            if coef(g,eta,theta)>0 and math.exp(lnx(g,eta,u,theta))<=xmax: return f,gf
    return None

# ---------- (B) heuristic first moment, large ranks.
def gain(A, mu0):
    # sum_{i=1}^A max(0, i ln(i/(e mu0)))  (log-prob of A demanded intermediate columns, product bound)
    lo=max(1,int(math.e*mu0))
    # closed form via integral approx with Euler-Maclaurin-free numeric sum in blocks
    s=0.0
    import numpy as np
    i=np.arange(lo,A+1,dtype=float)
    return float(np.sum(i*np.log(i/(math.e*mu0))))
def entropy_per_col(f,g,e,vs):
    # vs = s/n ; j0 = s e/eps ; k=j0/(g+1) top columns among n; per bad column:
    # tops count (e n/k)^k (e tau/k)^k  + C(n,s)
    k_over_s=e/(eps*(g+1))
    n_over_k=1/(vs*k_over_s)
    tau_over_k=g+1  # tau<=j0=k(g+1)
    ent=k_over_s*(1+LN(max(n_over_k,1))+1+LN(tau_over_k)) if n_over_k>=1 else k_over_s*(2+LN(tau_over_k))
    ent+=1+LN(1/vs)
    return ent
def margin(f,g):
    worst=(1e300,None)
    for e in [1,10,100,1e3,1e4,3e4,1e5,3e5,1e6]:
        A=int(f+e-g)
        for vs in [1e-3,1e-5,1e-7,1e-9,1e-12,1e-15,1e-20]:
            j0perS=e/eps          # mass per bad column
            mu0=min(j0perS*vs, delta*f)   # mean top hits per column, capped by support
            if j0perS*vs>delta*f: continue  # not supported
            gn=gain(A,mu0)
            en=entropy_per_col(f,g,e,vs)
            r=gn/en
            if r<worst[0]: worst=(r,(e,vs,gn,en))
    return worst
if __name__=="__main__":
    print("small-rank f_min (sum, budget .49, theta=.5):",fmin_small())
    print("small-rank f_min (sup x<=.3223):",fmin_small_sup())
    for f in [2**15,2**16,3*2**15,2**17,2**18]:
        for gf in [0.3,0.5,0.7]:
            r=margin(f,int(gf*f))
            print(f,gf,"margin gain/entropy=%.3g"%r[0],r[1])
