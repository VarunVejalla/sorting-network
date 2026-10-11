from closed import *
import sys
mp.mp.dps=30
def r2_slope(f,g2,c,b):
    df=DELTA*f; Phi=f-g2
    return c*mp.log(e**2*J*b/(df*c**2)) - mp.log(J*Phi/(df*e*b))
def ok(f, a1, a2, verbose=False):
    g1,g2=int(a1*f),int(a2*f)
    if g2-g1<=DELTA*f+1: return False
    c,_=choose(f,g1,g2,1)
    _,b=choose(f,g1,g2,12)
    if r2_slope(f,g2,c,b)>=0: return False
    Es=[int(10**(k/4)) for k in range(2,4*30)]
    w=max(r2(f,g2,c,b,E) for E in Es)
    if verbose: print(f,a1,a2,float(c),float(b),float(w),float(r1a(f,g1,g2,c,2)),float(sr(f,g1)),float(r2_slope(f,g2,c,b)))
    return w< -20 and r1a(f,g1,g2,c,2)< -20 and sr(f,g1)< -20
splits=[(a1/100,a2/100) for a1 in range(20,60,5) for a2 in range(a1+10,100,5)]
def fmin():
    lo,hi=20000,131040
    while hi-lo>500:
        mid=(lo+hi)//2
        if any(ok(mid,a1,a2) for a1,a2 in splits): hi=mid
        else: lo=mid
    return hi
F=fmin(); print("fmin approx",F)
for a1,a2 in splits:
    if ok(F,a1,a2): ok(F,a1,a2,True)
