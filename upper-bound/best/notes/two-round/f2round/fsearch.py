"""Float search for the smallest f the R1/R2 scheme supports (then certify with cert.py)."""
import math, sys
LN=math.log; J=86e6; e=math.e
def params(f,g1,g2,lam=1.0):
    D=128/4095*f; Dl=g2-g1; Phi=f-g2
    if Dl+1<D: return None
    ts=J/(g1+1)*LN(e*e*(g1+1)**2/D)
    def slope_a(c): return ts+c*(LN(e*J/(c*D))+(Dl+1)*LN(e*D/(Dl+1)))
    lo,hi=1e-6,0.5
    if slope_a(hi)>-lam: return None
    for _ in range(100):
        m=(lo+hi)/2
        if slope_a(m)<=-lam: hi=m
        else: lo=m
    c=hi*1.0001
    def psistar(b):
        dp=lambda s: LN(J/(s*D))+Dl*LN(e*D*s/(Dl*s+b))+b/s
        a,z=1e-30,1e30
        for _ in range(300):
            m=math.sqrt(a*z)
            if dp(m)>0: a=m
            else: z=m
        s=a; return s*LN(e*J/(s*D))+(Dl*s+b)*LN(e*D*s/(Dl*s+b))
    lo,hi=J/(g1+1),1e9
    if ts+psistar(hi)>-lam: return None
    for _ in range(100):
        m=(lo+hi)/2
        if ts+psistar(m)<=-lam: hi=m
        else: lo=m
    b=hi*1.0001
    LY=LN(e*e*J*b/(D*c*c)); q0=LN(J*Phi/(D*e*b))
    return c,b,q0-c*LY
best={}
for f in [int(x) for x in sys.argv[1:]]:
    res=[]
    for a1 in [x/100 for x in range(10,70,2)]:
        for a2 in [x/100 for x in range(int(a1*100)+4,99,2)]:
            p=params(f,int(a1*f),int(a2*f))
            if p and p[2]>0: res.append((p[2],a1,a2,p[0],p[1]))
    res.sort(reverse=True)
    print(f, res[:3] if res else "none")
