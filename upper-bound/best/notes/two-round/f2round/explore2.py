from explore import *
import sys
def scan(f, a1, a2, tgt0=20):
    g1, g2 = int(a1*f), int(a2*f)
    worst=(-1e300,None)
    for t in [1.0001,1.01,1.1,1.5,2,3,5,10,30,100,1e3,1e4,1e5,1e6,1e8,1e10,1e12]:
        n=int(J/(DELTA*f)*t)+1
        Emax=math.ceil(DELTA*f*n/J)
        Es=sorted(set([2,3,4,6,10,20,50,100,200,500,1000,2000,5000,1e4,2e4,5e4,1e5,2e5,5e5,1e6,1e7,1e8,1e9,1e10,1e11,Emax,Emax-1]))
        for E in Es:
            E=int(E)
            if E>Emax or E<2: continue
            jE=min(E*J, math.floor(DELTA*f*n))
            target=-(tgt0+2*LN(E))
            lo,hi=0,10**13
            while lo<hi:
                mid=(lo+hi)//2
                if r1a(f,g1,g2,n,jE,mid)<=target: hi=mid
                else: lo=mid+1
            kap=lo
            if kap==0: continue
            lo,hi=2,10**16
            while lo<hi:
                mid=(lo+hi)//2
                if r1b(f,g1,g2,n,jE,kap,mid)<=target: hi=mid
                else: lo=mid+1
            B=lo
            v2=r2(f,g2,n,E,kap,B)+2*LN(E)
            if v2>worst[0]: worst=(v2,(n,E,kap,B,kap/E,B/E))
    return worst
f=int(sys.argv[1])
for a1,a2 in [(0.3,0.6),(0.35,0.7),(0.4,0.8),(0.45,0.9),(0.3,0.75),(0.4,0.9),(0.5,0.9)]:
    print(f,a1,a2,scan(f,a1,a2))
