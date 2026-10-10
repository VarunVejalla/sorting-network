from tworound import *
def scan(budget, theta=0.5):
    for f in [int(1e4*1.02**i) for i in range(0,250)]:
        for gf in [0.3,0.4,0.5,0.6,0.7,0.8,0.9]:
            if ok_small(f,int(gf*f),theta,budget): return f,gf
for b in (0.49,0.3):
    print("small-rank sum-version f_min budget",b,scan(b))
f=131072
for gf in (0.5,0.6,0.7):
    print(f, gf, "ok_small:", ok_small(f,int(gf*f),0.5,0.49), max((S_small(f,int(gf*f),0.5,n),n) for n in NS))
# margin threshold f for large ranks
for f in [2**14,2**15,3*2**14,2**16]:
    print(f,[round(margin(f,int(gf*f))[0],2) for gf in (0.2,0.3,0.5)])
