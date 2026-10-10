"""Ideal merge-tree first sort: per big node, per column, the input is runs (parent runs of length b_p, children runs of f_c).
Cost of merging two sorted runs x,y = ceil(lg(x+y)) (odd-even merge); tree critical path via greedy smallest-first (Huffman-like).
Compare with T(L) (full first sort) and with the aligned-chunk scheme T(L)-T(29)."""
import heapq, math, sys, importlib.util
spec=importlib.util.spec_from_file_location('rc','run_check2.py'); rc=importlib.util.module_from_spec(spec); spec.loader.exec_module(rc)
F=rc.load('flow_table2.txt')
def geo(d,t,l):
    a,u,dn=F[(d,t,l)]
    if a<=rc.SMALL or dn==0: return None
    return rc.geometry(a,u,dn)
def clg(x): return (x-1).bit_length()
def merge_cost(runs):
    # runs: dict length->count ; greedy smallest-two merging; returns critical-path depth
    h=[(L,0) for L,c in runs.items() for _ in range(min(c,10**6))] if sum(runs.values())<5000 else None
    if h is None: # compress huge counts: merge equal runs pairwise levels analytically
        h=[]
        for L,c in runs.items():
            cnt=c; cur=(L,0)
            # combine c equal runs by balanced tree
            while cnt>1:
                half=cnt//2
                cur=(2*cur[0],cur[1]+clg(2*cur[0]))
                rem=cnt-2*half
                cnt=half
                if rem: h.append((cur[0]//2, cur[1]-clg(cur[0])))  # leftover unmerged run (approx)
            h.append(cur)
    heapq.heapify(h)
    while len(h)>1:
        a=heapq.heappop(h); b=heapq.heappop(h)
        s=a[0]+b[0]; heapq.heappush(h,(s,max(a[1],b[1])+clg(s)))
    return h[0][1]
d=int(sys.argv[1])
tf=max(t for (dd,t,l) in F if dd==d)
print("d",d)
tot_full=tot_new=0
for t in range(2,tf+1):
    best=0; bestfull=0
    for l in range(0,d+1):
        if (d,t,l) not in F: continue
        g=geo(d,t,l)
        if not g: continue
        m,n,f,b=g
        runs={}
        # parent
        if l>=1 and (d,t-1,l-1) in F:
            a2,u2,d2=F[(d,t-1,l-1)]
            if d2>0:
                gp=geo(d,t-1,l-1)
                if gp: mp,np_,fp,bp=gp; runs[bp]=runs.get(bp,0)+np_//n if np_>=n else 0
                else: runs[d2]=runs.get(d2,0)+ max(1,1)  # small parent: single run (rare)
        for (dd,tt,ll) in [(d,t-1,l+1)]:
            if (dd,tt,ll) in F:
                a2,u2,d2=F[(dd,tt,ll)]
                if u2>0:
                    gc=geo(dd,tt,ll)
                    if gc:
                        mc,nc,fc,bc=gc
                        runs[fc]=runs.get(fc,0)+ (2*nc*64)//n
                    else:
                        runs[u2//2]=runs.get(u2//2,0)+ (2*64)//1  # small child: 2 runs each
        if sum(runs.values())==0: continue
        c=merge_cost(runs)
        L=clg(m); full=L*(L+1)//2
        if c>best: best=c; bestfull=full
        # no: per stage depth = max over nodes: use first-sort cost c + T(L)
    if best: 
        L=59; tot_full+=2*(L*(L+1)//2) ; tot_new+=best+L*(L+1)//2
        print(f" t={t} first-sort merge-tree depth {best} (vs {L*(L+1)//2})")
print("ratio",tot_new/tot_full)
