"""Exhaustive small-instance joint two-round gate (not an all-n certificate).

At fixed mass enumerate every input height profile and its exact reachable
middle. Compare exact worst leakage against arbitrary middles having the same
mass and the maximum reachable L1 spread, then add every subset support cut.
All objective numerators and support tests use integers. Random permutations
are fixed before the exhaustive adversary; results do not prove existence of
8192-row scrambles with a uniform bound.
"""
import argparse
import itertools
import json
from pathlib import Path
import numpy as np
from d2_bulk_attack import Stage


def profiles(n, m, mass):
    def visit(prefix, left, count):
        if count == 1:
            if 0 <= left <= m:
                yield prefix+[left]
            return
        for h in range(max(0,left-(count-1)*m),min(m,left)+1):
            yield from visit(prefix+[h],left-h,count-1)
    return np.array(list(visit([],mass,n)),dtype=np.int64)


def advance_many(p, perm):
    m,n=perm.shape
    table=np.zeros((n,m+1,n),dtype=np.int64)
    for u in range(n):
        for r in range(m):
            table[u,r+1]=table[u,r]
            table[u,r+1,perm[r,u]]+=1
    result=np.zeros_like(p)
    for u in range(n):
        result+=table[u,p[:,u],:]
    return result


def support_dp(perm, weights, mass):
    """Exact support function of reachable middles, without enumerating inputs.

    A column choosing height h contributes its first h destination weights.
    Knapsack DP enforces the shared total mass exactly.
    """
    m,n=perm.shape
    unreachable=-10**15
    dp=np.full(mass+1,unreachable,dtype=np.int64)
    dp[0]=0
    for u in range(n):
        prefix=np.concatenate(([0],np.cumsum(weights[perm[:,u]])))
        nxt=np.full_like(dp,unreachable)
        for h in range(min(m,mass)+1):
            nxt[h:]=np.maximum(nxt[h:],dp[:mass+1-h]+prefix[h])
        dp=nxt
    return int(dp[mass])


def run(n,m,seed,tiered=False):
    mass=n*m//2
    p=profiles(n,m,mass)
    stage=Stage(n,m,seed)
    mid=advance_many(p,stage.s1)
    reachable=np.unique(mid,axis=0)
    # Use integer-scaled deviation to allow masses not divisible by n.
    spread=np.abs(n*reachable-mass).sum(axis=1).max()
    scalar=np.abs(n*p-mass).sum(axis=1)<=spread
    cuts=np.array(list(itertools.product([0,1],repeat=n)),dtype=np.int64)
    caps=(reachable@cuts.T).max(axis=0)
    for cut,cap in zip(cuts,caps):
        assert support_dp(stage.s1,cut,mass)==cap
    subset=scalar.copy()
    for cut,cap in zip(cuts,caps):
        subset &= p@cut<=cap
    def objective(q):
        final=advance_many(q,stage.s2)
        score=np.maximum(n*final-mass,0).sum(axis=1)
        i=int(np.argmax(score))
        return dict(numerator=int(score[i]),denominator=n*n,rows=float(score[i]/(n*n)),
                    middle=q[i].tolist(),final=final[i].tolist())
    a,b,c=objective(reachable),objective(p[scalar]),objective(p[subset])
    extra={}
    if tiered:
        mask=subset.copy()
        # Shift invariance at fixed mass: only min=0, max=2 adds new cuts.
        for weights in itertools.product(range(3),repeat=n):
            if min(weights)!=0 or max(weights)!=2:
                continue
            w=np.array(weights,dtype=np.int64)
            cap=int((reachable@w).max())
            assert support_dp(stage.s1,w,mass)==cap
            mask &= p@w<=cap
        d=objective(p[mask])
        assert a['numerator']<=d['numerator']<=c['numerator']
        extra=dict(tiered_profiles=int(mask.sum()),tiered=d)
    assert a['numerator']<=c['numerator']<=b['numerator']
    return dict(columns=n,rows=m,seed=seed,mass=mass,input_profiles=len(p),
                reachable_profiles=len(reachable),scalar_profiles=int(scalar.sum()),
                subset_profiles=int(subset.sum()),max_mean_absolute_spread=float(spread/(n*n)),
                reachable=a,scalar=b,subset=c,
                quantifier='exhaustive inputs at this fixed mass and sampled scramble pair',**extra)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--columns',type=int,default=6)
    ap.add_argument('--rows',type=int,default=8)
    ap.add_argument('--seeds',type=int,nargs='+',default=[0,1,2,3,4])
    ap.add_argument('--output')
    ap.add_argument('--tiered',action='store_true')
    a=ap.parse_args()
    if a.columns>8:
        ap.error('exhaustive gate limited to at most eight columns')
    results=[]
    for seed in a.seeds:
        r=run(a.columns,a.rows,seed,a.tiered)
        results.append(r)
        print(json.dumps(r),flush=True)
    if a.output:
        Path(a.output).write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':
    main()
