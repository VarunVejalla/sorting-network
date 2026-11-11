"""Objective-guided round-one support cuts; finite numerical MILP screen.

Cuts are independently validated by integer DP. HiGHS optimal/dual bounds are
numerical, not exact rational optimization certificates. Small exhaustive mode
checks the master optimum against every fixed-mass middle after each cut.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.optimize import milp, linprog, Bounds, LinearConstraint
from scipy.sparse import lil_matrix
from d2_bulk_attack import Stage
from d2_joint_reachable_gate import profiles, advance_many


def support(perm,w,mass):
    m,n=perm.shape
    neg=-10**16
    dp=np.full(mass+1,neg,dtype=np.int64); dp[0]=0
    choices=[]
    for u in range(n):
        vals=np.r_[0,np.cumsum(w[perm[:,u]])]
        nxt=np.full_like(dp,neg); ch=np.zeros(mass+1,dtype=np.int32)
        for h in range(min(m,mass)+1):
            v=dp[:mass+1-h]+vals[h]
            take=v>nxt[h:]
            nxt[h:][take]=v[take]; ch[h:][take]=h
        dp=nxt; choices.append(ch)
    left=mass; h=np.zeros(n,dtype=np.int64)
    for u in reversed(range(n)):
        h[u]=choices[u][left]; left-=h[u]
    assert left==0 and h.sum()==mass
    y=advance_many(h[None,:],perm)[0]
    assert w@y==dp[mass]
    return int(dp[mass]),y


def separate(perm,y,mass,limit=100):
    n=len(y)
    h=np.full(n,mass//n,dtype=np.int64)
    h[:mass%n]+=1
    witnesses=[advance_many(h[None,:],perm)[0]]
    for k in range(limit):
        # delta <= p.(y-r) for all generated reachable r.
        A=np.array([np.r_[r-y,1] for r in witnesses],dtype=float)
        result=linprog(np.r_[np.zeros(n),-1],A_ub=A,b_ub=np.zeros(len(A)),
                       bounds=[(-1,1)]*n+[(None,None)],method='highs')
        if not result.success:
            return None,dict(status='separation_lp_failed',iterations=k)
        if result.x[-1]<1e-7:
            return None,dict(status='no_convex_separation_numerical',iterations=k)
        w=np.rint(result.x[:n]*1000000).astype(np.int64)
        w-=w.min()  # fixed-mass translation is immaterial
        g=np.gcd.reduce(w)
        if g: w//=g
        cap,r=support(perm,w,mass)
        gap=int(w@y-cap)
        if gap>0:
            return (w,cap),dict(status='integer_cut',iterations=k+1,gap=gap)
        witnesses.append(r)
    return None,dict(status='separation_iteration_limit',iterations=limit)


def master(stage,mass,cuts,seconds):
    n,m=stage.n,stage.rows
    nz=n*(m+1); N=nz+2*n
    # z[v,h] chooses the integer middle height; l[j] is final excess.
    table=np.zeros((n,m+1,n),dtype=np.int64)
    for v in range(n):
        for r in range(m):
            table[v,r+1]=table[v,r]
            table[v,r+1,stage.s2[r,v]]+=1
    A=lil_matrix((n+1+2*n+len(cuts),N),dtype=float)
    lo=np.full(A.shape[0],-np.inf); hi=np.zeros(A.shape[0])
    for v in range(n):
        A[v,v*(m+1):(v+1)*(m+1)]=1; lo[v]=hi[v]=1
    heights=np.tile(np.arange(m+1),n)
    A[n,:nz]=heights; lo[n]=hi[n]=mass
    for j in range(n):
        r=n+1+2*j
        A[r,:nz]=-table[:,:,j].reshape(-1)
        A[r,nz+j]=1; A[r,nz+n+j]=m; hi[r]=m-mass/n
        A[r+1,nz+j]=1; A[r+1,nz+n+j]=-m; hi[r+1]=0
    for i,(w,cap) in enumerate(cuts):
        r=n+1+2*n+i
        A[r,:nz]=(w[:,None]*np.arange(m+1)).reshape(-1); hi[r]=cap
    cost=np.r_[np.zeros(nz),-np.ones(n),np.zeros(n)]
    ub=np.r_[np.ones(nz),np.full(n,m),np.ones(n)]
    integer=np.r_[np.ones(nz),np.zeros(n),np.ones(n)]
    result=milp(cost,integrality=integer,bounds=Bounds(np.zeros(N),ub),
                constraints=LinearConstraint(A.tocsr(),lo,hi),
                options=dict(time_limit=seconds,mip_rel_gap=0))
    if result.x is None: raise RuntimeError(result.message)
    z=np.rint(result.x[:nz]).astype(np.int64).reshape(n,m+1)
    assert (z.sum(axis=1)==1).all()
    y=z@np.arange(m+1)
    assert y.sum()==mass
    assert all(w@y<=cap for w,cap in cuts)
    f=advance_many(y[None,:],stage.s2)[0]
    score=int(np.maximum(n*f-mass,0).sum())
    assert abs(-result.fun-score/n)<1e-5
    return y,dict(rows=score/(n*n),score_numerator=score,score_denominator=n*n,
                  numerical_upper_rows=-float(result.mip_dual_bound)/n,
                  status=int(result.status),gap=float(result.mip_gap))


def run(a,seed):
    stage=Stage(a.columns,a.rows,seed); n=stage.n; mass=n*stage.rows//2
    cuts=[]; history=[]
    p=profiles(n,stage.rows,mass) if a.exhaustive else None
    true=None
    if p is not None:
        f=advance_many(advance_many(p,stage.s1),stage.s2)
        true=int(np.maximum(n*f-mass,0).sum(axis=1).max())/(n*n)
    for k in range(a.cuts+1):
        y,info=master(stage,mass,cuts,a.seconds)
        if p is not None and info['status']==0:
            mask=np.ones(len(p),dtype=bool)
            for w,cap in cuts: mask &= p@w<=cap
            final=advance_many(p[mask],stage.s2)
            score=int(np.maximum(n*final-mass,0).sum(axis=1).max())
            assert score==info['score_numerator']
        if k==a.cuts:
            info['separation']={'status':'cut_limit'}; history.append(info); break
        cut,sep=separate(stage.s1,y,mass)
        info['separation']=sep; info['middle']=y.tolist(); history.append(info)
        Path(a.output+'.progress.json').write_text(json.dumps(dict(
            seed=seed,iterations=len(history),history=history),indent=2)+'\n')
        if cut is None: break
        cuts.append(cut)
    witnesses=[support(stage.s1,w,mass)[1] for w,cap in cuts]
    if witnesses:
        f=advance_many(np.array(witnesses),stage.s2)
        lower=int(np.maximum(n*f-mass,0).sum(axis=1).max())/(n*n)
    else:
        lower=0.0
    return dict(columns=n,rows=stage.rows,seed=seed,mass=mass,true_rows=true,
                exact_witness_lower_rows=lower,
                best_numerical_upper_rows=min(x['numerical_upper_rows'] for x in history),
                history=history,cuts=[dict(weights=w.tolist(),cap=cap) for w,cap in cuts],
                note='integer-valid support cuts; numerical MILP bounds, not all-n certificates')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--columns',type=int,default=6); p.add_argument('--rows',type=int,default=8)
    p.add_argument('--seeds',type=int,nargs='+',default=[0,1,2])
    p.add_argument('--cuts',type=int,default=30); p.add_argument('--seconds',type=float,default=20)
    p.add_argument('--exhaustive',action='store_true'); p.add_argument('--output',required=True)
    a=p.parse_args(); results=[]
    for seed in a.seeds:
        r=run(a,seed); results.append(r)
        Path(a.output).write_text(json.dumps(results,indent=2)+'\n')
        print(json.dumps(dict(seed=seed,cuts=len(r['cuts']),true_rows=r['true_rows'],
                             first=r['history'][0],last=r['history'][-1])),flush=True)
    Path(a.output+'.progress.json').unlink(missing_ok=True)

if __name__=='__main__': main()
