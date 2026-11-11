"""Full fixed-mass reachable hull via DP flow; finite numerical MILP screen.

A unit path chooses actual input heights with exact total mass. Continuous
flow gives exactly their convex hull. Integer middle heights and round two
are retained. Rational input mixtures can certify feasible hull obstructions;
solver upper bounds remain numerical.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import milp,linprog,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
from d2_bulk_attack import Stage
from d2_joint_direct import table
from d2_joint_reachable_gate import advance_many


def rational_mixture(arcs,flow,n,m,M,perm,target):
    outgoing={}
    for i,(u,s,h) in enumerate(arcs):outgoing.setdefault((u,s),[]).append(i)
    rem=np.maximum(flow,0).copy();paths=[]
    while sum(rem[i] for i in outgoing[(0,0)])>1e-7:
        path=[];heights=[];s=0
        for u in range(n):
            candidates=[i for i in outgoing[(u,s)] if rem[i]>1e-8]
            if not candidates:raise RuntimeError('numerical flow decomposition failed')
            i=max(candidates,key=lambda i:rem[i]);path.append(i)
            h=arcs[i][2];heights.append(h);s+=h
        assert s==M
        amount=min(rem[i] for i in path)
        rem[path]-=amount;paths.append(heights)
    paths=np.unique(np.array(paths,dtype=np.int64),axis=0)
    mids=advance_many(paths,perm)
    A=np.vstack([np.ones(len(paths)),mids.T]);b=np.r_[1,target]
    result=linprog(np.zeros(len(paths)),A_eq=A,b_eq=b,bounds=(0,None),method='highs')
    if not result.success:raise RuntimeError('decomposed paths do not reproduce target')
    chosen=np.where(result.x>1e-8)[0]
    from sympy import Matrix
    exact,params=Matrix(A[:,chosen].astype(int).tolist()).gauss_jordan_solve(Matrix(b.tolist()))
    if params.rows:raise RuntimeError('dependent mixture support')
    weights=[Fraction(str(x)) for x in exact]
    assert all(w>=0 for w in weights)
    return [dict(weight=str(w),input=paths[i].tolist()) for i,w in zip(chosen,weights) if w]


def verify(doc):
    p1=np.array(doc['round1'],dtype=np.int64);p2=np.array(doc['round2'],dtype=np.int64)
    m,n=p1.shape;M=doc['mass'];target=doc['middle']
    assert p2.shape==p1.shape and doc['columns']==n and doc['rows']==m
    assert len(target)==n and all(isinstance(y,int) and 0<=y<=m for y in target) and sum(target)==M
    for perm in [p1,p2]:assert all(sorted(row.tolist())==list(range(n)) for row in perm)
    total=Fraction(0);mean=[Fraction(0) for _ in range(n)]
    for item in doc['mixture']:
        w=Fraction(item['weight'])
        assert all(isinstance(x,int) for x in item['input'])
        h=np.array(item['input'],dtype=np.int64)
        assert w>=0 and len(h)==n and (h>=0).all() and (h<=m).all() and h.sum()==M
        y=advance_many(h[None,:],p1)[0]
        total+=w
        for v in range(n):mean[v]+=w*int(y[v])
    assert total==1 and mean==[Fraction(y) for y in target]
    final=advance_many(np.array([target],dtype=np.int64),p2)[0]
    score=int(np.maximum(n*final-M,0).sum())
    assert score==doc['score_numerator'] and doc['score_denominator']==n*n
    print(json.dumps(dict(status='exact_rational_hull_witness_verified',paths=len(doc['mixture']),
                          numerator=score,denominator=n*n)))


def solve(a):
    n,m=a.columns,a.rows;M=n*m//2;stage=Stage(n,m,a.seed)
    nodes=[(u,s) for u in range(n+1) for s in range(max(0,M-(n-u)*m),min(u*m,M)+1)]
    node_index={node:i for i,node in enumerate(nodes)}
    arcs=[(u,s,h) for u,s in nodes if u<n for h in range(m+1) if (u+1,s+h) in node_index]
    nf=len(arcs);nz=n*(m+1);N=nf+nz+2*n
    nr=len(nodes)+4*n
    A=lil_matrix((nr,N),dtype=float);lo=np.zeros(nr);hi=np.zeros(nr)
    t1,t2=table(stage.s1),table(stage.s2)
    for i,(u,s,h) in enumerate(arcs):
        A[node_index[(u,s)],i]+=1;A[node_index[(u+1,s+h)],i]-=1
        A[len(nodes)+n:len(nodes)+2*n,i]=t1[u,h].reshape(-1,1)
    lo[node_index[(0,0)]]=hi[node_index[(0,0)]]=1
    lo[node_index[(n,M)]]=hi[node_index[(n,M)]]=-1
    for v in range(n):
        r=len(nodes)+v
        A[r,nf+v*(m+1):nf+(v+1)*(m+1)]=1;lo[r]=hi[r]=1
        A[len(nodes)+n+v,nf+v*(m+1):nf+(v+1)*(m+1)]=-np.arange(m+1)
    for j in range(n):
        r=len(nodes)+2*n+2*j
        A[r,nf:nf+nz]=-t2[:,:,j].reshape(-1)
        A[r,nf+nz+j]=1;A[r,nf+nz+n+j]=m;lo[r]=-np.inf;hi[r]=m-M/n
        A[r+1,nf+nz+j]=1;A[r+1,nf+nz+n+j]=-m;lo[r+1]=-np.inf;hi[r+1]=0
    result=milp(np.r_[np.zeros(nf+nz),-np.ones(n),np.zeros(n)],
                integrality=np.r_[np.zeros(nf),np.ones(nz),np.zeros(n),np.ones(n)],
                bounds=Bounds(0,np.r_[np.ones(nf+nz),np.full(n,m),np.ones(n)]),
                constraints=LinearConstraint(A.tocsr(),lo,hi),
                options=dict(time_limit=a.seconds,mip_rel_gap=0))
    if result.x is None:raise RuntimeError(result.message)
    z=np.rint(result.x[nf:nf+nz]).astype(np.int64).reshape(n,m+1)
    assert (z.sum(axis=1)==1).all()
    target=z@np.arange(m+1)
    mixture=rational_mixture(arcs,result.x[:nf],n,m,M,stage.s1,target)
    final=advance_many(target[None,:],stage.s2)[0]
    score=int(np.maximum(n*final-M,0).sum())
    assert abs(-result.fun-score/n)<1e-5
    doc=dict(columns=n,rows=m,seed=a.seed,mass=M,round1=stage.s1.tolist(),round2=stage.s2.tolist(),
             middle=target.tolist(),mixture=mixture,score_numerator=score,score_denominator=n*n,
             numerical_upper_rows=-float(result.mip_dual_bound)/n,status=int(result.status),
             gap=float(result.mip_gap),flow_arcs=nf)
    Path(a.output).write_text(json.dumps(doc,indent=2)+'\n');verify(doc)
    print(json.dumps({k:v for k,v in doc.items() if k not in ['round1','round2','mixture']}))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--columns',type=int,default=12);p.add_argument('--rows',type=int,default=4)
    p.add_argument('--seed',type=int,default=0);p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--output');p.add_argument('--verify')
    a=p.parse_args()
    if a.verify:verify(json.loads(Path(a.verify).read_text()))
    else:
        if not a.output:p.error('--output required')
        solve(a)

if __name__=='__main__':main()
