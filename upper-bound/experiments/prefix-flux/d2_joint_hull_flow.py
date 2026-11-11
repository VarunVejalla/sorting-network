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


def flow_graph(n,m,M):
    nodes=[(u,s) for u in range(n+1) for s in range(max(0,M-(n-u)*m),min(u*m,M)+1)]
    index={node:i for i,node in enumerate(nodes)}
    arcs=[(u,s,h) for u,s in nodes if u<n for h in range(m+1) if (u+1,s+h) in index]
    return nodes,index,arcs


def verify_affine(d):
    from d2_joint_reachable_gate import support_dp
    n,m,M=d['columns'],d['rows'],d['mass']
    p1,p2=np.array(d['round1']),np.array(d['round2'])
    assert p1.shape==p2.shape==(m,n)
    for p in [p1,p2]:assert all(sorted(row.tolist())==list(range(n)) for row in p)
    nodes,_,arcs=flow_graph(n,m,M);legal=set(arcs)
    balance={node:Fraction(0) for node in nodes};moment=[Fraction(0)]*n
    t1,t2=table(p1),table(p2);T=d['target_set'];phi=t2[:,:,T].sum(axis=2)
    for u,s,h,value in d['flows']:
        assert (u,s,h) in legal
        q=Fraction(value);assert q>=0
        balance[(u,s)]+=q;balance[(u+1,s+h)]-=q
        for v in range(n):moment[v]+=q*int(t1[u,h,v])
    assert all(x==(1 if node==(0,0) else -1 if node==(n,M) else 0) for node,x in balance.items())
    totals=[Fraction(0)]*n;means=[Fraction(0)]*n;objective=Fraction(0)
    for v,h,value in d['distributions']:
        assert 0<=v<n and 0<=h<=m
        q=Fraction(value);assert q>=0
        totals[v]+=q;means[v]+=q*h;objective+=q*int(phi[v,h])
    assert totals==[1]*n and means==moment
    w=np.array(d['weights'],dtype=np.int64);C=d['scale'];assert C>0
    cap=support_dp(p1,w,M);assert cap==d['support_cap']
    residual=(C*phi-w[:,None]*np.arange(m+1)).max(axis=1)
    assert residual.tolist()==d['residual_caps']
    upper=(Fraction(int(cap+residual.sum()),C)-Fraction(len(T)*M,n))/n
    lower=(objective-Fraction(len(T)*M,n))/n
    assert upper==lower==Fraction(d['exact_fixed_target_upper_rows'])
    print(json.dumps(dict(status='exact_affine_primal_dual_verified',value=str(upper))))


def affine_gate(path,output):
    """Fixed-T upper bound from affine envelopes and exact round-one support."""
    from d2_joint_reachable_gate import support_dp
    d=json.loads(Path(path).read_text());n,m,M=d['columns'],d['rows'],d['mass']
    p1,p2=np.array(d['round1']),np.array(d['round2'])
    T=np.array(d['final'])*n>M
    phi=table(p2)[:,:,T].sum(axis=2)
    nodes,index,arcs=flow_graph(n,m,M);nf=len(arcs);nz=n*(m+1)
    A=lil_matrix((len(nodes)+2*n,nf+nz));b=np.zeros(A.shape[0])
    first=table(p1)
    for i,(u,s,h) in enumerate(arcs):
        A[index[(u,s)],i]=1;A[index[(u+1,s+h)],i]=-1
        A[len(nodes)+n:len(nodes)+2*n,i]=first[u,h].reshape(-1,1)
    b[index[(0,0)]]=1;b[index[(n,M)]]=-1
    for v in range(n):
        A[len(nodes)+v,nf+v*(m+1):nf+(v+1)*(m+1)]=1;b[len(nodes)+v]=1
        A[len(nodes)+n+v,nf+v*(m+1):nf+(v+1)*(m+1)]=-np.arange(m+1)
    res=linprog(np.r_[np.zeros(nf),-phi.reshape(-1)],A_eq=A.tocsr(),b_eq=b,
                bounds=(0,None),method='highs')
    if not res.success:raise RuntimeError(res.message)
    from math import lcm
    dual=[Fraction(float(x)).limit_denominator(1000000) for x in res.eqlin.marginals[-n:]]
    C=lcm(*(x.denominator for x in dual));candidates=[]
    for sign in [-1,1]:
        w=np.array([int(sign*C*x) for x in dual],dtype=np.int64)
        cap=support_dp(p1,w,M)
        residual=(C*phi-w[:,None]*np.arange(m+1)).max(axis=1)
        bound=(Fraction(int(cap+residual.sum()),C)-Fraction(int(T.sum())*M,n))/n
        candidates.append((bound,w,cap,residual))
    bound,w,cap,residual=min(candidates,key=lambda x:x[0])
    doc=dict(columns=n,rows=m,mass=M,target_set=np.where(T)[0].tolist(),
             weights=w.tolist(),scale=C,support_cap=cap,residual_caps=residual.tolist(),
             exact_fixed_target_upper_rows=str(bound),numerical_local_concave_relaxation_rows=
             (-float(res.fun)-int(T.sum())*M/n)/n,
             known_joint_witness_rows=d['leakage_rows'])
    exact_x=[Fraction(float(x)).limit_denominator(1000000) for x in res.x]
    csr=A.tocsr()
    for row in range(A.shape[0]):
        assert sum((Fraction(int(csr.data[j]))*exact_x[int(csr.indices[j])]
                    for j in range(csr.indptr[row],csr.indptr[row+1])),Fraction(0))==int(b[row])
    assert all(x>=0 for x in exact_x)
    primal=(sum((exact_x[nf+v*(m+1)+h]*int(phi[v,h])
                 for v in range(n) for h in range(m+1)),Fraction(0))-Fraction(int(T.sum())*M,n))/n
    assert primal==bound
    doc.update(round1=p1.tolist(),round2=p2.tolist(),
               flows=[[u,s,h,str(exact_x[i])] for i,(u,s,h) in enumerate(arcs) if exact_x[i]],
               distributions=[[v,h,str(exact_x[nf+v*(m+1)+h])] for v in range(n)
                              for h in range(m+1) if exact_x[nf+v*(m+1)+h]])
    verify_affine(doc)
    Path(output).write_text(json.dumps(doc,indent=2)+'\n')
    print(json.dumps({k:v for k,v in doc.items() if k not in ['round1','round2','flows','distributions']}))


def solve(a):
    n,m=a.columns,a.rows;M=n*m//2;stage=Stage(n,m,a.seed)
    nodes,node_index,arcs=flow_graph(n,m,M)
    nf=len(arcs);nz=n*(m+1);N=nf+nz+2*n
    nr=len(nodes)+4*n+(1 if a.lower_input else 0)
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
    known_lower=None
    if a.lower_input:
        known=json.loads(Path(a.lower_input).read_text())
        assert known['mass']==M and known['round1']==stage.s1.tolist() and known['round2']==stage.s2.tolist()
        h=np.array(known['input'],dtype=np.int64)
        assert h.sum()==M and (h>=0).all() and (h<=m).all()
        y0=advance_many(h[None,:],stage.s1)
        f0=advance_many(y0,stage.s2)
        known_score=int(np.maximum(n*f0-M,0).sum())
        A[nr-1,nf+nz:nf+nz+n]=1;lo[nr-1]=known_score/n;hi[nr-1]=np.inf
        known_lower=known_score/(n*n)
    result=milp(np.r_[np.zeros(nf+nz),-np.ones(n),np.zeros(n)],
                integrality=np.r_[np.zeros(nf),np.ones(nz),np.zeros(n),np.ones(n)],
                bounds=Bounds(0,np.r_[np.ones(nf+nz),np.full(n,m),np.ones(n)]),
                constraints=LinearConstraint(A.tocsr(),lo,hi),
                options=dict(time_limit=a.seconds,mip_rel_gap=0))
    if result.x is None:
        doc=dict(columns=n,rows=m,seed=a.seed,mass=M,status=int(result.status),
                 outcome='no_incumbent',message=result.message,known_reachable_lower_rows=known_lower)
        Path(a.output).write_text(json.dumps(doc,indent=2)+'\n');print(json.dumps(doc));return
    z=np.rint(result.x[nf:nf+nz]).astype(np.int64).reshape(n,m+1)
    assert (z.sum(axis=1)==1).all()
    target=z@np.arange(m+1)
    mixture=rational_mixture(arcs,result.x[:nf],n,m,M,stage.s1,target)
    final=advance_many(target[None,:],stage.s2)[0]
    score=int(np.maximum(n*final-M,0).sum())
    assert score/n >= -result.fun-1e-5
    if result.status==0:assert abs(-result.fun-score/n)<1e-5
    doc=dict(columns=n,rows=m,seed=a.seed,mass=M,round1=stage.s1.tolist(),round2=stage.s2.tolist(),
             middle=target.tolist(),mixture=mixture,score_numerator=score,score_denominator=n*n,
             numerical_upper_rows=-float(result.mip_dual_bound)/n,status=int(result.status),
             gap=float(result.mip_gap),flow_arcs=nf,
             numerical_incumbent_rows=-float(result.fun)/n,
             known_reachable_lower_rows=known_lower)
    Path(a.output).write_text(json.dumps(doc,indent=2)+'\n');verify(doc)
    print(json.dumps({k:v for k,v in doc.items() if k not in ['round1','round2','mixture']}))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--columns',type=int,default=12);p.add_argument('--rows',type=int,default=4)
    p.add_argument('--seed',type=int,default=0);p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--output');p.add_argument('--verify')
    p.add_argument('--verify-affine')
    p.add_argument('--affine-input',help='direct instance JSON selecting a fixed final target set')
    p.add_argument('--lower-input',help='verified direct input JSON, used as a valid objective cutoff')
    a=p.parse_args()
    if a.verify_affine:
        verify_affine(json.loads(Path(a.verify_affine).read_text()));return
    if a.affine_input:
        if not a.output:p.error('--output required')
        affine_gate(a.affine_input,a.output);return
    if a.verify:verify(json.loads(Path(a.verify).read_text()))
    else:
        if not a.output:p.error('--output required')
        solve(a)

if __name__=='__main__':main()
