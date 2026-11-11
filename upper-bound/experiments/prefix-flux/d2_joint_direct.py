"""Direct finite two-round MILP; input and middle heights are coupled exactly.

Returned network witnesses are checked with integers. Solver upper bounds are
numerical. Use d2_joint_exhaustive.cpp for an independent exhaustive optimum.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
from d2_bulk_attack import Stage
from d2_joint_reachable_gate import advance_many


def table(perm):
    m,n=perm.shape
    out=np.zeros((n,m+1,n),dtype=np.int64)
    for u in range(n):
        for h in range(m):
            out[u,h+1]=out[u,h]
            out[u,h+1,perm[h,u]]+=1
    return out


def solve(n,m,seed,seconds):
    stage=Stage(n,m,seed); M=n*m//2
    nz=n*(m+1); N=2*nz+2*n
    A=lil_matrix((5*n+1,N),dtype=float)
    lo=np.full(5*n+1,-np.inf); hi=np.zeros(5*n+1)
    t1,t2=table(stage.s1),table(stage.s2)
    for u in range(n):
        A[u,u*(m+1):(u+1)*(m+1)]=1;lo[u]=hi[u]=1
        A[n+u,nz+u*(m+1):nz+(u+1)*(m+1)]=1;lo[n+u]=hi[n+u]=1
        A[2*n+u,:nz]=t1[:,:,u].reshape(-1)
        A[2*n+u,nz+u*(m+1):nz+(u+1)*(m+1)]=-np.arange(m+1)
        lo[2*n+u]=hi[2*n+u]=0
    A[3*n,:nz]=np.tile(np.arange(m+1),n);lo[3*n]=hi[3*n]=M
    for j in range(n):
        r=3*n+1+2*j
        A[r,nz:2*nz]=-t2[:,:,j].reshape(-1)
        A[r,2*nz+j]=1;A[r,2*nz+n+j]=m;hi[r]=m-M/n
        A[r+1,2*nz+j]=1;A[r+1,2*nz+n+j]=-m
    cost=np.r_[np.zeros(2*nz),-np.ones(n),np.zeros(n)]
    result=milp(cost,integrality=np.r_[np.ones(2*nz),np.zeros(n),np.ones(n)],
                bounds=Bounds(0,np.r_[np.ones(2*nz),np.full(n,m),np.ones(n)]),
                constraints=LinearConstraint(A.tocsr(),lo,hi),
                options=dict(time_limit=seconds,mip_rel_gap=0))
    if result.x is None:raise RuntimeError(result.message)
    x=np.rint(result.x[:nz]).astype(np.int64).reshape(n,m+1)
    z=np.rint(result.x[nz:2*nz]).astype(np.int64).reshape(n,m+1)
    assert (x.sum(axis=1)==1).all() and (z.sum(axis=1)==1).all()
    h=x@np.arange(m+1);y=z@np.arange(m+1)
    assert h.sum()==M and (advance_many(h[None,:],stage.s1)[0]==y).all()
    f=advance_many(y[None,:],stage.s2)[0]
    score=int(np.maximum(n*f-M,0).sum())
    assert abs(-result.fun-score/n)<1e-5
    return dict(columns=n,rows=m,seed=seed,mass=M,round1=stage.s1.tolist(),round2=stage.s2.tolist(),
                input=h.tolist(),middle=y.tolist(),final=f.tolist(),score_numerator=score,
                score_denominator=n*n,leakage_rows=score/(n*n),status=int(result.status),
                numerical_upper_rows=-float(result.mip_dual_bound)/n,gap=float(result.mip_gap))


def verify_audit(instance_path,audit_path):
    a=json.loads(Path(instance_path).read_text());b=json.loads(Path(audit_path).read_text())
    n,m,M=a['columns'],a['rows'],a['mass']
    count=[0]*(M+1);count[0]=1
    for u in range(n):
        count=[sum(count[s-h] for h in range(m+1) if 0<=s-h<=M) for s in range(M+1)]
    assert b['profiles']==count[M] and b['denominator']==n*n
    for source,key in [(a,'input'),(b,'input')]:
        h=np.array(source[key],dtype=np.int64)
        assert len(h)==n and (h>=0).all() and (h<=m).all() and h.sum()==M
        mid=advance_many(h[None,:],np.array(a['round1'],dtype=np.int64))
        final=advance_many(mid,np.array(a['round2'],dtype=np.int64))
        assert int(np.maximum(n*final-M,0).sum())==b['maximum_numerator']
    assert a['score_numerator']==b['maximum_numerator']
    print(json.dumps(dict(status='audit_count_and_witnesses_verified',profiles=count[M],
                          numerator=b['maximum_numerator'],denominator=n*n)))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--columns',type=int,default=12);p.add_argument('--rows',type=int,default=4)
    p.add_argument('--seed',type=int,default=0);p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--output')
    p.add_argument('--verify-audit',nargs=2,metavar=('INSTANCE_JSON','AUDIT_JSON'))
    a=p.parse_args()
    if a.verify_audit:
        verify_audit(*a.verify_audit);return
    if not a.output:p.error('--output is required for a solve')
    r=solve(a.columns,a.rows,a.seed,a.seconds)
    Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
    text=[f"{r['columns']} {r['rows']} {r['mass']}"]
    text += [' '.join(map(str,row)) for key in ['round1','round2'] for row in r[key]]
    Path(a.output+'.instance.txt').write_text('\n'.join(text)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ['round1','round2']}))

if __name__=='__main__':main()
