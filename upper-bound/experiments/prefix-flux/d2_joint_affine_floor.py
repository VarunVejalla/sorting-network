"""Exact fixed-scramble floor for affine-envelope joint bounds.

Uniform middle height c=m/2 is reachable for every first scramble. Per column,
a distribution over two heights with mean c is feasible for the local envelope
relaxation. Its value lower-bounds EVERY weighted-support/affine-envelope bound.
This screens the affine relaxation, not the integer-middle full hull model.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path
import numpy as np


def counts(n,m,seed):
    assert n%2==0 and m%8==0
    rng=np.random.default_rng(seed);running=np.zeros(n,dtype=np.int64)
    snapshots=[running.copy()]
    for r in range(m):
        running+=rng.permutation(n)<n//2
        if (r+1)%(m//8)==0:snapshots.append(running.copy())
    return np.array(snapshots)


def generate(n,m,seed):
    phi=counts(n,m,seed);pairs=[];values=[]
    for v in range(n):
        best=Fraction(int(phi[4,v]));pair=[4,4]
        for a in range(4):
            for b in range(5,9):
                value=Fraction((b-4)*int(phi[a,v])+(4-a)*int(phi[b,v]),b-a)
                if value>best:best=value;pair=[a,b]
        pairs.append(pair);values.append(best)
    floor=(sum(values)-n*m//4)/n
    return dict(columns=n,rows=m,seed=seed,target='first half of destination columns',
                endpoint_counts=phi.tolist(),pairs=pairs,floor_rows=str(floor))


def verify(d):
    n,m,seed=d['columns'],d['rows'],d['seed'];phi=counts(n,m,seed)
    assert phi.tolist()==d['endpoint_counts'] and len(d['pairs'])==n
    value=Fraction(0)
    for v,(a,b) in enumerate(d['pairs']):
        if a==b:
            assert a==4;value+=int(phi[4,v])
        else:
            assert 0<=a<4<b<=8
            value+=Fraction((b-4)*int(phi[a,v])+(4-a)*int(phi[b,v]),b-a)
    assert int(phi[4].sum())==n*m//4
    floor=(value-n*m//4)/n
    assert floor==Fraction(d['floor_rows'])
    print(json.dumps(dict(status='exact_affine_floor_verified',seed=seed,
                         floor_rows=str(floor),decimal=float(floor))))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--columns',type=int,default=256);p.add_argument('--rows',type=int,default=8192)
    p.add_argument('--seed',type=int,default=0);p.add_argument('--output');p.add_argument('--verify')
    a=p.parse_args()
    if a.verify:verify(json.loads(Path(a.verify).read_text()))
    else:
        if not a.output:p.error('--output required')
        d=generate(a.columns,a.rows,a.seed);verify(d)
        Path(a.output).write_text(json.dumps(d,indent=2)+'\n')

if __name__=='__main__':main()
