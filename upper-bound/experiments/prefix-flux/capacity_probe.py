#!/usr/bin/env python3
"""Bounded-horizon necessary global gate for the strengthened UB-42 interface.

Retains the OLD UNPRICED rare-fringe contract as an optimistic assumption.
Negative cut-capacity evidence is useful; a pass is not a sorting proof.
This uses concatenation order, NOT the static-label order of R1Wire/R1Exec.
The rectangular bulk scalar is assumed, not numerically certified here.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from oracle import Par,build_table,run
from moderate_tail import ragged


def cut_gaps(state,p,d,t,q):
    wrong={}
    for (lev,idx),a in state['sizes'].items():
        H=state['counts'][(lev,idx)]
        for l in range(lev+1):
            ancestor=idx//p.k**(lev-l)
            size=p.k**(d-l)
            color=(1 if (ancestor+1)*size<=q else
                   0 if ancestor*size>=q else None)
            if color is not None:
                key=(l,ancestor)
                wrong[key]=wrong.get(key,0)+(a-H if color else H)
    gaps=[]
    for node,population in wrong.items():
        if not population:
            continue
        lev,_=node
        future=[u for u in range(t,p.tf(d)) if p.active(d,lev,u)]
        if any(p.role(d,lev,u)=='botRise' for u in future):
            continue  # whole-bag rise needs a different capacity upper bound
        escape=sum((p.up(d,lev,u) for u in future),F(0))
        gaps.append((F(population)-escape,node,population,escape))
    return sorted(gaps,reverse=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--depth',type=int,default=14)
    ap.add_argument('--horizon',type=int,default=6)
    ap.add_argument('--threshold',default='1/3')
    ap.add_argument('--exact-cap',type=int,default=2**21)
    ap.add_argument('--eps-b',default='19/2000')
    ap.add_argument('--coarse',action='store_true')
    ap.add_argument('--exact-root',action='store_true',help='unpriced diagnostic only')
    args=ap.parse_args()
    p=Par(2,3,2); eps=F(args.eps_b)
    table,_,_=build_table(p,args.depth,'D2',horizon=args.horizon)
    @lru_cache(None)
    def contract(a,pi,H):
        n=(a+4095)//4096; L,r=divmod(a,n); h=pi//2
        budget=int(eps*L*n/2)+4*r
        if h==0:
            return budget,0,0
        lo=ragged(a,h,H)['integer_bound']
        hi=ragged(a,h,a-H)['integer_bound']
        return budget,H-lo,a-H-hi
    q=int(F(args.threshold)*p.k**args.depth)
    result=run(table,p,args.depth,q,args.exact_cap,eps,F(1,16),F(1,8),
               monotone=True,exact_root=args.exact_root,terminal=False,
               local_contract=None if args.coarse else contract)
    gaps=cut_gaps(result,p,args.depth,len(table),q)
    print('NECESSARY CAPACITY GATE ONLY; original rare contract retained, unpriced')
    print(f'd={args.depth} t={len(table)} q={q} C={args.exact_cap} '
          f'moderate={not args.coarse} exactroot={args.exact_root} '
          f'nonideal={result["nonideal_choices"]}')
    if gaps:
        gap,node,population,escape=gaps[0]
        print(f'worst cut {node}: wrong={population}, future escape<={escape}, '
              f'gap={gap}; '+('FAIL' if gap>0 else 'no witnessed violation'))
    else:
        print('no eligible wrong-color cut; no witnessed violation')
