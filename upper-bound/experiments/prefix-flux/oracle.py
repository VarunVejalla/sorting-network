#!/usr/bin/env python3
"""Exact Boolean contract-state diagnostics on the existing D2 flow table.

An LP selects integer feasible prefix counts; every returned choice is checked
with integer arithmetic. This is an adversarial local-output oracle, NOT a
fixed comparator network or a proof that a passing configuration sorts.
"""
import argparse
import json
import math
from pathlib import Path
import random
import sys
from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'slackfree'))
from explicit import build_table
from flowsim import Par


def integer(x):
    assert int(x)==x, x
    return int(x)


def word_prefix(word,positions):
    """Prefix zero counts in a run-length Boolean word; 1 represents a zero key."""
    out=[]; end=0; marked=0; j=0
    for pos in positions:
        while j<len(word) and end+word[j][0]<=pos:
            length,bit=word[j]; end+=length; marked+=length*bit; j+=1
        out.append(marked+(pos-end)*word[j][1] if j<len(word) else marked)
    return out


def normalize_word(word):
    out=[]
    for length,bit in word:
        if not length:
            continue
        if out and out[-1][1]==bit:
            out[-1]=(out[-1][0]+length,bit)
        else:
            out.append((length,bit))
    return out


def dominates(output,incoming):
    # Between run endpoints the difference is linear, so endpoint checks suffice.
    positions={0}
    for word in (output,incoming):
        pos=0
        for length,_ in word:
            pos+=length; positions.add(pos)
    positions=sorted(positions)
    return all(a>=b for a,b in zip(word_prefix(output,positions),
                                  word_prefix(incoming,positions)))


def need_capture(j,epsilon):
    if not j:
        return 0
    # Strict integer escape <epsilon*j.
    u=epsilon*j
    return j-(math.ceil(u)-1)


def bounds(a,h,zeros,ends,eps_b,eps_f,delta_f,exact,contract=None):
    assert eps_f>0 and eps_b>=0 and 0<=delta_f<=1
    assert 0<=zeros<=a and 0<=2*h<=a
    budget=0 if exact else int(eps_b*a/2)
    support=int(delta_f*h)
    low=need_capture(min(zeros,support),eps_f)
    high=need_capture(min(a-zeros,support),eps_f)
    if contract is not None:
        budget,extra_low,extra_high=contract
        low=max(low,extra_low); high=max(high,extra_high)
    out=[]
    for p in ends:
        lo=max(0,zeros-(a-p),min(zeros,p)-budget)
        hi=min(zeros,p)
        if p==h:
            lo=max(lo,low)
        if p==a-h:
            lo=max(lo,zeros-h+high)
        if p==0:
            lo=hi=0
        if p==a:
            lo=hi=zeros
        assert lo<=hi,(a,h,zeros,p,budget,lo,hi)
        out.append((lo,hi))
    return out,budget,support


def verify(a,zeros,ends,ys,limits):
    assert ys[0]==0 and ys[-1]==zeros
    for y,(lo,hi) in zip(ys,limits):
        assert isinstance(y,int) and lo<=y<=hi
    for p,q,y,z in zip(ends,ends[1:],ys,ys[1:]):
        assert 0<=z-y<=q-p


def native_weight(node,threshold,p,d):
    lev,idx=node
    if lev<0:
        return 0
    size=p.k**(d-lev)
    lo=idx*size
    if threshold<=lo:
        return 1
    if threshold>=lo+size:
        return -1
    return 0


def choose(a,pi,blocks,zeros,node,p,d,threshold,eps_b,eps_f,
           delta_f,exact,rng,policy,incoming=None,supplied=None,contract=None):
    lev,idx=node
    h=pi//2
    lengths=[h,*blocks,h]
    ends=[0]
    for length in lengths:
        ends.append(ends[-1]+length)
    assert ends[-1]==a and pi%2==0,(node,a,pi,blocks,ends)
    limits,budget,support=bounds(a,h,zeros,ends,eps_b,eps_f,delta_f,exact,contract)
    if incoming is not None:
        limits=[(max(lo,value),hi) for value,(lo,hi) in
                zip(word_prefix(incoming,ends),limits)]
    ideal=[min(zeros,pos) for pos in ends]
    if supplied is not None:
        ys=ideal if supplied=='ideal' else supplied
        verify(a,zeros,ends,ys,limits)
        if exact:
            assert ys==ideal
        return ends,ys,budget,support
    if exact or budget==0 or zeros in (0,a) or pi==a:
        verify(a,zeros,ends,ideal,limits)
        return ends,ideal,budget,support
    destinations=[(lev-1,idx//p.k),
                  *((lev+1,idx*p.k+j) for j in range(p.k)),
                  (lev-1,idx//p.k)]
    weights=[]
    for j,dest in enumerate(destinations):
        weight=native_weight(dest,threshold,p,d)
        if policy=='random':
            weight=rng.uniform(-1,1)
        elif policy=='delay':
            weight=j
        else:
            weight+=rng.uniform(-0.01,0.01)
        weights.append(weight)
    objective=np.zeros(len(ends))
    for j,w in enumerate(weights):
        objective[j]-=w
        objective[j+1]+=w
    matrix=[]
    rhs=[]
    for j,length in enumerate(lengths):
        row=np.zeros(len(ends)); row[j+1]=1; row[j]=-1
        matrix.extend((row,-row)); rhs.extend((length,0))
    result=linprog(-objective,A_ub=np.array(matrix),b_ub=np.array(rhs),
                   bounds=limits,method='highs')
    assert result.success,result.message
    ys=[int(round(v)) for v in result.x]
    verify(a,zeros,ends,ys,limits)  # never trust LP floating-point output alone
    return ends,ys,budget,support


def run(table,p,d,threshold,exact_cap,eps_b,eps_f,delta_f,
        seed=0,policy='native',record=False,monotone=False,replay=None,
        exact_root=True,local_contract=None,terminal=True):
    n=p.k**d
    counts={(0,0):threshold}
    rng=random.Random(seed)
    trace=[]
    sizes={(0,0):n}
    lp_steps=0
    replay_seen=set()
    # 1 denotes a zero key. Reverse initial word maximizes sorting freedom.
    words={(0,0):normalize_word([(n-threshold,0),(threshold,1)])} if monotone else {}
    for t,step in enumerate(table):
        next_counts={}; next_sizes={}
        next_words={}
        handled=set()
        for lev,rows in step.items():
            for idx,(aa,pp,bb) in enumerate(rows):
                a,pi,blocks=integer(aa),integer(pp),list(map(integer,bb))
                if not a:
                    continue
                node=(lev,idx)
                handled.add(node)
                assert sizes.get(node,0)==a,(t,node,sizes.get(node),a)
                zeros=counts.get(node,0)
                if pi==a:
                    # Bottom-rise bags travel whole, including odd-sized bags.
                    assert not any(blocks) and lev>0
                    dest=(lev-1,idx//p.k)
                    next_sizes[dest]=next_sizes.get(dest,0)+a
                    next_counts[dest]=next_counts.get(dest,0)+zeros
                    if monotone:
                        next_words.setdefault(dest,[]).extend(words[node])
                    continue
                exact=a<=exact_cap or (t==0 and exact_root)
                ends,ys,budget,support=choose(a,pi,blocks,zeros,node,p,d,
                    threshold,eps_b,eps_f,delta_f,exact,rng,policy,
                    words[node] if monotone else None,
                    replay.get((t,node),'ideal') if replay is not None else None,
                    local_contract(a,pi,zeros) if local_contract is not None and not exact
                    and zeros not in (0,a) else None)
                if replay is not None and (t,node) in replay:
                    replay_seen.add((t,node))
                if monotone:
                    output=normalize_word([run for length,value in
                        zip(np.diff(ends),np.diff(ys))
                        for run in [(int(value),1),(int(length-value),0)]])
                    assert dominates(output,words[node])
                if ys!=[min(zeros,pos) for pos in ends]:
                    lp_steps+=1
                    if record:
                        trace.append(dict(t=t,node=node,a=a,pi=pi,blocks=blocks,
                                          zeros=zeros,ends=ends,ys=ys,budget=budget,
                                          support=support))
                h=pi//2
                destinations=[(lev-1,idx//p.k),
                    *((lev+1,idx*p.k+j) for j in range(p.k)),
                    (lev-1,idx//p.k)]
                for j,dest in enumerate(destinations):
                    length=ends[j+1]-ends[j]
                    value=ys[j+1]-ys[j]
                    if not length:
                        assert value==0
                        continue
                    assert 0<=dest[0]<=d
                    next_sizes[dest]=next_sizes.get(dest,0)+length
                    next_counts[dest]=next_counts.get(dest,0)+value
                    if monotone:
                        next_words.setdefault(dest,[]).extend([(value,1),(length-value,0)])
        assert set(sizes)==handled,(t,set(sizes)-handled)
        assert sum(next_sizes.values())==n
        assert sum(next_counts.values())==threshold
        counts,sizes=next_counts,next_sizes
        if monotone:
            words={node:normalize_word(parts) for node,parts in next_words.items()}
            assert all(sum(length for length,_ in word)==sizes[node]
                       and sum(length*bit for length,bit in word)==counts[node]
                       for node,word in words.items())
    if replay is not None:
        assert replay_seen==set(replay),'unused replay decisions'
    if not terminal:
        return dict(counts=counts,sizes=sizes,nonideal_choices=lp_steps,trace=trace)
    failures=[]
    intervals=sorted((idx*p.k**(d-lev),(idx+1)*p.k**(d-lev))
                     for lev,idx in sizes)
    assert intervals[0][0]==0 and intervals[-1][1]==n
    assert all(left[1]==right[0] for left,right in zip(intervals,intervals[1:]))
    for node,a in sizes.items():
        lev,idx=node
        native=p.k**(d-lev)
        assert a==native,(node,a,native)
        target=max(0,min(native,threshold-idx*native))
        actual=counts[node]
        if actual!=target:
            failures.append(dict(node=node,capacity=a,actual=actual,target=target))
    return dict(terminal_L1=sum(abs(v['actual']-v['target']) for v in failures),
                wrong_bags=len(failures),nonideal_choices=lp_steps,
                failures=failures,trace=trace)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--depth',type=int,default=8)
    ap.add_argument('--exact-cap',type=int,default=1024)
    ap.add_argument('--eps-b',default='1/100')
    ap.add_argument('--eps-f',default='1/16')
    ap.add_argument('--delta-f',default='1/8')
    ap.add_argument('--thresholds',default='1/2,1/3,1/16')
    ap.add_argument('--policy',choices=('native','random','delay'),default='native')
    ap.add_argument('--seed',type=int,default=0)
    ap.add_argument('--witness')
    ap.add_argument('--monotone',action='store_true',
                    help='track a deterministic concatenation order and preserve every input zero prefix')
    ap.add_argument('--approx-root',action='store_true',
                    help='use the same approximate contract at the initial large root')
    args=ap.parse_args()
    p=Par(2,3,2)
    table,_,_=build_table(p,args.depth,'D2')
    print('ORACLE MODEL; '+('approximate root' if args.approx_root else 'exact root diagnostic')+
          '; no fixed comparator network',flush=True)
    print(f'N={p.k**args.depth}, stages={len(table)}, C={args.exact_cap}, '
          f'epsB={args.eps_b}, epsF={args.eps_f}, policy={args.policy}')
    for fraction in args.thresholds.split(','):
        q=int(F(fraction)*p.k**args.depth)
        result=run(table,p,args.depth,q,args.exact_cap,F(args.eps_b),
                   F(args.eps_f),F(args.delta_f),args.seed,args.policy,
                   record=bool(args.witness),monotone=args.monotone,
                   exact_root=not args.approx_root)
        print(f'q={q}: terminal L1={result["terminal_L1"]}, '
              f'wrong bags={result["wrong_bags"]}, '
              f'nonideal choices={result["nonideal_choices"]}')
        if args.witness and result['terminal_L1']:
            Path(args.witness).write_text(json.dumps(dict(config=vars(args),
                threshold=q,result=result),indent=2)+'\n',encoding='utf8')
            break


if __name__=='__main__':
    main()
