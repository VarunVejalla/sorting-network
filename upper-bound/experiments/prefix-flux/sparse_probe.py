#!/usr/bin/env python3
"""Sparse ordered adversary after an initial inverted rank band.

Only bags meeting currently misplaced wire intervals are processed; other
bags see ideal sorted input and every ascending provider fixes that input.
This still permits input-dependent oracle outputs, NOT one fixed provider.
"""
import argparse
from bisect import bisect_right
from fractions import Fraction as F
import random
from flow_dag import FlowDAG
from oracle import Par,choose,normalize_word,labeled_outputs,dominates
from moderate_tail import ragged
from first_column import first_column
from moderate_tail import bound,interval_envelope
from functools import lru_cache
from math import ceil,floor


def merge(intervals):
    out=[]
    for lo,hi in sorted(intervals):
        if lo>=hi: continue
        if out and lo<=out[-1][1]: out[-1]=(out[-1][0],max(hi,out[-1][1]))
        else: out.append((lo,hi))
    return out


def overlap(intervals,lo,hi):
    j=max(0,bisect_right(intervals,(lo,float('inf')))-1)
    total=0
    while j<len(intervals) and intervals[j][0]<hi:
        a,b=intervals[j]; total+=max(0,min(b,hi)-max(a,lo)); j+=1
    return total


def inversion_count(errors,q,N):
    """Exact binary inversion count for ideal-threshold word XOR errors."""
    left=[]; right=[]
    for lo,hi in errors:
        if lo<q: left.append((lo,min(hi,q)))
        if hi>q: right.append((max(lo,q),hi))
    l=sum(b-a for a,b in left); r=sum(b-a for a,b in right)
    # Wrong ones on the left contribute their later positions, excluding
    # pairs of wrong ones; wrong zeros on the right contribute preceding
    # positions, excluding pairs of wrong zeros. Every left/right pair is
    # also an inversion.
    left_weight=sum((b-a)*(2*q-a-b-1)//2 for a,b in left)
    right_weight=sum((b-a)*(a+b-1-2*q)//2 for a,b in right)
    return left_weight-l*(l-1)//2 + right_weight-r*(r-1)//2 + l*r


def distance_moment(errors,q,power):
    """Exact sum of threshold distances^power over misplaced wires.

    Left-side wrong ones have distance q-x; right-side wrong zeros have
    distance x-q. The nearest right-side wire has weight zero, and power 1
    agrees exactly with the global inversion count.
    """
    def prefix(n):
        if n<=0: return 0
        if power==1: return n*(n+1)//2
        if power==2: return n*(n+1)*(2*n+1)//6
        if power==3: return (n*(n+1)//2)**2
        raise ValueError('distance moment power must be 1, 2, or 3')
    total=0
    for lo,hi in errors:
        left_lo,left_hi=lo,min(hi,q)
        if left_lo<left_hi:
            low=q-left_hi+1; high=q-left_lo
            total+=prefix(high)-prefix(low-1)
        right_lo,right_hi=max(lo,q),hi
        if right_lo<right_hi:
            low=right_lo-q; high=right_hi-q-1
            total+=prefix(high)-prefix(low-1)
    return total


def sum_abs_integer_interval(lo,hi,q):
    """Sum |x-q| over integer wire positions lo <= x < hi."""
    split=max(lo,min(hi,q))
    left=split-lo
    right=hi-split
    return left*q-(lo+split-1)*left//2 + (split+hi-1)*right//2-right*q


def rank_distance_sum(wires,start,stop,q):
    """Sum |wire-q| over local ranks [start,stop) of ordered wire intervals."""
    total=0; rank=0
    for lo,hi in wires:
        a=max(start,rank); b=min(stop,rank+hi-lo)
        if a<b:
            wire_lo=lo+a-rank; wire_hi=lo+b-rank
            total+=sum_abs_integer_interval(wire_lo,wire_hi,q)
        rank+=hi-lo
    assert stop<=rank
    return total


def bag_alignment_inversion(flow,t,errors,q):
    """Exact inversion of the word obtained by sorting every bag at time t."""
    total=0
    for lev,idx,node,wires in affected(flow,t,errors,q)[0]:
        labels=colored(wires,errors,q)
        H=sum((hi-lo)*bit for lo,hi,bit in labels)
        P=sum(max(0,min(hi,q)-lo) for lo,hi,_ in labels)
        if H>P:
            total+=rank_distance_sum(wires,P,H,q)
        elif H<P:
            total+=rank_distance_sum(wires,H,P,q)
    return total


def subtract(intervals,remove):
    out=[]
    for lo,hi in intervals:
        pos=lo
        for a,b in remove:
            if b<=pos or a>=hi: continue
            if pos<a: out.append((pos,a))
            pos=max(pos,b)
        if pos<hi: out.append((pos,hi))
    return out


def colored(wires,errors,q):
    out=[]
    def emit(lo,hi,wrong):
        if lo>=hi: return
        if lo<q<hi:
            out.extend(((lo,q,1^wrong),(q,hi,wrong)))
        else: out.append((lo,hi,int(lo<q)^wrong))
    for lo,hi in wires:
        j=max(0,bisect_right(errors,(lo,float('inf')))-1); pos=lo
        while j<len(errors) and errors[j][0]<hi:
            a,b=errors[j]
            if b>pos:
                emit(pos,min(hi,max(pos,a)),0)
                emit(max(pos,a),min(hi,b),1)
                pos=min(hi,b)
            j+=1
        emit(pos,hi,0)
    return out


def affected(flow,t,errors,q):
    """Find affected bags and the pure-native ancestor cuts they pass through."""
    bags=[]; cuts=[]; todo=[(flow.roots[t],0)]
    while todo:
        node,idx=todo.pop(); lev=flow.nodes[node][0]
        whole=flow.subtree_interval(node,idx)
        if whole is None or not overlap(errors,*whole): continue
        R=flow.native(lev)
        if (idx+1)*R<=q or idx*R>=q: cuts.append((lev,idx,overlap(errors,*whole)))
        wires=flow.bag_intervals(node,idx)
        if any(overlap(errors,*v) for v in wires): bags.append((lev,idx,node,wires))
        todo.extend((c,idx*flow.p.k+j) for j,c in enumerate(flow.nodes[node][4]))
    return bags,cuts


@lru_cache(None)
def profile_tail(total,f,n,m):
    """Uniform baseline/orientation tail, outward-rounded, eta=1/1000."""
    if total==0 or f>=m: return 0
    i=min(m,(total+n-1)//n)
    # PROFILE-GATE chooses one core simultaneously over m baselines,
    # mass classes, output subsets and both orientations.
    _,theta,p0=bound(i,f,n,m,baseline_factor=m)
    upper=interval_envelope(i,f,n,m,theta,p0,baseline_factor=m)
    return min(total,floor(n*upper))


def rank_prefix_lower(a,H,ends,qrows=12):
    assert a%(1<<qrows)==0
    m=1<<qrows; n=a//m; N=a
    lower={}
    for p in ends:
        k,r=divmod(p,n)
        marks=profile_tail(H,k,n,m)
        holes=profile_tail(N-H,m-k,n,m)+r
        semantic=min(marks,holes)
        # Physical output differs from the semantic output by a row-preserving
        # cumulative column permutation, changing a partial prefix by <=r.
        error=semantic+r
        lower[p]=max(0,min(H,p)-error)
    return lower


def probe(d,horizon,root_eps,eps_b,eps_f,delta,threshold,moderate=True,
          initial='band',first_sort=True,scale=1,rank_core=False,
          params=(2,3,2),row_bits=12,trace_stages=False):
    flow=FlowDAG(d,scale=scale,p=Par(*params)).build(); p=flow.p; N=p.k**d*scale; q=int(threshold*N)
    e=min(int(root_eps*N/2),q,N-q)
    assert initial in ('band','outer','left','right','stripes')
    low=(0,e) if initial in ('outer','left') else (q-e,q)
    high=(N-e,N) if initial in ('outer','right') else (q,q+e)
    errors=merge([low,high])
    if initial=='stripes':
        row_count=1<<row_bits; n=N//row_count
        def stripes(lo,hi,phase):
            rows=range((lo+n-1)//n,hi//n)
            width=(e+len(rows)-1)//len(rows)
            assert phase+width<=n
            left=e; out=[]
            for row in rows:
                take=min(width,left)
                if take: out.append((row*n+phase,row*n+phase+take))
                left-=take
            assert left==0
            return out
        errors=merge(stripes(0,q,n//7)+stripes(q,N,5*n//7))
    history=[2*e]; inv_history=[inversion_count(errors,q,N)]; rng=random.Random(0)
    stage_trace=[]
    initial_alignment=bag_alignment_inversion(flow,0,errors,q) if trace_stages else None
    assert e>0,'choose a larger diagnostic N for nonzero initial error'
    # Each profile has maximum diagonal prefix deficit e, hence fits the root
    # bulk bound. No root fringe guarantee is asserted by this initializer.
    for t in range(1,min(horizon,len(flow.rows))):
        bags,_=affected(flow,t,errors,q)
        before_inv=inv_history[-1]
        roles={}; events=[]
        for lev,idx,node,wires in bags:
            a,pi,blocks=flow.rows[t][node]
            if pi==a: continue
            role=p.role(d,lev,t)
            roles[role]=roles.get(role,0)+1
            event=None
            if trace_stages:
                event=dict(role=role,level=lev,index=idx,a=a,pi=pi,
                           blocks=tuple(blocks),
                           wrong_before=overlap(errors,*flow.subtree_interval(node,idx)))
                events.append(event)
            labels=colored(wires,errors,q)
            incoming=normalize_word([(hi-lo,bit) for lo,hi,bit in labels])
            original=incoming
            if first_sort:
                incoming=first_column(incoming,q=row_bits)
            H=sum(length*bit for length,bit in incoming)
            P=sum(max(0,min(hi,q)-lo) for lo,hi,_ in labels)
            contract=None
            # One column is sorted exactly by the first column sort. There is
            # no random permutation union to estimate when n=1.
            row_count=1<<row_bits
            exact=moderate and not rank_core and a<=row_count
            if moderate and not rank_core and a>row_count and pi and H not in (0,a):
                n=(a+row_count-1)//row_count; L,r=divmod(a,n)
                low=ragged(a,pi//2,H)['integer_bound']
                high=ragged(a,pi//2,a-H)['integer_bound']
                contract=(int(eps_b*L*n/2)+4*r,H-low,a-H-high)
            pos=0; extra=[]
            for length,_ in incoming:
                pos+=length; extra.append(pos)
            local_ends=[0];pos=0
            for length in [pi//2,*blocks,pi//2]:
                pos+=length;local_ends.append(pos)
            prefix_lower=(rank_prefix_lower(a,H,sorted(set(local_ends+extra+[P])),row_bits)
                          if rank_core else None)
            local_parameters=(F(2),F(1),F(0)) if rank_core else (eps_b,eps_f,delta)
            ends,ys,_,_=choose(a,pi,blocks,H,(lev,idx),p,d,q,*local_parameters,
                exact,rng,'identity',incoming=incoming,contract=contract,
                target_cut=P,extra_cuts=extra,prefix_lower=prefix_lower)
            output=labeled_outputs(labels,ends,ys)
            outword=normalize_word([(hi-lo,bit) for lo,hi,bit in output])
            assert dominates(outword,incoming)
            assert dominates(outword,original)
            new=[]
            for lo,hi,bit in output:
                if bit==0 and lo<q: new.append((lo,min(hi,q)))
                if bit==1 and hi>q: new.append((max(lo,q),hi))
            if event is not None:
                event.update(input_zeros=H,threshold_zeros=P,
                             wrong_after=sum(hi-lo for lo,hi in new))
            errors=merge(subtract(errors,wires)+new)
        total=sum(b-a for a,b in errors)
        assert total<=history[-1]
        history.append(total)
        inv_next=inversion_count(errors,q,N)
        assert inv_next<=inv_history[-1]
        inv_history.append(inv_next)
        if trace_stages:
            alignment=bag_alignment_inversion(flow,t+1,errors,q)
            assert 0<=alignment<=inv_next,(t,alignment,inv_next)
            moment1=distance_moment(errors,q,1)
            assert moment1==inv_next,(moment1,inv_next)
            stage_trace.append(dict(t=t,bags=len(bags),roles=roles,
                                    before=before_inv,after=inv_next,
                                    drop=before_inv-inv_next,
                                    wrong_bits=total,alignment=alignment,
                                    local_defect_area=inv_next-alignment,
                                    distance_moment_1=moment1,
                                    distance_moment_2=distance_moment(errors,q,2),
                                    distance_moment_3=distance_moment(errors,q,3),
                                    events=events))
        _,cuts=affected(flow,t+1,errors,q)
        for lev,idx,wrong in cuts:
            future=sum(flow.row(u,lev,idx)[1] for u in range(t+1,len(flow.rows))
                       if p.active(d,lev,u))
            if wrong>future:
                return dict(fail=True,t=t+1,node=(lev,idx),wrong=wrong,
                            future=future,history=history,states=len(flow.nodes))
    complete=len(history)==len(flow.rows)
    terminal=None
    if complete:
        # A perfect native-block cleanup can repair the single block whose
        # native interval contains q. Every other occupied final bag must be
        # pure. This is stronger than merely observing small total error.
        mixed=0; pure=0
        for lev,idx,node,wires in affected(flow,len(flow.rows),errors,q)[0]:
            R=flow.native(lev)
            assert wires==[(idx*R,(idx+1)*R)]
            wrong=sum(overlap(errors,*v) for v in wires)
            if idx*R<q<(idx+1)*R: mixed+=wrong
            else: pure+=wrong
        terminal=dict(pure_wrong=pure,mixed_wrong=mixed,
                      cleanup_sorts_this_execution=pure==0)
    from math import log2
    final_inv=inv_history[-1]
    return dict(fail=False,history=history,inversion_history=inv_history,
                initial_inversions=inv_history[0],final_inversions=final_inv,
                final_inversion_exponent=(log2(final_inv)/log2(N) if final_inv else 0.0),
                states=len(flow.nodes),terminal=terminal,
                initial_alignment=initial_alignment,
                stage_trace=stage_trace if trace_stages else None)


if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--depth',type=int,default=20)
    ap.add_argument('--horizon',type=int,default=32)
    ap.add_argument('--root-eps',default='1/10000000')
    ap.add_argument('--threshold',default='1/3')
    ap.add_argument('--eps-f',default='1/16'); ap.add_argument('--delta',default='1/8')
    ap.add_argument('--initial',choices=['band','outer','left','right','stripes'],default='band')
    ap.add_argument('--skip-first-sort',action='store_true',
                    help='weaker postcondition-only oracle; omits mandatory first sort')
    ap.add_argument('--scale',type=int,default=1,
                    help='uniform wire-count inflation for the D2 flow')
    ap.add_argument('--params',nargs=3,type=int,default=(2,3,2),metavar=('X','Y','Z'))
    ap.add_argument('--row-bits',type=int,default=12,
                    help='log2 of the exact rectangular core row count')
    ap.add_argument('--verbose',action='store_true',
                    help='print full error and inversion histories')
    ap.add_argument('--rank-core',action='store_true',
                    help='impose reviewed whole-row spill-tail rank limits')
    ap.add_argument('--coarse',action='store_true')
    args=ap.parse_args()
    result=probe(args.depth,args.horizon,F(args.root_eps),F(19,2000),
                 F(args.eps_f),F(args.delta),F(args.threshold),not args.coarse,
                 args.initial,not args.skip_first_sort,args.scale,args.rank_core,
                 tuple(args.params),args.row_bits)
    print('SPARSE RELATIONAL ORACLE; no fixed-network or all-input upper bound')
    if args.verbose:
        print(result)
    else:
        print({key:result[key] for key in (
            'fail','initial_inversions','final_inversions',
            'final_inversion_exponent','states','terminal')
            if key in result})
