#!/usr/bin/env python3
"""Finite exact screen for height-balanced ragged D2 shapes.

For each distinct (allocation, up-port) in the compressed flow, find a balanced
column profile with a bounded fringe, 0 <= b_j, and
2*f_j + 64*b_j <= 8192. Both modes default to a 13-row floor. This tests
geometry only, not provider probability or global sorting correctness.
"""
from collections import Counter
from fractions import Fraction
import argparse
from mpmath import iv

from flow_dag import FlowDAG
from oracle import Par
from ragged_fringe_geometry import port_misalignment


def median_cut_mismatch(profile, rows=8192, groups=64):
    """Worst L1 boundary mismatch using a separate median row cut per q."""
    n=sum(profile.values())
    worst=0
    for q in range(groups+1):
        cuts=sorted((rows-f-(groups-q)*b,count)
                    for (f,b),count in profile.items())
        target=(n-1)//2
        cumulative=0
        median=cuts[-1][0]
        for cut,count in cuts:
            cumulative+=count
            if cumulative>target:
                median=cut
                break
        worst=max(worst,sum(count*abs(cut-median) for cut,count in cuts))
    return worst


def equalized_profile(a, pi, rows=8192, tail=13, groups=64, min_n=1):
    if pi % 2 or a < pi or (a - pi) % groups:
        return None, "integrality"
    F, B = pi // 2, (a - pi) // groups
    bmax = (rows - 2 * tail) // groups
    n0 = max(min_n, (B + bmax - 1) // bmax, (a + rows - 1) // rows)
    nmax = F // tail
    if n0 > nmax:
        return None, ("fringe-capacity", n0, nmax, F, B)
    # Assign fringe widths against b_j so every column has nearly the same
    # total height. Since 2F+64B=a, the integer remainder after flooring is
    # between 0 and n-1 and can be paid by adding one fringe row per column.
    for n in range(n0, min(nmax, n0) + 1):
        q, r = divmod(B, n)
        if q + (r > 0) > bmax:
            continue
        prof = Counter()
        f0, f1 = (a // n - groups*q) // 2, (a // n - groups*(q+1)) // 2
        if n-r:
            prof[(f0,q)] += n-r
        if r:
            prof[(f1,q+1)] += r
        rem = F - (f0*(n-r) + f1*r)
        for b, f, count in sorted(((q,f0,n-r),(q+1,f1,r)),
                                  key=lambda x: (-x[2], x[0])):
            take = min(rem, count)
            if take:
                prof[(f,b)] -= take
                if not prof[(f,b)]: del prof[(f,b)]
                prof[(f+1,b)] += take
                rem -= take
        if rem:
            continue
        if any(f < tail or 2*f + groups*b > rows for f,b in prof):
            continue
        assert sum(c*f for (f,_),c in prof.items()) == F
        assert sum(c*b for (_,b),c in prof.items()) == B
        assert all(f >= tail and 2*f+groups*b <= rows for f,b in prof)
        return (n, prof, F, B), None
    return None, ("equalized-fit", n0, n0, F, B)


def waterfill_profile(a, pi, rows=8192, tail=13, groups=64, min_n=1):
    """Balance total column heights subject to f>=tail and wire capacity.

    This avoids relying on the equalized-profile formula to keep every fringe
    above its lower bound. It minimizes height spread by integer water filling;
    the resulting cut mismatch still has to be checked separately.
    """
    if pi % 2 or a < pi or (a - pi) % groups:
        return None, "integrality"
    F, B = pi // 2, (a - pi) // groups
    bmax = (rows - 2 * tail) // groups
    n = max(min_n, (B + bmax - 1) // bmax, (a + rows - 1) // rows)
    if F < tail * n:
        return None, ("fringe-capacity", n, F // tail, F, B)
    q, r = divmod(B, n)
    groups_by_b = [(q, n-r)] + ([(q+1, r)] if r else [])
    if any(b > bmax for b, _ in groups_by_b):
        return None, ("bulk-capacity", n, B)
    total_height = F + 32 * B
    if total_height > rows * n:
        return None, ("height-capacity", n, total_height)

    def filled(level):
        return sum(count * min(rows // 2, max(tail + 32*b, level))
                   for b, count in groups_by_b)

    # Largest integer level whose clipped profile does not exceed the target.
    left, right = 0, rows // 2
    while left < right:
        mid = (left + right + 1) // 2
        if filled(mid) <= total_height:
            left = mid
        else:
            right = mid - 1
    level = left
    rem = total_height - filled(level)
    prof = Counter()
    eligible = []
    for b, count in groups_by_b:
        x = min(rows // 2, max(tail + 32*b, level))
        prof[(x - 32*b, b)] += count
        if tail + 32*b <= level < rows // 2:
            eligible.append((b, count))
    for b, count in eligible:
        take = min(rem, count)
        if take:
            prof[(level + 1 - 32*b, b)] += take
            prof[(level - 32*b, b)] -= take
            if not prof[(level - 32*b, b)]:
                del prof[(level - 32*b, b)]
            rem -= take
    if rem:
        return None, ("waterfill-remainder", n, rem)
    if any(f < tail or 2*f + groups*b > rows for f, b in prof):
        return None, ("waterfill-geometry", n, dict(prof))
    assert sum(c*f for (f, _), c in prof.items()) == F
    assert sum(c*b for (_, b), c in prof.items()) == B
    return (n, prof, F, B), None


def run(depth, scale, min_n, rows=8192, tail=13, min_time=0,
        allocation="equalized"):
    p = Par(3,3,2)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    seen = {}
    failed = Counter()
    failure_examples = {}
    cut_fail_keys = set()
    worst = None
    min_fringe = None
    min_columns_seen = None
    min_columns_for_fringe = {}
    for t, step in enumerate(flow.rows):
        for node, (a,pi,_) in step.items():
            if t < min_time:
                continue
            lev = flow.nodes[node][0]
            role = p.role(depth,lev,t)
            if role not in {"mid","botDesc","topRise"} or not a or not pi:
                continue
            key=(a,pi)
            if key not in seen:
                profile_fn = (waterfill_profile if allocation == "waterfill"
                              else equalized_profile)
                profile_tail = tail
                shape, why = profile_fn(a,pi,rows,profile_tail,64,min_n)
                seen[key]=(shape,why,role,t,lev)
            shape,why,first_role,first_t,first_lev=seen[key]
            if shape is None:
                failed[str(why[0] if isinstance(why,tuple) else why)] += 1
                failure_examples.setdefault(str(why[0] if isinstance(why,tuple) else why), (why,a,pi,first_role,first_t,first_lev))
                continue
            n,prof,F,B=shape
            if min_columns_seen is None or n < min_columns_seen[0]:
                min_columns_seen=(n,a,pi,role,t,lev,dict(prof))
            fmin=min(f for f,_ in prof)
            old=min_columns_for_fringe.get(fmin)
            if old is None or n<old[0]:
                min_columns_for_fringe[fmin]=(n,a,pi,role,t,lev)
            if min_fringe is None or fmin < min_fringe[0]:
                min_fringe=(fmin,n,a,pi,role,t,lev,dict(prof))
            mismatch=median_cut_mismatch(prof,rows,64)
            # d=11/2500 in full B2 gives leakage d/2; epsB=17/2000
            # in the ragged cut contract leaves (epsB-d)/2 for geometry.
            slack=Fraction(41,20000)*rows*n
            if mismatch > slack:
                if key not in cut_fail_keys:
                    cut_fail_keys.add(key)
                    failed["cut-slack"] += 1
                score=Fraction(mismatch,n)
                if worst is None or score>worst[0]:
                    worst=(score,mismatch,n,a,pi,first_role,first_t,first_lev,dict(prof))
                continue
            score=Fraction(mismatch, n)
            if worst is None or score>worst[0]:
                worst=(score,mismatch,n,a,pi,first_role,first_t,first_lev,dict(prof))
    print(f"profile={allocation}, depth={depth}, scale={scale}, rows={sum(1 for t,s in enumerate(flow.rows) for node in s if p.role(depth,flow.nodes[node][0],t) in {'mid','botDesc','topRise'})}, unique senders={len(seen)}")
    print(f"failures={dict(failed)}")
    print(f"failure examples={failure_examples}")
    if worst:
        score,mm,n,a,pi,role,t,lev,prof=worst
        print(f"worst mismatch/n={score} ({mm}/{n}), t={t}, i={lev}, role={role}, a={a}, up={pi}, profile={prof}")
    if min_fringe:
        fmin,n,a,pi,role,t,lev,prof=min_fringe
        print(f"minimum fringe={fmin}, n={n}, t={t}, i={lev}, role={role}, a={a}, up={pi}, profile={prof}")
    if min_columns_seen:
        n,a,pi,role,t,lev,prof=min_columns_seen
        print(f"minimum columns={n}, t={t}, i={lev}, role={role}, a={a}, up={pi}, profile={prof}")
    print(f"distinct fringe minima={len(min_columns_for_fringe)}; minimum column counts by small fringe minimum=" + str({f:v[0] for f,v in sorted(min_columns_for_fringe.items()) if f<=20}))
    iv.dps=50
    E1,d,lam=Fraction(371,10**8),Fraction(11,2500),Fraction(1)
    K=lam*d/2-lam**2*(Fraction(1,2)+2*lam/9)*E1
    mK=iv.mpf(rows*K.numerator)/K.denominator
    logstates=iv.log(iv.mpf(2*(rows+1)))
    logfail=16*(logstates-mK)
    print(f"relaxed B2 screen: d={d}, leakage={d/2}, epsB={Fraction(17,2000)}, "
          f"geometry allowance={(Fraction(17,2000)-d)/2}; "
          f"at n=16 log fail fraction in [{float(logfail.a):.3f},{float(logfail.b):.3f}]")
    print("Finite screen only; no provider or sorting claim.")


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=30)
    ap.add_argument('--scale',type=int,default=8192)
    ap.add_argument('--min-columns',type=int,default=1)
    ap.add_argument('--min-time',type=int,default=0)
    ap.add_argument('--allocation',choices=('equalized','waterfill'),default='equalized')
    ap.add_argument('--tail',type=int,default=13)
    args=ap.parse_args()
    run(args.depth,args.scale,args.min_columns,min_time=args.min_time,
        allocation=args.allocation,tail=args.tail)
