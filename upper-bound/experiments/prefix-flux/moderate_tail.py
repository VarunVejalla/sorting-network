#!/usr/bin/env python3
"""Moderate-rank first-round tail: analytical entropy envelope, float screening.

Every chosen theta,tangent point gives a paper upper bound; optimization is
not trusted or needed for validity. Outward intervals check its numerical value.
No all-input sorting or coefficient claim follows from this local screen.
"""
import json
import math
from pathlib import Path
from scipy.optimize import minimize
from fractions import Fraction as F
from mpmath import iv


def envelope(i,f,n,m,theta,p0,eta=1/1000,baseline_factor=1):
    g=(i+1)*math.log1p(i)-i*math.log(i)
    overhead=math.log(2*m*baseline_factor*(n-1)/eta)/n
    u=math.expm1(theta)
    slope=i*u/(1+u*p0)
    intercept=i*math.log1p(u*p0)-slope*p0
    z=slope-f*theta
    logsum=max(0,z)+math.log1p(math.exp(-abs(z)))
    return (g+overhead+intercept+logsum)/theta


def bound(i,f,n,m,baseline_factor=1):
    """Return float upper envelope at a fixed rounded rational witness."""
    def fun(v):
        return envelope(i,f,n,m,math.exp(v[0]),v[1],baseline_factor=baseline_factor)
    def jac(v):
        theta=math.exp(v[0]); p0=v[1]
        u=math.expm1(theta); exp_theta=u+1; denom=1+u*p0
        slope=i*u/denom
        intercept=i*math.log1p(u*p0)-slope*p0
        z=slope-f*theta
        if z >= 0:
            sigmoid=1/(1+math.exp(-z))
        else:
            ez=math.exp(z); sigmoid=ez/(1+ez)
        g=(i+1)*math.log1p(i)-i*math.log(i)
        overhead=math.log(2*m*baseline_factor*(n-1)/0.001)/n
        total=g+overhead+intercept+math.log1p(math.exp(-abs(z)))+max(0,z)
        d_slope_theta=i*exp_theta/(denom*denom)
        d_slope_p=-i*u*u/(denom*denom)
        d_intercept_theta=i*p0*p0*u*exp_theta/(denom*denom)
        d_intercept_p=i*u*u*p0/(denom*denom)
        d_total_theta=d_intercept_theta+sigmoid*(d_slope_theta-f)
        d_total_p=d_intercept_p+sigmoid*d_slope_p
        return ((d_total_theta*theta-total)/theta,
                d_total_p/theta)
    candidates=[minimize(fun,[math.log(t),p],method='L-BFGS-B',
                        jac=jac,bounds=[(-9,3),(0,1)])
                for t,p in [(0.2,0.1),(0.7,0.3),(2,0.01)]]
    result=min(candidates,key=lambda r:r.fun)
    denom=2**20
    th=max(1,round(math.exp(result.x[0])*denom))/denom
    p0=min(1,max(0,round(result.x[1]*denom)/denom))
    return envelope(i,f,n,m,th,p0,baseline_factor=baseline_factor),th,p0


def interval_envelope(i,f,n,m,theta,p0,baseline_factor=1):
    """Outward interval evaluation at fixed dyadic parameters, eta=1/1000."""
    iv.dps=50
    def exact_float(x):
        num,den=x.as_integer_ratio()
        return iv.mpf(num)/den
    th,pt=exact_float(theta),exact_float(p0)
    g=(i+1)*iv.log(i+1)-i*iv.log(i)
    overhead=iv.log(2000*m*baseline_factor*(n-1))/n
    u=iv.exp(th)-1
    slope=i*u/(1+u*pt)
    intercept=i*iv.log(1+u*pt)-slope*pt
    value=(g+overhead+intercept+iv.log(1+iv.exp(slope-f*th)))/th
    # Convert the outward upper dyadic endpoint to an exact Fraction.
    sign,mantissa,exponent,_=value._mpi_[1]
    upper=F((-1)**sign*mantissa)*F(2)**exponent
    return upper


def ragged(a,h,marks,q=12):
    n=(a+2**q-1)//2**q
    L,remainder=divmod(a,n)
    assert L+bool(remainder)<=2**q
    b=L//2
    f=h//n
    assert f<=b and n>=2 and marks>0
    i=min(L,(marks+n-1)//n)
    percol,th,p0=bound(i,f,n,L)
    upper=interval_envelope(i,f,n,L,th,p0)
    extra=min(remainder,marks//(b+1)) if remainder else 0
    return dict(n=n,L=L,remainder=remainder,f=f,i=i,
                bound=min(marks,n*percol+extra),theta=th,p0=p0,extra=extra,
                integer_bound=min(marks,math.floor(n*upper)+extra))


if __name__=='__main__':
    data=json.loads(Path(__file__).with_name('frontier-witness.json').read_text())
    print('LOCAL TAIL SCREEN; optimized dyadics, outward interval evaluation; not Lean')
    print('Common probability budget eta=.001; no union over fringe widths needed.')
    for v in data['result']['trace']:
        a,H,h=v['a'],v['zeros'],v['pi']//2
        if h==0:
            continue
        marks=min(H,a-H)
        result=ragged(a,h,marks)
        actual=(H-v['ys'][1] if H<=a-H else
                a-H-(h-(H-v['ys'][-2])))
        print(f"t{v['t']} node{v['node']} minority={marks}, coarse escape={actual}; "
              f"new float bound={result['bound']:.3f}, "
              f"interval-checked integer bound<={result['integer_bound']}, "
              f"n={result['n']} L={result['L']} f={result['f']} "
              f"extra<={result['extra']}")
