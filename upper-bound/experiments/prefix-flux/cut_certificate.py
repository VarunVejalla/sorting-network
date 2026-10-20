#!/usr/bin/env python3
"""Exact capacity obstruction and early-table scaling checks; not Lean."""
import json
from fractions import Fraction as F
from pathlib import Path
from oracle import Par,build_table

data=json.loads(Path(__file__).with_name('frontier-witness.json').read_text())
v=next(v for v in data['result']['trace'] if v['t']==5 and v['node']==[3,17])
last_child_ones=v['ends'][5]-v['ends'][4]-(v['ys'][5]-v['ys'][4])
assert last_child_ones==678
assert sum(v['capacity']-v['actual'] for v in data['result']['failures']
           if v['node'][0]>=3 and v['node'][1]//4**(v['node'][0]-3)==17)==440
q=data['threshold']; p=Par(2,3,2)
assert [(t,p.up(12,3,t)) for t in range(7,p.tf(12),2)
        if p.active(12,3,t) and p.up(12,3,t)]==[(7,448),(9,28)]
assert 18*4**9<q  # native subtree17 must contain only zeros
base,_,_=build_table(p,12,'D2',horizon=6)
for r in range(13):
    d=12+r; scale=4**r
    table,_,_=build_table(p,d,'D2',horizon=6)
    assert [set(s) for s in table]==[set(s) for s in base]
    for step,original in zip(table,base):
        for lev,rows in step.items():
            for (a,pi,blocks),(aa,pp,bb) in zip(rows,original[lev]):
                assert (a,pi,blocks)==(aa*scale,pp*scale,[b*scale for b in bb])
    # Schedule-only future cut bound; it does not depend on descendant colors.
    for t in range(7,p.tf(d),2):
        if not p.active(d,3,t):
            continue
        assert p.role(d,3,t)!='botRise'
        assert p.up(d,3,t)<=p.cap(d,3,t)/128
        assert p.cap(d,3,t)==65536*scale*F(1,16)**((t-7)//2)
future=512/(1-F(1,16))
assert future==F(8192,15)<last_child_ones
print(f'CUT CERTIFICATE: 678*S wrong ones; future escape <= {future}*S; '
      f'trapped >= {last_child_ones-future}*S')
print('Early D2 scaling checked exactly for d12..24; future roles/capacities checked on those schedules.')
print('Uniform extension uses the displayed geometric formulas; this is not a kernel-checked theorem.')
