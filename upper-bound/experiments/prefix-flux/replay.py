#!/usr/bin/env python3
"""Replay stored integer decisions, without running an optimization solver.

This shares the flow/bounds code with oracle.py and is not an independent
implementation. It checks every port and, in monotone mode, every input prefix.
"""
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from oracle import Par,build_table,run

data=json.loads(Path(sys.argv[1]).read_text(encoding='utf8'))
c=data['config']; p=Par(2,3,2)
table,_,_=build_table(p,c['depth'],'D2')
choices={(v['t'],tuple(v['node'])):v['ys'] for v in data['result']['trace']}
assert len(choices)==len(data['result']['trace'])
result=run(table,p,c['depth'],data['threshold'],c['exact_cap'],F(c['eps_b']),
           F(c['eps_f']),F(c['delta_f']),monotone=c.get('monotone',False),
           replay=choices,exact_root=not c.get('approx_root',False))
for key in ('terminal_L1','wrong_bags','nonideal_choices','failures'):
    # JSON converts node tuples to lists.
    assert json.loads(json.dumps(result[key]))==data['result'][key],key
print(f"REPLAY OK: {len(choices)} decisions; terminal L1={result['terminal_L1']}; "
      f"monotone={c.get('monotone',False)}; no LP calls")
