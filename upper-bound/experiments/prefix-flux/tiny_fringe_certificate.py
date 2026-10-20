#!/usr/bin/env python3
"""Reviewed F2 probability-envelope check, pending current-API guard extension."""
from fractions import Fraction as F
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'walk-bound'))
from fringe_cert_v2 import certify

args=(13,5,11,F(1,2),5,17,F(1,10**100))
old=certify(*args)
new=certify(*args,exact_small=True)
assert not old['ok'] and new['ok'] and new['exact_ok'] and new['closed_ok']
assert not new['current_hf16']
print('INTERVAL CHECK: f13, g1=5, g2=11, c=1/2, b=5, J17, delta=10^-100')
print('Old relaxed E2 bound fails; exact ceil(2c) passes per-E and closed routes.')
print('Supported rank fraction is extremely small; this is not a global coefficient.')
print('Current Lean hf16 guard FAILS; reviewed zero/nonzero-jmax extension is not formalized.')
