#!/usr/bin/env python3
"""Exact evaluation of the transition box (INDUCTION-v6.md sec. 12) from a dump of width_sim.py
(TRANS_DUMP). Every recorded float (coefficients, local terms, per-tag ratio factors) is rounded UP to a
rational on a 1e-12 grid; the box recursion hw[q] = max_{p->q} (mu/2 + coef hw[p] + loc) is iterated in
Fractions from hw = mu/2 to a fixed point (monotone; each coef < 1 so it converges; we iterate until an
exact fixed point or a certified upper bound: hw_{k+1} <= hw_k). Prints the exact worst ratio bound."""
import json
import math
import sys
from fractions import Fraction as Fr

D = json.load(open(sys.argv[1]))
up = lambda x: Fr(math.ceil(Fr(x) * 10 ** 12), 10 ** 12)
mu = Fr(D["mu"]).limit_denominator(10 ** 15)
mu = Fr(math.ceil(mu * 10 ** 15), 10 ** 15)
R = Fr(D["round"])
tags = D["tags"]
trans = [(pt, tg, up(cf), up(lc)) for pt, tg, cf, lc in D["trans"]]
# upper bound: iterate from a large start downward (monotone operator) to a post-fixed point
hw = {tg: 10 * mu for tg in tags}
for it in range(400):
    new = {}
    for tg in tags:
        vals = [mu / 2 + cf * hw.get(pt, 10 * mu) + lc for pt, q, cf, lc in trans if q == tg]
        new[tg] = max(vals) if vals else mu / 2
    if all(new[tg] <= hw[tg] for tg in tags):
        hw = {tg: Fr(math.ceil(new[tg] * 10 ** 15), 10 ** 15) for tg in tags}   # round up, still post-fixed
    else:
        hw = new
worst = Fr(0)
for tg, td in sorted(tags.items()):
    rb = hw[tg] * up(td["rf"]) + up(td["D"]) + up(td["e"]) + R
    worst = max(worst, rb)
    print("%-10s hw <= %.6f mu   ratio <= %.6f" % (tg, float(hw[tg] / mu), float(rb)))
# verify post-fixed point: T(hw) <= hw for every tag (so hw bounds the least fixed point)
ok = all(max([mu / 2 + cf * hw.get(pt, 10 * mu) + lc for pt, q, cf, lc in trans if q == tg] or [mu / 2]) <= hw[tg] for tg in tags)
print("post-fixed point verified:", ok)
print("exact worst ratio bound:", float(worst), "  < 1:", worst < 1)
