#!/usr/bin/env python3
"""Coarse transition box (INDUCTION-v6.md sec. 13). Merge the TRANS_ANALYTIC tags of a width_sim dump
into a few groups and solve the merged box exactly (Fractions, inputs rounded up). The groups are the
structural classes of the two lemmas: E = far-charged end children, En = near-charged end children
(sparse at their next send, a/c <= 2^-2.5), I = interior/spilled, T = topRise."""
import json
import math
import sys
from fractions import Fraction as Fr

D = json.load(open(sys.argv[1]))
up = lambda x: Fr(math.ceil(Fr(x) * 10 ** 12), 10 ** 12)
mu = Fr(D["mu"])
R = Fr(D["round"])

def grp(tag):
    if tag == "topRise":
        return "T"
    kind = tag.split("|")[1] if "|" in tag else "E"
    if kind == "En":
        return "En"
    if kind in ("I", "S"):
        return "I"
    return "E"

G = {}
for tg, td in D["tags"].items():
    g = G.setdefault(grp(tg), dict(rf=Fr(0), e=Fr(0), D=Fr(0), members=[]))
    for k_ in ("rf", "e", "D"):
        g[k_] = max(g[k_], up(td[k_]))
    g["members"].append(tg)
T = {}
for pt, tg, cf, lc in D["trans"]:
    key = (grp(pt), grp(tg))
    c0, l0 = T.get(key, (Fr(0), Fr(0)))
    T[key] = (max(c0, up(cf)), max(l0, up(lc)))
hw = {g: 10 * mu for g in G}
for _ in range(300):
    new = {g: max([mu / 2 + cf * hw[p] + lc for (p, q), (cf, lc) in T.items() if q == g] or [mu / 2]) for g in G}
    hw = {g: Fr(math.ceil(min(new[g], hw[g]) * 10 ** 15), 10 ** 15) for g in G}
ok = all(max([mu / 2 + cf * hw[p] + lc for (p, q), (cf, lc) in T.items() if q == g] or [mu / 2]) <= hw[g] for g in G)
worst = Fr(0)
for g, d in sorted(G.items()):
    rb = hw[g] * d["rf"] + d["D"] + d["e"] + R
    worst = max(worst, rb)
    print("group %-3s (%2d tags) hw <= %.4f mu  e_max %.4f  ratio <= %.6f" % (g, len(d["members"]), float(hw[g] / mu), float(d["e"]), float(rb)))
for (p, q), (cf, lc) in sorted(T.items()):
    print("   %-3s -> %-3s coef %.4f loc/mu %.4f" % (p, q, float(cf), float(lc / mu)))
print("post-fixed point:", ok, "  worst ratio bound:", float(worst), " < 1:", worst < 1)
