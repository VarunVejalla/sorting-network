#!/usr/bin/env python3
"""Exact flow simulation of the sided, centred design (INDUCTION.md; REVIEW-centring.md items 2 and 4).

Schedule and roles: Chvatal's (../slackfree/flowsim.py), as in ../../best/notes/sub800/designP_sim.py.
Per node class: deficit G = R - W split as G = G_L + G_H (low / high ancestral-side deficits).
Design C (mid, botDesc, topRise senders; topDesc: theta = 0; botRise: no blocks):
  theta_first = pi/2 + G_L + o,  theta_last = pi/2 + G_H - o,  interior theta = 0,
  first child (G_L', G_H') = (theta_first, 0), last child = (0, theta_last), interior (0, 0);
  sender afterwards: G_L += pi/2, G_H += pi/2.
  o = OFRAC * c (design constant per capacity; default the centred w/2 ~ mu A nu / (2 (A nu - 1))).
Records, per role: negative blocks, max a/c (eta), max G/c, and the crossing-distance margin
  min (X_1 - pi/2)/a  with X_1 = G_first_child - G_L(sender)  (own child-1 keys held; REVIEW issue 1 needs
  X_1 - pi/2 to be a sizeable fraction of a so that the F1|B1 crossings that matter are far in rank).
Usage:  python -I centred_sim.py X Y Z D [D ...]     (env OFRAC to override o/c)
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "slackfree"))
from flowsim import Par  # noqa: E402

sys.setrecursionlimit(10000)
SPILL = os.environ.get('SPILL', '0') == '1'


class Cls:
    __slots__ = ("lev", "G", "GL", "kids")

    def __init__(s, lev, G, GL, kids):
        s.lev, s.G, s.GL, s.kids = lev, Fr(G), Fr(GL), kids


class Sim:
    def __init__(s, P, d, ofrac):
        s.P, s.d, s.k, s.ofrac = P, d, P.k, ofrac
        s.R = [s.k ** (d - i) for i in range(d + 1)]
        s.intern = {}
        s.stats = {}

    def note(s, role, key, val, better):
        r = s.stats.setdefault(role, {})
        if key not in r or better(val, r[key][0]):
            r[key] = (val, (s.t,))

    def mk(s, lev, G, GL, kids):
        key = (lev, G, GL, tuple((id(c), n) for c, n in kids))
        c = s.intern.get(key)
        if c is None:
            c = Cls(lev, G, GL, tuple(kids))
            s.intern[key] = c
        return c

    def initial(s):
        c = None
        for i in range(s.d, -1, -1):
            kids = () if c is None else ((c, s.k),)
            G = 0 if i == 0 else s.R[i]
            c = s.mk(i, G, Fr(G, 2), kids)
        return c

    def active(s, i):
        return (i == 0) if s.t == 0 else s.P.active(s.d, i, s.t)

    def step(s, root, t):
        s.t, s.memo_a, s.memo_i = t, {}, {}
        return s.visit(root, None, None)

    def visit(s, c, newG, newGL):
        if s.active(c.lev):
            if id(c) not in s.memo_a:
                s.memo_a[id(c)] = s.send(c)
            return s.memo_a[id(c)]
        key = (id(c), newG, newGL)
        if key not in s.memo_i:
            G = c.G if newG is None else newG
            GL = c.GL if newGL is None else newGL
            kids = tuple((s.visit(kc, None, None), n) for kc, n in c.kids)
            s.memo_i[key] = s.mk(c.lev, G, GL, kids)
        return s.memo_i[key]

    def send(s, c):
        P, d, t, k = s.P, s.d, s.t, s.k
        i = c.lev
        role = "topDesc" if t == 0 else P.role(d, i, t)
        a = sum(kc.G * n for kc, n in c.kids) - c.G if c.kids else s.R[i] - c.G
        cap = P.cap(d, i, t)
        pi = a if role == "botRise" else (Fr(0) if t == 0 else P.up(d, i, t))
        GL, GH = c.GL, c.G - c.GL
        if role == "botRise" or not c.kids:
            kids = tuple((s.visit(kc, None, None), n) for kc, n in c.kids)
            return s.mk(i, c.G + pi, GL + pi / 2, kids)
        flat = [[kc, n] for kc, n in c.kids]
        first, last = flat[0][0], flat[-1][0]
        if role == "topDesc":
            thetas = [(kc, n, Fr(0), Fr(0)) for kc, n in flat]
        else:
            o = s.ofrac * cap
            tf = pi / 2 + GL + o
            tl = pi / 2 + GH - o
            mid = []
            for idx, (kc, n) in enumerate(flat):
                cnt = n - (1 if idx == 0 else 0) - (1 if idx == len(flat) - 1 else 0)
                mid += [(kc, 1, Fr(0), Fr(0))] * cnt
            thetas = [(first, 1, tf, tf)] + mid + [(last, 1, tl, Fr(0))]
            if SPILL:
                # spill rule: low deficit fills children from the low end, high deficit from the high end,
                # each child's theta capped at its own deficit G (its keys held outside its subtree + here)
                seq = [first] + [m_[0] for m_ in mid] + [last]
                caps = [kc.G for kc in seq]
                th = [Fr(0)] * len(seq)
                low, high = tf, tl
                for j in range(len(seq)):
                    take = min(low, caps[j]); th[j] += take; low -= take
                    if low == 0:
                        break
                for j in range(len(seq) - 1, -1, -1):
                    take = min(high, caps[j] - th[j]); th[j] += take; high -= take
                    if high == 0:
                        break
                assert low == 0 and high == 0, (t, i, role)
                spilled = sum(1 for j in range(1, len(seq) - 1) if th[j] > 0)
                if spilled:
                    s.note(role, "spill_children_max", spilled, lambda v, w: v > w)
                    s.note(role, "spill_a_over_c_max", a / cap, lambda v, w: v > w)
                thetas = [(seq[j], 1, th[j], th[j] if j < len(seq) // 2 else Fr(0)) for j in range(len(seq))]
            if t >= 1:
                X1 = first.G - GL
                s.note(role, "cross_margin_min", (X1 - pi / 2) / a, lambda v, w: v < w)
        T = Fr(0)
        newkids = []
        for kc, n, th, thL in thetas:
            b = kc.G - th
            if b < 0:
                s.note(role, "neg_block_min", b / cap, lambda v, w: v < w)
            T += n * th
            newkids.append((s.visit(kc, th, thL), n))
        assert T == pi + c.G or role == "topDesc"
        if t >= 1:
            s.note(role, "a_over_c_max", a / cap, lambda v, w: v > w)
            s.note(role, "G_over_c_max", c.G / cap, lambda v, w: v > w)
        merged = []
        for kc, n in newkids:
            if merged and merged[-1][0] is kc:
                merged[-1] = (kc, merged[-1][1] + n)
            else:
                merged.append((kc, n))
        return s.mk(i, c.G + pi, GL + pi / 2, tuple(merged))


def main():
    x, y, z = map(int, sys.argv[1:4])
    k, A, nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
    Anu = A * nu
    dF = Fr(1, 8)
    mu = (1 - Fr(1, 1024)) * min(nu / (A * k * k), dF * (Anu * k - 1) / (2 * A * A * k * k))
    ofrac = Fr(os.environ["OFRAC"]) if "OFRAC" in os.environ else mu * Anu / (2 * (Anu - 1))
    for d in map(int, sys.argv[4:]):
        P = Par(x, y, z)
        S = Sim(P, d, ofrac)
        root = S.initial()
        for t in range(P.tf(d)):
            root = S.step(root, t)
        print(f"({x},{y},{z}) d={d} tf={P.tf(d)} o/c={float(ofrac):.3e} classes={len(S.intern)}")
        for role, r in sorted(S.stats.items()):
            print("   %-8s %s" % (role, {kk: (round(float(v[0]), 6), v[1]) for kk, v in r.items()}))


if __name__ == "__main__":
    main()
