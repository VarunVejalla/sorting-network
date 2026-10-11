#!/usr/bin/env python3
"""Exact k = 64 flow tables by hash-consing node classes (nodes whose whole subtree state is equal
share a class).  Designs 'U' (Chvatal) and 'D2' (cut layout, see explicit.py).  Exact integers.

Per sending class we record a, pi, the run-length block list, G, and check: integrality, b >= 0,
conservation (sum b = a - pi, global wire count = N), a/c, G/c (one-sided residual is
(k-1)/k * G at most), and the separator geometry: does some n | gcd(pi/2, all b_l) give
m = a/n in the window (2^L, 2^(L+1)] (only for a > 2^63; smaller nodes use one sorter)?
"""
import sys, math
from fractions import Fraction as Fr
from flowsim import Par

sys.setrecursionlimit(10000)


class Cls:
    __slots__ = ('lev', 'G', 'gL', 'gH', 'kids', 'id')

    def __init__(s, lev, G, gL, gH, kids):
        s.lev, s.G, s.gL, s.gH, s.kids = lev, G, gL, gH, kids  # kids: tuple of (Cls, count)


class Sim:
    def __init__(s, P, d, design, L=42):
        s.P, s.d, s.design, s.L = P, d, design, L
        s.k = P.k
        s.R = [s.k ** (d - i) for i in range(d + 1)]
        s.table = {}
        s.intern = {}
        s.nid = 0
        s.stats = dict(neg=0, nonint=0, oddpi=0, cons=0, geom_bad=0, senders=0, maxclasses=0)
        s.worst = dict(ac=Fr(0), G=Fr(0), res=Fr(0))
        s.geom_examples = []

    def mk(s, lev, G, gL, gH, kids):
        key = (lev, G, gL, gH, tuple((id(c), n) for c, n in kids))
        c = s.intern.get(key)
        if c is None:
            c = Cls(lev, G, gL, gH, tuple(kids))
            c.id = s.nid
            s.nid += 1
            s.intern[key] = c
        return c

    def initial(s):
        c = None
        for i in range(s.d, -1, -1):
            kids = () if c is None else ((c, s.k),)
            G = 0 if i == 0 else s.R[i]
            c = s.mk(i, G, 0 if i == 0 else 0, 0 if i == 0 else G, kids)
        return c

    # ---- one stage t -> t+1 -------------------------------------------------------------
    def step(s, root, t):
        s.memo_a, s.memo_i = {}, {}
        s.t = t
        s.alog = {}
        # multiplicities of the current classes
        mult = {id(root): 1}
        order = [root]
        seen = {id(root)}
        j = 0
        while j < len(order):
            c = order[j]; j += 1
            for kc, n in c.kids:
                mult[id(kc)] = mult.get(id(kc), 0) + mult[id(c)] * n
                if id(kc) not in seen:
                    seen.add(id(kc)); order.append(kc)
        # NB: classes are shared across different parents; mult accumulates correctly only if
        # parents are processed before children (BFS by level guarantees it: kids are one level down)
        r = s.visit(root, None)
        tot = sum(mult[cid] * a for cid, a in s.alog.items())
        if tot != s.k ** s.d:
            s.stats['cons'] += 1
        return r

    def active(s, i):
        return (i == 0) if s.t == 0 else s.P.active(s.d, i, s.t)

    def visit(s, c, recv):
        """recv = None (parent not sending) or (b, gL, gH) for this node."""
        if s.active(c.lev):
            assert recv is None
            key = id(c)
            if key not in s.memo_a:
                s.memo_a[key] = s.send(c)
            new, a = s.memo_a[key]
            return new
        key = (id(c), recv)
        if key not in s.memo_i:
            G, gL, gH = c.G, c.gL, c.gH
            if recv is not None:
                b, gL, gH = recv
                G = gL + gH
            kids = tuple((s.visit(kc, None), n) for kc, n in c.kids)
            s.memo_i[key] = s.mk(c.lev, G, gL, gH, kids)
        return s.memo_i[key]

    def send(s, c):
        P, d, t, k = s.P, s.d, s.t, s.k
        i = c.lev
        role = 'topDesc' if t == 0 else P.role(d, i, t)
        U = [(kc.G, n, kc) for kc, n in c.kids]
        a = sum(u * n for u, n, _ in U) - c.G if c.kids else s.R[i] - c.G
        s.alog[id(c)] = a
        if s.design == 'U' and t >= 1 and a != P.alloc(d, i, t):
            s.stats['alloc_mismatch'] = s.stats.get('alloc_mismatch', 0) + 1
        cap = P.cap(d, i, t)
        if role == 'botRise':
            pi = a
        elif t == 0:
            pi = 0
        else:
            pi = P.up(d, i, t)
            if pi.denominator != 1:
                s.stats['nonint'] += 1
            pi = int(pi)
            if pi % 2:
                s.stats['oddpi'] += 1
        newkids = []
        blocks = []
        if role == 'botRise' or not c.kids:
            newkids = [(s.visit(kc, None), n) for kc, n in c.kids]
        else:
            if role == 'topDesc':
                lo, hi = 0, None
            elif s.design == 'D2':
                S = sum(u * n for u, n, _ in U)
                lo, hi = c.gL + pi // 2, S - c.gH - pi // 2
            pos = 0
            for u, n, kc in U:
                if role != 'topDesc' and s.design == 'U':
                    beta = P.down(d, i, t)
                    if beta.denominator != 1:
                        s.stats['nonint'] += 1
                    beta = int(beta)
                    th = u - beta
                    if th < 0 or beta < 0:
                        s.stats['neg'] += 1
                    newkids.append((s.visit(kc, (beta, th, 0)), n))
                    blocks.append((beta, n))
                    pos += u * n
                    continue
                if role == 'topDesc':
                    newkids.append((s.visit(kc, (u, 0, 0)), n))
                    blocks.append((u, n))
                    pos += u * n
                    continue
                # cut layout over a run of n identical kids of size u starting at pos
                q = 0
                while q < n:
                    s0 = pos + q * u
                    s1 = s0 + u
                    # how many consecutive kids from q have the same (b,cl,ch)?
                    b = max(0, min(s1, hi) - max(s0, lo))
                    cl = max(0, min(s1, lo) - s0)
                    ch = max(0, s1 - max(s0, hi))
                    if u > 0 and s1 <= lo:
                        run = min(n - q, max(1, (lo - s0) // u))
                    elif u > 0 and s0 >= lo and s1 <= hi:
                        run = min(n - q, max(1, (hi - s0) // u))
                    elif u > 0 and s0 >= hi:
                        run = n - q
                    else:
                        run = 1 if u > 0 else n - q
                    newkids.append((s.visit(kc, (b, cl, ch)), run))
                    blocks.append((b, run))
                    q += run
                pos += u * n
            sb = sum(b * n for b, n in blocks)
            if sb != a - pi:
                s.stats['cons'] += 1
            if any(b < 0 for b, _ in blocks):
                s.stats['neg'] += 1
        G2 = c.G + pi
        new = s.mk(i, G2, c.gL + pi // 2, c.gH + pi - pi // 2, tuple(newkids))
        if t >= 2 and role not in ('topDesc', 'botRise') and c.kids:
            s.stats['senders'] += 1
            s.worst['ac'] = max(s.worst['ac'], Fr(a) / cap)
            s.worst['G'] = max(s.worst['G'], Fr(c.G) / cap)
            if a > 2 ** 63:
                g = pi // 2
                for b, _ in blocks:
                    g = math.gcd(g, b)
                if not s.geom_ok(a, g):
                    s.stats['geom_bad'] += 1
                    if len(s.geom_examples) < 3:
                        s.geom_examples.append((t, i, role, a, g, a // g if g else None))
        return new, a

    def geom_ok(s, a, g):
        if g == 0:
            return False
        lo, hi = 2 ** s.L, 2 ** (s.L + 1)
        # need n | g, n | a with lo < a/n <= hi
        g2 = math.gcd(g, a)
        o = g2
        v = 0
        while o % 2 == 0:
            o //= 2
            v += 1
        odd_divs = [dv for dv in range(1, min(o, 10 ** 5) + 1) if o % dv == 0] if o < 10 ** 10 else [1, o]
        for od in odd_divs:
            for j in range(v + 1):
                n = od * 2 ** j
                m = a // n
                if lo < m <= hi:
                    return True
        return False


def self_mult_dummy(x):
    return x


def run(P, d, design, L=42):
    S = Sim(P, d, design, L)
    root = S.initial()
    # count wires properly: total over all nodes = N  (needs multiplicities) -> separate pass
    TF = P.tf(d)
    nclasses = []
    for t in range(TF):
        root = S.step(root, t)
        nclasses.append(len(S.memo_a) + len(S.memo_i))
    S.stats['maxclasses'] = max(nclasses)
    return S


if __name__ == '__main__':
    x, y, z = map(int, sys.argv[1:4])
    lean7 = (x, y, z) == (6, 12, 6)
    P = Par(x, y, z, lean7=lean7)
    for d in map(int, sys.argv[4:]):
        for des in ('U', 'D2'):
            S = run(P, d, des)
            st = S.stats
            print(f'({x},{y},{z}) d={d} tf={P.tf(d)} {des}: {st} max a/c={float(S.worst["ac"]):.6f} '
                  f'max G/c={float(S.worst["G"]):.3e} geom_bad_examples={S.geom_examples[:2]}')
            sys.stdout.flush()
