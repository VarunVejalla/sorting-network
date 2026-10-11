#!/usr/bin/env python3
"""Exact flow-table simulator for Chvatal's tree (DCS-TR-294 Sec. 3), uniform and non-uniform blocks.

Everything is exact (Python ints / Fractions).  Parameters k = 2^x, A = 2^y, nu = 2^-z.

State variable: for every node y and time t, the *deficit*
    G_y(t) = R_y - W_y(t),   R_y = k^(d - level(y)) (keys addressed below y),
                             W_y(t) = wires located in subtree(y) at time t.
Identities used (all exact):
    a_x(t)      = sum_children G_l(t) - G_x(t)              (wires in x)
    U_l(t)      = G_l(t)          for a child l of an active x (Lemma 3.1 / 4.1 upper count)
    b_l         = U_l - theta_l   (wires x sends to child l)
    G_l(t+1)    = theta_l,  G_x(t+1) = G_x(t) + pi_x       (sum_l theta_l = pi_x + G_x)
Design = rule for theta_l.  'U' = Chvatal (b_l = beta(i,t) for every child), 'D2' = two-sided
non-uniform design (theta = pi/2 + G_x on the end child on x's run side, pi/2 on the other end,
0 on interior children), 'P' = optimal one-sided design (theta_end = pi/2 + G - r c,
theta_int = (2 r c - G)/(k-2), r = (k-1)/(2 A^2 k^2)) -- P is not type-closed, so it is only
run on the explicit small-k tree.
"""
from fractions import Fraction as Fr
import math, sys


class Par:
    def __init__(s, x, y, z, lean7=False):
        s.x, s.y, s.z = x, y, z
        s.k, s.A, s.nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
        s.lean7 = lean7   # use the Lean Schedule7 closed forms (only for (6,12,6))

    def cap(s, d, i, t):
        N = s.k ** d
        return Fr(N) * s.A ** i * s.nu ** t / (s.A * s.nu * s.k)

    # ---- schedule (Chvatal p. 6-7) ----
    def alpha(s, d, t):
        if t == 0:
            return 0
        if t == 1:
            return 1
        if s.lean7:
            lo = 0 if t + 5 <= d else (t + 6 - d) // 2
        else:
            # alpha*(t) = (t lg(1/nu) - lg N + lg(2 A k^3 nu))/lg A  (c(alpha,t) >= 2k^2)
            num = t * s.z - d * s.x + 1 + 3 * s.x + s.y - s.z
            lo = max(0, -((-num) // s.y))
        return lo if lo % 2 == t % 2 else lo + 1

    def omega(s, d, t):
        if t == 0:
            return 0
        if t == 1:
            return 1
        if s.lean7:
            lo = (t + 4) // 3
        else:
            num = t * s.z + s.x + s.y - s.z   # omega*(t) = (t lg(1/nu) + lg(A nu k))/lg(Ak)
            lo = -((-num) // (s.x + s.y))
        return lo if lo % 2 == t % 2 else lo + 1

    def tf(s, d):
        if not hasattr(s, '_tf'):
            s._tf = {}
        if d not in s._tf:
            s._tf[d] = s._tf_(d)
        return s._tf[d]

    def _tf_(s, d):
        if s.lean7:
            return 3 * d - 20
        t = 2
        while s.alpha(d, t) < s.omega(d, t):
            t += 1
        return t

    def active(s, d, i, t):
        return (t <= s.tf(d) and s.alpha(d, t) <= i <= s.omega(d, t) and i % 2 == t % 2)

    # ---- Chvatal's uniform closed forms (Lean FlowTable for (6,12,6)) ----
    def alloc(s, d, i, t):
        if t == 0:
            return Fr(s.k ** d) if i == 0 else Fr(0)
        if not s.active(d, i, t):
            return Fr(0)
        c = s.cap(d, i, t)
        Q = s.A ** 2 * s.k ** 2
        if i == s.alpha(d, t):
            return c
        if i == s.omega(d, t):
            return Fr(s.k ** d, s.k ** i) - c / Q
        return (1 - Fr(1, Q)) * c

    def role(s, d, i, t):
        a0, a1 = s.alpha(d, t), s.alpha(d, t + 1)
        w0, w1 = s.omega(d, t), s.omega(d, t + 1)
        if i == a0:
            return 'topDesc' if a0 < a1 else 'topRise'
        if i == w0:
            return 'botDesc' if w0 < w1 else 'botRise'
        return 'mid'

    def up(s, d, i, t, a=None):
        if t == 0:
            return Fr(0)
        if not s.active(d, i, t):
            return Fr(0)
        c = s.cap(d, i, t)
        Q = s.A ** 2 * s.k ** 2
        r = s.role(d, i, t)
        if r == 'topDesc':
            return Fr(0)
        if r == 'topRise':
            return s.nu * c / (s.A * s.k)
        if r == 'botRise':
            return s.alloc(d, i, t) if a is None else a
        return (s.A * s.nu * s.k - 1) * c / Q

    def down(s, d, i, t):
        if t == 0:
            return Fr(s.k ** (d - 1)) if i == 0 else Fr(0)
        if not s.active(d, i, t):
            return Fr(0)
        c = s.cap(d, i, t)
        r = s.role(d, i, t)
        if r == 'topDesc':
            return c / s.k
        if r == 'botDesc':
            return s.alloc(d, i + 1, t + 1)
        if r == 'botRise':
            return Fr(0)
        return (s.A * s.k - s.nu) * c / (s.A * s.k ** 2)


def verify_lean_dump(path):
    P = Par(6, 12, 6, lean7=True)
    bad = n = 0
    for line in open(path):
        p = line.split()
        if len(p) != 6:
            continue
        d, t, i, a, u, b = map(int, p)
        n += 1
        got = (P.alloc(d, i, t), P.up(d, i, t), P.down(d, i, t))
        if got != (a, u, b):
            bad += 1
            if bad < 5:
                print('MISMATCH', d, t, i, (a, u, b), got)
    print(f'Lean dump check: {n} rows, {bad} mismatches')
    return bad == 0


# ------------------------------------------------------------------------------------------
# Typed (k = 64-capable) simulator.  Node type at level i: s = 0 (interior / fresh) or s >= 1
# (the last s links from the parent chain are all end-links on the same side).  Children of a
# type-s node: one 'same-side' end child of type s+1 (for s = 0 both ends are type 1), one
# 'other-side' end child of type 1, and k-2 interior children of type 0.
# For designs 'U' and 'D2', G depends only on (level, time, type): verified on the explicit tree.
# ------------------------------------------------------------------------------------------

from functools import lru_cache

_MC = {}


def mult(P, i, s):
    key = (P.k, i, s)
    if key in _MC:
        return _MC[key]
    v = _mult(P, i, s)
    _MC[key] = v
    return v


def _mult(P, i, s):
    """number of nodes of type s at level i."""
    k = P.k
    if i == 0:
        return 1 if s == 0 else 0
    if s == 0:
        return (k - 2) * k ** (i - 1)
    if s == 1:
        return 2 * mult(P, i - 1, 0) + sum(mult(P, i - 1, q) for q in range(1, i))
    return mult(P, i - 1, s - 1)


def child_types(P, s):
    """list of (child type, count, which) ; which in {'same','other','int'}."""
    if s == 0:
        return [(1, 1, 'same'), (1, 1, 'other'), (0, P.k - 2, 'int')]
    return [(s + 1, 1, 'same'), (1, 1, 'other'), (0, P.k - 2, 'int')]


def typed_sim(P, d, design, report=None):
    """returns dict with per-(t,i,s) records and global checks."""
    k = P.k
    TF = P.tf(d)
    N = k ** d
    R = [Fr(k ** (d - i)) for i in range(d + 1)]
    # G[i][s] at current time ; initial t = 0: all keys at root: W_root = N, W_y = 0 below
    G = [{s: (Fr(0) if i == 0 else R[i]) for s in range(i + 1)} for i in range(d + 1)]
    recs = {}
    checks = dict(nonint=0, neg=0, odd_pi=0, cons=0, recv=0)
    prev_recv = None
    for t in range(0, TF):
        newG = [dict(G[i]) for i in range(d + 1)]
        recv = [{s: Fr(0) for s in range(i + 1)} for i in range(d + 1)]
        total = Fr(0)
        seen = {}
        for i in range(d + 1):
            if t == 0:
                act = (i == 0)
            else:
                act = P.active(d, i, t)
            if not act:
                continue
            role = 'topDesc' if t == 0 else P.role(d, i, t)
            c = P.cap(d, i, t)
            for s in range(i + 1):
                m = mult(P, i, s)
                if m == 0:
                    continue
                Gx = G[i][s]
                if i < d:
                    ch = child_types(P, s)
                    a = sum(cnt * G[i + 1][cs] for cs, cnt, _ in ch) - Gx
                else:
                    a = R[i] - Gx
                total += m * a
                if prev_recv is not None and prev_recv[i][s] != a:
                    checks['recv'] += 1
                pi = Fr(0) if t == 0 else P.up(d, i, t, a=a)
                if role == 'botRise':
                    pi = a
                if pi.denominator != 1 or pi % 2 != 0:
                    checks['odd_pi'] += 1
                theta = {}
                if role == 'botRise':
                    theta = None
                elif role == 'topDesc':
                    theta = {'same': Fr(0), 'other': Fr(0), 'int': Fr(0)}
                    if Gx != 0:
                        checks['cons'] += 1
                elif design == 'U':
                    beta = P.down(d, i, t)
                    theta = {w: G[i + 1][cs] - beta for cs, _, w in child_types(P, s)}
                elif design == 'D2':
                    theta = {'same': pi / 2 + Gx, 'other': pi / 2, 'int': Fr(0)}
                else:
                    raise ValueError(design)
                if theta is not None:
                    ch = child_types(P, s)
                    if sum(cnt * theta[w] for _, cnt, w in ch) != pi + Gx:
                        checks['cons'] += 1
                    blocks = {}
                    for cs, cnt, w in ch:
                        b = G[i + 1][cs] - theta[w]
                        blocks[w] = b
                        if b < 0:
                            checks['neg'] += 1
                        if b.denominator != 1:
                            checks['nonint'] += 1
                        if (i + 1, cs) in seen and seen[(i + 1, cs)] != b:
                            checks['cons'] += 1   # type not closed
                        seen[(i + 1, cs)] = b
                        recv[i + 1][cs] = b
                        newG[i + 1][cs] = theta[w]
                    if sum(cnt * blocks[w] for _, cnt, w in ch) != a - pi:
                        checks['cons'] += 1
                else:
                    blocks = None
                newG[i][s] = Gx + pi
                if i > 0:
                    # parent receives pi from each child; account per parent type later
                    pass
                for v in (a, pi, Gx):
                    if v.denominator != 1:
                        checks['nonint'] += 1
                recs[(t, i, s)] = dict(a=a, pi=pi, G=Gx, c=c, role=role, blocks=blocks,
                                       theta=theta, mult=m)
        # parents receive k * pi of children (all children of a parent at level i+1 share
        # the parent's... types differ, so sum per child type)
        for (tt, i, s), r in list(recs.items()):
            if tt != t or i == 0:
                continue
        for i in range(1, d + 1):
            for s in range(i + 1):
                r = recs.get((t, i, s))
                if r is None:
                    continue
        # received from children: parent of type sp at level i-1 gets sum over its children
        for i in range(0, d):
            for sp in range(i + 1):
                if mult(P, i, sp) == 0:
                    continue
                tot = Fr(0)
                for cs, cnt, _ in child_types(P, sp):
                    r = recs.get((t, i + 1, cs))
                    if r is not None:
                        tot += cnt * r['pi']
                recv[i][sp] += tot
        if total != N:
            checks['cons'] += 1
        prev_recv = recv
        G = newG
    return recs, checks


def residual_onesided(P, r):
    """Chvatal-style one-sided spill bound max_j (L_j^+ + R_j^+) at a sender (no outsiders):
    L_j = T_{j-1} - pi/2, R_j = pi/2 + G - T_j, T_j = theta-prefix (ends at positions 1,k).
    Only the 3 theta values matter (ends 'same'/'other' at positions 1 and k)."""
    th = r['theta']
    if th is None or r['role'] == 'topDesc':
        return Fr(0)
    k = P.k
    pi, G = r['pi'], r['G']
    seq = [th['same']] + [th['int']] * (k - 2) + [th['other']]
    best = Fr(0)
    T = Fr(0)
    for j in range(k):
        L = T - pi / 2
        T += seq[j]
        Rr = pi / 2 + G - T
        v = max(L, 0) + max(Rr, 0)
        best = max(best, v)
    # by symmetry also the mirrored orientation (same end on the right)
    seq = seq[::-1]
    T = Fr(0)
    for j in range(k):
        L = T - pi / 2
        T += seq[j]
        Rr = pi / 2 + G - T
        best = max(best, max(L, 0) + max(Rr, 0))
    return best


if __name__ == '__main__':
    verify_lean_dump(sys.argv[1])
