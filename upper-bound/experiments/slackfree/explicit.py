#!/usr/bin/env python3
"""Explicit-node flow tables (small k) + key-level simulation with PERFECT separators.

Designs:
  U   Chvatal: every child gets beta(i,t) (Lean/Chvatal closed forms).
  D2  slack-free 'cut layout': virtual sorted layout of x's range = [0, sum_l U_l), U_l = G_l
      (exact deficit of child l); the ancestral share gL (low end) / gH (high end) and the two
      fringes pi/2 are cut off the two ends; child l gets |I_l cap [gL+pi/2, S-gH-pi/2)|, and its
      own (gL', gH') are the parts of I_l cut off at the low / high end.
  P   one-sided optimal (Fractions): theta_end = pi/2 + G - r c, theta_int = (2rc - G)/(k-2),
      r = (k-1)/(2A^2k^2)   (only for the one-sided residual check; non-integral).
Key simulation: N = k^d keys, key r addressed to leaf r.  Every active node sorts its keys and
sends F1 (pi/2 smallest) + F2 (pi/2 largest) up and consecutive blocks b_1..b_k down (perfect
separator).  We count order-0 outsiders (keys not addressed below their node) after each stage.
"""
import sys
import numpy as np
from fractions import Fraction as Fr
from flowsim import Par


def build_table(P, d, design):
    k = P.k
    TF = P.tf(d)
    R = [k ** (d - i) for i in range(d + 1)]
    # G per node, gL/gH per node (for D2) ; level i arrays of length k^i (python objects)
    G = [[(0 if i == 0 else R[i]) for _ in range(k ** i)] for i in range(d + 1)]
    gL = [[0] * (k ** i) for i in range(d + 1)]
    gH = [[0] * (k ** i) for i in range(d + 1)]
    if design == 'P':
        G = [[Fr(v) for v in row] for row in G]
    table = []   # per t: dict level -> list of (a, pi, blocks list) per node or None
    maxres = Fr(0)
    rstar = Fr(k - 1, 2 * P.A ** 2 * k ** 2)
    for t in range(TF):
        step = {}
        newG = [row[:] for row in G]
        newgL = [row[:] for row in gL]
        newgH = [row[:] for row in gH]
        for i in range(d + 1):
            act = (i == 0) if t == 0 else P.active(d, i, t)
            if not act:
                continue
            role = 'topDesc' if t == 0 else P.role(d, i, t)
            c = P.cap(d, i, t)
            rows = []
            for j in range(k ** i):
                Gx = G[i][j]
                if i < d:
                    U = [G[i + 1][j * k + l] for l in range(k)]
                    a = sum(U) - Gx
                else:
                    U = []
                    a = R[i] - Gx
                if role == 'botRise':
                    pi = a
                elif t == 0:
                    pi = 0
                else:
                    pi = P.up(d, i, t)
                    assert pi.denominator == 1
                    pi = int(pi) if design != 'P' else pi
                if role == 'botRise':
                    blocks = [0] * k if i < d else []
                    newG[i][j] = Gx + pi
                    if design == 'D2':
                        newgL[i][j] = gL[i][j] + pi // 2
                        newgH[i][j] = gH[i][j] + pi - pi // 2
                    rows.append((a, pi, blocks))
                    continue
                if role == 'topDesc':
                    th = [0] * k
                    for l in range(k):
                        newgL[i + 1][j * k + l] = 0
                        newgH[i + 1][j * k + l] = 0
                elif design == 'U':
                    beta = P.down(d, i, t)
                    th = [u - beta for u in U]
                elif design == 'P':
                    r = rstar * c
                    te = pi / 2 + Gx - r
                    ti = (2 * r - Gx) / (k - 2)
                    th = [te] + [ti] * (k - 2) + [te]
                elif design == 'D2':
                    S = sum(U)
                    lo, hi = gL[i][j] + pi // 2, S - gH[i][j] - pi // 2
                    th = []
                    pos = 0
                    for l in range(k):
                        s0, s1 = pos, pos + U[l]
                        pos = s1
                        b = max(0, min(s1, hi) - max(s0, lo))
                        cl = max(0, min(s1, lo) - s0)
                        ch = max(0, s1 - max(s0, hi))
                        newgL[i + 1][j * k + l] = cl
                        newgH[i + 1][j * k + l] = ch
                        th.append(U[l] - b)
                blocks = [U[l] - th[l] for l in range(k)]
                assert sum(blocks) == a - pi, (t, i, j, design)
                if role != 'topDesc' and design != 'D2':
                    # one-sided residual (Chvatal accounting), relative to c
                    T = 0
                    for l in range(k):
                        L = T - pi / 2 if design == 'P' else Fr(T) - Fr(pi, 2)
                        T += th[l]
                        Rr = pi / 2 + Gx - T if design == 'P' else Fr(pi, 2) + Gx - T
                        v = (max(L, 0) + max(Rr, 0)) / c
                        if t >= 2 and v > maxres:
                            maxres = v
                for l in range(k):
                    newG[i + 1][j * k + l] = th[l]
                newG[i][j] = Gx + pi
                if design == 'D2':
                    assert gL[i][j] + gH[i][j] == Gx, (t, i, j)
                    newgL[i][j] = gL[i][j] + pi // 2
                    newgH[i][j] = gH[i][j] + pi // 2
                rows.append((a, pi, blocks))
            step[i] = rows
        table.append(step)
        G, gL, gH = newG, newgL, newgH
    return table, maxres, rstar


def key_sim(P, d, table, seed=1):
    """perfect separators; returns list over t of (max outsiders / c over nodes, total outsiders)."""
    k = P.k
    N = k ** d
    rng = np.random.default_rng(seed)
    keys = rng.permutation(N)
    # node of each key: (level, index); start all at root
    lev = np.zeros(N, dtype=np.int64)
    idx = np.zeros(N, dtype=np.int64)
    out = []
    for t, step in enumerate(table):
        newlev = lev.copy()
        newidx = idx.copy()
        for i, rows in step.items():
            sel = np.nonzero(lev == i)[0]
            if len(sel) == 0:
                continue
            order = np.lexsort((keys[sel], idx[sel]))
            sel = sel[order]
            nid = idx[sel]
            # segments per node
            bounds = np.flatnonzero(np.diff(nid)) + 1
            starts = np.concatenate(([0], bounds))
            ends = np.concatenate((bounds, [len(sel)]))
            for s0, s1 in zip(starts, ends):
                j = int(nid[s0])
                a, pi, blocks = rows[j]
                assert Fr(a).denominator == 1
                a = int(a)
                assert s1 - s0 == a, (t, i, j, s1 - s0, a)
                seg = sel[s0:s1]
                h = int(pi) // 2
                # up: first h and last h (all of them if botRise: pi = a)
                if int(pi) == a:
                    newlev[seg] = i - 1
                    newidx[seg] = j // k
                    continue
                newlev[seg[:h]] = i - 1
                newidx[seg[:h]] = j // k
                newlev[seg[a - h:]] = i - 1
                newidx[seg[a - h:]] = j // k
                pos = h
                for l in range(k):
                    b = int(blocks[l])
                    newlev[seg[pos:pos + b]] = i + 1
                    newidx[seg[pos:pos + b]] = j * k + l
                    pos += b
                assert pos == a - h
        lev, idx = newlev, newidx
        # order-0 outsiders: key not addressed below its node
        span = np.array([k ** (d - i) for i in range(d + 1)], dtype=np.int64)[lev]
        outs = (keys // span) != idx
        tot = int(outs.sum())
        worst = 0.0
        if tot:
            L, I = lev[outs], idx[outs]
            pairs, cnt = np.unique(L * (k ** d) + I, return_counts=True)
            for p, cn in zip(pairs, cnt):
                ii = int(p // (k ** d))
                worst = max(worst, cn / float(P.cap(d, ii, t + 1)))
        out.append((t + 1, worst, tot))
    return out


if __name__ == '__main__':
    x, y, z, d = map(int, sys.argv[1:5])
    P = Par(x, y, z)
    for des in ('U', 'D2', 'P'):
        tab, res, rstar = build_table(P, d, des)
        slack = (P.A * P.nu * P.k - 2 * P.A * P.nu + 1) / (2 * P.A ** 2 * P.k ** 2)
        print(f'({x},{y},{z}) d={d} tf={P.tf(d)} design {des}: one-sided residual/c = '
              f'{float(res):.4e}  (slackCoeff {float(slack):.4e}, r* = {float(rstar):.4e})')
        if des != 'P':
            negs = sum(1 for st in tab for rows in st.values() for (a, pi, bl) in rows
                       if any(b < 0 for b in bl))
            print('   negative blocks:', negs)
            res = key_sim(P, d, tab)
            print('   perfect-separator outsiders per stage (t, max outsiders/c, total):')
            print('   ', [(t, round(w, 6), n) for (t, w, n) in res])
        sys.stdout.flush()
