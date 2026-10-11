#!/usr/bin/env python3
"""Stage-0 gate, part 3: (6,10,6) schedule closed forms, meeting level, final sorter, depth.

alpha(t) = ceilParity(max(0, ceil((6t - 6d + 23)/10)), t),  omega(t) = ceilParity(ceil((6t+10)/16), t)
(flowsim.Par general envelopes; for (6,12,6) they coincide with Lean alpha7/omega7, checked here).
tf = first t >= 2 with alpha(t) >= omega(t).
Depth: totalDepth(d) = 6320 + (tf-1)*2838 + T(lg finalBlock), finalBlock = 64^(d - lam + 1) (64 children
of a level-(lam-1) bag, as RealBlocks.finalS), T(p) = p(p+1)/2 (bitonic), 2838 = 3 T(43).
"""
import sys
from fractions import Fraction as Fr
from flowsim import Par
from d2lean import constants


def T(p):
    return p * (p + 1) // 2


def sched(P, d):
    tf = P.tf(d)
    lam = P.alpha(d, tf)
    ok_meet = lam == P.omega(d, tf)
    ok_apart = all(P.alpha(d, t) < P.omega(d, t) for t in range(2, tf))
    return tf, lam, ok_meet, ok_apart


if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    # (6,12,6): general formulas vs Lean closed forms
    Pg, PL = Par(6, 12, 6), Par(6, 12, 6, lean7=True)
    mism = [(d, t) for d in range(14, dmax + 1) for t in range(0, 3 * d - 19)
            if (Pg.alpha(d, t), Pg.omega(d, t)) != (PL.alpha(d, t), PL.omega(d, t))]
    tfm = [d for d in range(14, dmax + 1) if Pg.tf(d) != 3 * d - 20]
    print(f'(6,12,6) general vs Lean alpha7/omega7: {len(mism)} mismatches; tf != 3d-20 for {len(tfm)} d')
    P = Par(6, 10, 6)
    C = constants(P)
    rows = {}
    bad = []
    for d in range(14, dmax + 1):
        tf, lam, m, ap = sched(P, d)
        if not (m and ap):
            bad.append((d, tf, lam, m, ap))
        r = d % 6
        rows.setdefault(r, []).append((d, tf, lam))
    print(f'(6,10,6) d=14..{dmax}: meet/apart failures: {bad}')
    for r in sorted(rows):
        L = rows[r]
        offs = {3 * tf - 8 * d for d, tf, _ in L}
        lams = {d - lam for d, _, lam in L}
        print(f'  d = {r} mod 6: 3*tf - 8d in {sorted(offs)} ; d - lam in {sorted(lams)}  (d={L[0][0]}..{L[-1][0]})')
    # closed forms and depth
    print('  per residue: tf, lam, final block, c(lam,tf), mu*delta*c(lam,tf) < 1, totalDepth')
    c1s = {}
    for r in sorted(rows):
        d, tf, lam = rows[r][3]
        fb = 6 * (d - lam + 1)
        cap = P.cap(d, lam, tf)
        tot = 6320 + (tf - 1) * 2838 + T(fb)
        c1 = Fr(3784, 3) * 6 * d - tot
        c1s[r] = c1
        print(f'   d={d} (r={r}): tf={tf} lam={lam} finalBlock=2^{fb} (depth T={T(fb)}) c(lam,tf)={cap} '
              f'mu*delta*c={float(C["mu"] * C["delta"] * cap):.3e} totalDepth={tot} = (3784/3)*6d - {c1}')
        # verify identical c1 over all d of the residue
        for dd, tff, lamm in rows[r]:
            fbb = 6 * (dd - lamm + 1)
            tt = 6320 + (tff - 1) * 2838 + T(fbb)
            assert Fr(3784, 3) * 6 * dd - tt == c1, (dd, tt)
    cmin = min(c1s.values())
    print(f'  totalDepth(d) <= (3784/3) * 6d - {cmin} for all d >= 14 (period 6 in d; checked to {dmax})')
    print(f'  with lg n > 6(d-1):  D(n) <= (3784/3) lg n - {cmin - 7568} = {3784/3:.4f} lg n - {float(cmin - 7568):.2f}')
    print(f'  integer-coefficient form: D(n) <= 1262 lg n - c0 needs care (1262 > 3784/3); '
          f'e.g. D(n) <= 1261.34 lg n - {float(cmin - 7568):.0f}')
