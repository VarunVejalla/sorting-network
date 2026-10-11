#!/usr/bin/env python3
"""Exact-arithmetic feasibility of Chvatal's conditions (4.2)-(4.5) for integer (x,y,z), for four
treatments of the Lemma-4.2 schedule residual:

  R0  Chvatal / Lean table:       res = (A nu k - 2 A nu + 1)/(2 A^2 k^2)            [slackCoeff]
  R1  best one-sided table:       res = (k-1)/(2 A^2 k^2)       (provably optimal under P alone)
  R2  slack-free D2 + NEW two-sided invariant Q:
                                  res = kap*(mu + epsB/2)/(A nu - 1)   kap = 1 (worst), 1/2 (centred)
  R3  idealised res = 0 (the tapered/NOTES model assumption)

Fixed (proved route): eps_F = 1/86e6 (valid 131040 <= f < 8.5e9), delta_F = 128/4095.
mu = min((4.3) nu/(A k^2), (4.4) delta_F (A nu k - 1)/(2 A^2 k^2)) * (1 - 2^-10).
delta = smallest dyadic-grid rational satisfying (4.5) (eps_F/(A nu) + delta^2 A k/nu <= delta).
(4.2):  mu + (k-1) mu sib + res + epsB*eta + mu delta A^2 k <= mu A nu,
        sib = delta k A^2/(1 - delta^2 k^2 A^2), eta = max a/c (1 for R0; from the simulator for D2).
eps_B -> window: L=42 certified (1/59e6, BULK2); other L use the BULK2-calibrated model eps2(L)
(exchange_rate.py), guaranteed value at the window's lower end.  stage = 3*T(L+1), T(p)=p(p+1)/2.
slope = stage * (x+y)/(x z).
"""
from fractions import Fraction as Fr
import math, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'tapered'))
from exchange_rate import eps2_scalar  # noqa: E402

EPSF = Fr(1, 86000000)
DF = Fr(128, 4095)
F_LO, F_HI = 131040, Fr(85, 10) * 10 ** 9
LMIN = int(os.environ.get('LMIN', '20'))   # LMIN=42: only certified-or-larger windows


def eps_window(L):
    if L == 42:
        return Fr(1, 59000000)
    return Fr(eps2_scalar(L)).limit_denominator(10 ** 15)


def T(p):
    return p * (p + 1) // 2


def delta_choice(k, A, nu):
    # smallest delta on grid 2^-60 multiples with (4.5): epsF/(A nu) + d^2 A k / nu <= d
    a2 = A * k / nu
    c0 = EPSF / (A * nu)
    disc = 1 - 4 * a2 * c0
    if disc < 0:
        return None
    lo = (1 - math.sqrt(float(disc))) / (2 * float(a2))
    d = Fr(math.ceil(lo * 2 ** 60 * (1 + 1e-12)), 2 ** 60)
    while not (c0 + d * d * a2 <= d):
        d += Fr(1, 2 ** 60)
    if d * k * A >= 1:
        return None
    return d


def analyse(x, y, z, regime, eta=Fr(1), kap=Fr(1)):
    k, A, nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
    Anu = A * nu
    if Anu <= 1:
        return None
    mu43 = nu / (A * k * k)
    mu44 = DF * (Anu * k - 1) / (2 * A * A * k * k)
    mu = min(mu43, mu44) * (1 - Fr(1, 1024))
    bind_mu = '(4.3)' if mu43 <= mu44 else '(4.4)'
    delta = delta_choice(k, A, nu)
    if delta is None:
        return dict(ok=False, why='(4.5) infeasible')
    sib = delta * k * A * A / (1 - delta ** 2 * k ** 2 * A ** 2)
    base = mu * (Anu - 1) - (k - 1) * mu * sib - mu * delta * A * A * k
    if regime == 'R0':
        res = (Anu * k - 2 * Anu + 1) / (2 * A * A * k * k)
        epsB = (base - res) / eta
    elif regime == 'R1':
        res = Fr(k - 1, 2 * A * A * k * k)
        epsB = (base - res) / eta
    elif regime == 'R2':
        # base - kap(mu + epsB/2)/(Anu-1) - epsB*eta >= 0
        res = kap * mu / (Anu - 1)
        epsB = (base - res) / (eta + kap / (2 * (Anu - 1)))
    else:
        res = Fr(0)
        epsB = base / eta
    out = dict(k=k, A=A, nu=nu, mu=mu, bind_mu=bind_mu, delta=delta, sib=(k - 1) * mu * sib,
               base=base, res=res, budget=mu * (Anu - 1), epsB=epsB)
    if epsB <= 0:
        out.update(ok=False, why=f'(4.2): residual {float(res/mu):.2f} mu > budget '
                                 f'{float(base/mu):.2f} mu')
        return out
    # smallest window with eps_window(L) <= epsB, fringe range, m >= A^2k^2
    fom = (nu / (2 * A * k)) * (1 - 1 / (Anu * k)) / (1 - Fr(1, (A * k) ** 2))
    for L in range(LMIN, 80):
        if eps_window(L) <= epsB and 2 ** L * fom >= F_LO and 2 ** L >= (A * k) ** 2:
            break
    fhi = 2 ** (L + 1) * fom
    stage = 3 * T(L + 1)
    slope = Fr(stage * (x + y), x * z)
    out.update(ok=True, L=L, stage=stage, slope=slope, f_lo=float(2 ** L * fom), f_hi=float(fhi),
               f_in_range=fhi < F_HI, margin=float(epsB / eps_window(L)))
    return out


if __name__ == '__main__':
    triples = [(6, 12, 6), (6, 11, 6), (6, 10, 6), (6, 9, 6), (6, 8, 6), (6, 7, 6), (6, 7, 5),
               (6, 8, 5), (6, 9, 5), (5, 7, 5), (5, 8, 5), (5, 9, 5), (5, 10, 5), (6, 10, 5),
               (6, 6, 5), (7, 9, 6), (7, 10, 6), (7, 11, 7), (7, 12, 7), (6, 13, 7), (7, 13, 7),
               (6, 11, 7), (6, 12, 7), (5, 8, 4), (5, 9, 4)]
    # eta for D2 measured by run_tables (max a/c): pass conservative 1 + 1/(k A nu (A nu - 1))
    for reg in ('R0', 'R1', 'R2', 'R2c', 'R3'):
        print(f'==== regime {reg}')
        best = None
        for (x, y, z) in triples:
            if y <= z:
                continue
            k, A, nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
            Anu = A * nu
            eta = Fr(1)
            if reg == 'R1':
                eta = 1 + Fr(k - 1, 2 * A * A * k * k) / nu ** 2
            if reg in ('R2', 'R2c', 'R3'):
                eta = 1 + 1 / (k * Anu * (Anu - 1)) if Anu > 1 else Fr(1)
            r = analyse(x, y, z, 'R2' if reg.startswith('R2') else reg, eta=eta,
                        kap=Fr(1, 2) if reg == 'R2c' else Fr(1))
            if r is None:
                continue
            if not r['ok']:
                print(f'({x},{y},{z}) INFEASIBLE {r["why"]}')
                continue
            print(f'({x},{y},{z}) mu={float(r["mu"]):.3e}{r["bind_mu"]} delta={float(r["delta"]):.3e} '
                  f'budget={float(r["budget"]/r["mu"]):.2f}mu sib={float(r["sib"]/r["mu"]):.3f}mu '
                  f'res={float(r["res"]/r["mu"]):.3f}mu epsB<={float(r["epsB"]):.3e} '
                  f'(1/{float(1/r["epsB"]):.3g}) -> L={r["L"]} (margin x{r["margin"]:.2f}) '
                  f'f=[{r["f_lo"]:.3g},{r["f_hi"]:.3g}]{"" if r["f_in_range"] else " f>8.5e9!"} '
                  f'stage={r["stage"]} slope={float(r["slope"]):.1f}')
            if best is None or r['slope'] < best[0]:
                best = (r['slope'], (x, y, z))
        print('best', float(best[0]) if best else None, best[1] if best else None)
