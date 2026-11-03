#!/usr/bin/env python3
"""Price the repository's tree analyses at ideal (attack-level) separators, UB-09 follow-on.

Corrects ideal_limit_screen.py, which charged two sorts per tree step while using the
bulk and fringe constants of the three-sort (two-scramble) stage. Here the stage depth is
s * L(L+1)/2 with s = 3 (the stage those constants belong to); s = 2 is kept as the
"first sort free" bound, a floor for any merge-first stage with the same leak.

Tree analyses, as (4.2) multiplied by A nu (slackfree/SLACKFREE.md sec. 4, feas.py):

    base = mu (A nu - 1 - (k-1) sib - delta A^2 k)
    R0   eps_B         <= base - (A nu k - 2 A nu + 1)/(2 A^2 k^2)          Chvatal
    R1   eps_B eta1    <= base - (k-1)/(2 A^2 k^2)                          design P (789.75 proof)
    R2   eps_B (eta2 + kap/(2(A nu-1))) <= base - kap mu/(A nu - 1)         D2 + invariant Q, kap = 1
    R2c  as R2 with kap = 1/2                                               centred
    R3   eps_B eta2    <= base                                              zero residual (not reachable)

    eta1 = 1 + (k-1)/(2 A^2 k^2 nu^2),  eta2 = 1 + 1/(k A nu (A nu - 1)).

Bulk eps_B(m), m = 2^L rows, two-round (three-sort) separator:
    certified: walk-bound/na_precision.py (d_na, uniform), interpolated in log over L;
    attack:    3.79 rows at m = 8192 (D2 sec. 11), scaled as m^(1/4) like the certified
               leak in rows (heuristic); eps_B = 2 rows / m.
Fringe: the attack eps_F table of ideal_limit_screen.py at the structural fringe.

Real x, y, z, L; no rounding reserve; integer effects and the root separator are free.
Claim level: model (optimistic floor for each analysis).

    python tree_pricing.py            # full table (a few minutes; caches the bulk table)
    python tree_pricing.py --check    # reproduce the 789.75 R1 point
"""
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ideal_limit_screen import attack_table  # noqa: E402

LS = np.arange(4.0, 64.01, 2.0)


def certified_table(cache):
    if cache and os.path.exists(cache):
        return np.load(cache)
    sys.path.insert(0, os.path.join(HERE, "..", "..", "walk-bound"))
    import na_precision as NP
    d = np.array([NP.d_na(L, NP.e1_na(L, uniform=True), uniform=True)[0] for L in LS])
    if cache:
        np.save(cache, d)
    return d


def bulk_models(cache):
    d = certified_table(cache)
    lcert = np.log(d)

    def cert(L):
        return np.exp(np.interp(L, LS, lcert))

    def attack(L):
        rows = 3.79 * 2.0 ** ((L - 13.0) / 4)
        return 2 * rows / 2.0 ** L
    return dict(certified=cert, attack=attack)


def allowance(regime, x, y, z, deltaF, epsF, kmu=1.0):
    """Largest eps_B allowed by (4.2)-(4.5) under the given tree analysis (arrays)."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    Anu = A * nu
    with np.errstate(all='ignore'):
        mu = kmu * np.minimum(nu / (A * k * k), 0.5 * deltaF * (Anu * k - 1) / (A * A * k * k))
        a_, b_ = A * k / nu, epsF / Anu
        disc = 1 - 4 * a_ * b_
        delta = np.where(disc >= 0, (1 - np.sqrt(np.maximum(disc, 0))) / (2 * a_), np.nan)
        sib = delta * k * A * A / (1 - (delta * k * A) ** 2)
        base = mu * (Anu - 1 - (k - 1) * sib - delta * A * A * k)
        eta1 = 1 + (k - 1) / (2 * A * A * k * k * nu * nu)
        eta2 = 1 + 1 / (k * Anu * (Anu - 1))
        if regime == 'R0':
            e = base - (Anu * k - 2 * Anu + 1) / (2 * A * A * k * k)
        elif regime == 'R1':
            e = (base - (k - 1) / (2 * A * A * k * k)) / eta1
        elif regime in ('R2', 'R2c'):
            kap = 1.0 if regime == 'R2' else 0.5
            e = (base - kap * mu / (Anu - 1)) / (eta2 + kap / (2 * (Anu - 1)))
        elif regime == 'R3':
            e = base / eta2
        else:
            raise ValueError(regime)
        ok = (Anu > 1) & (delta * k * A < 1) & (disc >= 0)
    return np.where(ok, e, -1.0)


def price(regime, bulk, deltaF, sorts=3, step=0.1, f_min=4, kmu=1.0):
    x = np.arange(1, 10 + 1e-9, step)
    z = np.arange(0.25, 12 + 1e-9, step)
    Ls = np.arange(4, 64, 0.25)
    X, Z, L = np.meshgrid(x, z, Ls, indexing='ij')
    epsB = bulk(L)
    best = (math.inf, None)
    for yz in np.arange(step, 12 + 1e-9, step):
        Y = Z + yz
        k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
        fom = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
        f = 2.0 ** L * fom
        epsF = attack_table(np.maximum(f, f_min), deltaF)
        e = allowance(regime, X, Y, Z, deltaF, epsF, kmu)
        ok = (e > 0) & (epsB <= e) & (L >= 2 * (X + Y)) & (f >= f_min)
        s = np.where(ok, sorts * L * (L + 1) / 2 * (X + Y) / (X * Z), np.inf)
        i = np.unravel_index(np.argmin(s), s.shape)
        if s[i] < best[0]:
            best = (float(s[i]), (float(X[i]), float(Y[i]), float(Z[i]), float(L[i]), float(f[i])))
    return best


def check():
    """The proved R1 point: (4,5,3), delta_F = 1/8, eps_F = 1/190000, rows < 2^26."""
    x, y, z, L = 4, 5, 3, 26
    epsB = 1 / 105000                                  # r1_point.py's eps_B (walk bound d = 6.74e-6 below it)
    for reg in ('R0', 'R1', 'R2', 'R2c', 'R3'):
        e = float(allowance(reg, np.array(x), np.array(y), np.array(z), 1 / 8, 1 / 190000))
        print(f'{reg}: allowance {e:.3e} vs eps_B {epsB:.3e} -> {"OK" if epsB <= e else "FAIL"}')
    print('slope 3 S(26) (x+y)/(xz) =', 3 * 26 * 27 / 2 * (x + y) / (x * z))


def main():
    if '--check' in sys.argv:
        check()
        return
    cache = os.environ.get('BULK_CACHE')
    models = bulk_models(cache)
    regimes = ['R0', 'R1', 'R2', 'R2c', 'R3']
    step = float(os.environ.get('STEP', '0.2'))
    print(f'min slope at s = 3 sorts per step (s = 2: multiply by 2/3, same optimum); grid step {step}',
          flush=True)
    for bname in ('certified', 'attack'):
        for dF in (0.5, 0.75, 1.0):
            for reg in regimes:
                v, p = price(reg, models[bname], dF, sorts=3, step=step)
                tag = 'infeasible' if p is None else (f'{v:.1f} [s=2: {2 * v / 3:.1f}]  ('
                                                      + ' '.join(f'{t:.2f}' for t in p[:4]) + f', f {p[4]:.0f})')
                print(f'{bname:9s} dF={dF:<4} {reg:3s}: {tag}', flush=True)


if __name__ == '__main__':
    main()
