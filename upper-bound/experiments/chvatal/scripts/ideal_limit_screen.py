#!/usr/bin/env python3
"""Ideal-limit screen of Chvatal's M-sorter tree (DCS-TR-294 Theorems 1.1/1.2), UB-09.

Theorem 1.1 is Theorem 1.2's construction with Batcher m-sorters, m ~ 2^60, so the
binary coefficient of the M-sorter framework is the slope

    slope = L(L+1) (x+y) / (x z),     k = 2^x, A = 2^y, nu = 2^-z, m = 2^L,

with two Batcher sorts of depth L(L+1)/2 per tree step (window 'top', as in
chvatal_param_search.py). This screen keeps the paper's tree constraints (4.2)-(4.5)
and the template constraint (5.1) m >= (Ak)^2, but replaces the certified separator
constants by idealised ones:

  * Property B:  eps_B = C_B / sqrt(m). Paper: C_B = sqrt(2(1+ln m)). Bulk leak in
    rows is eps_B m / 2, so the D2 measurements at m = 8192 give C_B = 0.39
    (certified, 17.7 rows) and 0.084 (attack, 3.79 rows).
  * Property F:  eps_F given directly (0 = perfect fringe), delta_F given directly
    (paper 1/25; up to 1 would mean the whole fringe obeys the eps_F law).

Every real (x, y, z, L) is searched, so with eps_F = 0 the result is a floor for
this tree: no sharpening of separator certificates alone goes below it. Claim
level: model (constraint system as transcribed in chvatal_param_search.py).

    python ideal_limit_screen.py
"""
import math

import numpy as np


KNOB = dict(slack=1.0, mu=1.0, sib=1.0)     # tree-analysis sensitivity (--sensitivity)


def emax(x, y, z, deltaF, epsF):
    """Largest eps_B allowed by (4.2)-(4.5), vectorised over arrays x, y, z."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    with np.errstate(all='ignore'):
        mu = KNOB['mu'] * np.minimum(nu / (A * k * k), 0.5 * deltaF * (A * nu * k - 1) / (A * A * k * k))
        a_, b_ = A * k / nu, epsF / (A * nu)
        disc = 1 - 4 * a_ * b_
        delta = np.where(disc >= 0, (1 - np.sqrt(np.maximum(disc, 0))) / (2 * a_), np.nan)
        sib = delta * k * A * A / (1 - (delta * k * A) ** 2)
        slack = (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
        e = mu * (A * nu - 1 - KNOB['sib'] * (k - 1) * sib - delta * A * A * k) - KNOB['slack'] * slack
        ok = (A * nu > 1) & (delta * k * A < 1) & (disc >= 0)
    return np.where(ok, e, -1.0)


def best_slope(CB, deltaF, epsF, step=0.05):
    """Min slope over real x, y, z; L least real with CB 2^(-L/2) <= emax, 2^L >= (Ak)^2."""
    x = np.arange(1, 12 + 1e-9, step)
    z = np.arange(0.25, 14 + 1e-9, step)
    best = (math.inf, None)
    for yz in np.arange(step, 16 + 1e-9, step):          # y = z + yz, so A nu = 2^yz > 1
        X, Z = np.meshgrid(x, z, indexing='ij')
        Y = Z + yz
        e = emax(X, Y, Z, deltaF, epsF)
        cb = CB(X) if callable(CB) else CB
        with np.errstate(all='ignore'):
            L_b = 2 * np.log2(cb / e)                     # CB / sqrt(2^L) <= e
            L = np.maximum(L_b, 2 * (X + Y))              # (5.1)
            s = L * (L + 1) * (X + Y) / (X * Z)
        s = np.where(e > 0, s, np.inf)
        i = np.unravel_index(np.argmin(s), s.shape)
        if s[i] < best[0]:
            best = (float(s[i]), (float(X[i]), float(Y[i]), float(Z[i]), float(L[i]),
                                  bool(L_b[i] < 2 * (X[i] + Y[i]))))
    return best


def coupled_slope(CB, table, deltaF, step=0.1, f_min=4):
    """As best_slope, but eps_F = table(f, deltaF) at the structural fringe f = m f_over_m.

    `table(f, u)` returns the attack eps_F for fringe rows f at capture ratio u; f below
    f_min is treated as infeasible. L is scanned on a grid."""
    x = np.arange(1, 10 + 1e-9, step)
    z = np.arange(0.25, 12 + 1e-9, step)
    best = (math.inf, None)
    for yz in np.arange(step, 12 + 1e-9, step):
        X, Z = np.meshgrid(x, z, indexing='ij')
        Y = Z + yz
        k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
        fom = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
        for L in np.arange(4, 70, 0.25):
            f = 2.0 ** L * fom
            epsF = table(np.maximum(f, f_min), deltaF)
            e = emax(X, Y, Z, deltaF, epsF)
            ok = (e > 0) & (CB * 2.0 ** (-L / 2) <= e) & (L >= 2 * (X + Y)) & (f >= f_min)
            s = np.where(ok, L * (L + 1) * (X + Y) / (X * Z), np.inf)
            i = np.unravel_index(np.argmin(s), s.shape)
            if s[i] < best[0]:
                best = (float(s[i]), (float(X[i]), float(Y[i]), float(Z[i]), float(L),
                                      float(f[i]), float(epsF[i])))
    return best


FS = np.array([4, 8, 16, 32, 64.0])
US = np.array([0.25, 0.5, 0.75, 1.0])
# Attack eps_F (fringe_attack_scan.py, n = 500, one seed): rows f, columns u.
EPS_F = np.array([[0.0640, 0.0990, 0.1407, 0.2030],
                  [0.0180, 0.0305, 0.0590, 0.1177],
                  [0.0035, 0.0077, 0.0192, 0.0659],
                  [0.0000, 0.0014, 0.0040, 0.0356],
                  [0.0000, 0.0000, 0.0007, 0.0183]])


def attack_table(f, u):
    """Attack eps_F at capture ratio u (a grid value), log-log in f; zeros stay zero
    (optimistic), and beyond f = 64 the last slope is extended."""
    col = EPS_F[:, int(np.argmin(abs(US - u)))]
    lf = np.log(f)
    out = np.zeros_like(lf)
    pos = col > 0
    lx, ly = np.log(FS[pos]), np.log(col[pos])
    if len(lx) >= 2:
        slope = (ly[-1] - ly[-2]) / (lx[-1] - lx[-2])
        val = np.where(lf <= lx[-1], np.interp(lf, lx, ly), ly[-1] + slope * (lf - lx[-1]))
        out = np.exp(val)
        last_zero = FS[~pos].min() if (~pos).any() else np.inf
        out = np.where(f >= last_zero, 0.0, out)
    return out


def sensitivity():
    print('tree-analysis sensitivity at attack C_B 0.084, delta_F 0.75 (grid step 0.15)')
    for name, kn in [('slack x0', dict(slack=0)), ('mu x2', dict(mu=2)), ('sib x0', dict(sib=0)),
                     ('all three', dict(slack=0, mu=2, sib=0))]:
        KNOB.update({**dict(slack=1.0, mu=1.0, sib=1.0), **kn})
        s, p = coupled_slope(0.084, attack_table, 0.75, step=0.15)
        print(f'{name}: {s:.1f} at x y z L = ' + ' '.join(f'{v:.2f}' for v in p[:4]), flush=True)
    KNOB.update(slack=1.0, mu=1.0, sib=1.0)


def main():
    import sys
    if '--sensitivity' in sys.argv:
        sensitivity()
        return
    print('coupled screen: eps_F = attack table at the structural fringe f')
    print('C_B | delta_F | slope | x y z L | f rows | eps_F')
    for CB in [0.39, 0.084]:
        for dF in [0.25, 0.5, 0.75, 1.0]:
            s, p = coupled_slope(CB, attack_table, dF)
            if p is None:
                print(f'{CB} | {dF} | infeasible', flush=True)
                continue
            print(f'{CB} | {dF} | {s:.1f} | ' + ' '.join(f'{v:.2f}' for v in p[:4])
                  + f' | {p[4]:.1f} | {p[5]:.2e}', flush=True)
    print()
    print('decoupled floors (eps_F given directly)')
    old_main()


def old_main():
    def paper(L_guess=60):
        return math.sqrt(2 * (1 + L_guess * math.log(2)))
    cases = [
        ('paper C_B (L~60), delta_F 1/25, eps_F 0', paper(), 1 / 25, 0.0),
        ('certified C_B 0.39, delta_F 1/25, eps_F 0', 0.39, 1 / 25, 0.0),
        ('attack C_B 0.084, delta_F 1/25, eps_F 0', 0.084, 1 / 25, 0.0),
        ('attack C_B 0.084, delta_F 1, eps_F 0', 0.084, 1.0, 0.0),
        ('C_B 0.01, delta_F 1, eps_F 0', 0.01, 1.0, 0.0),
        ('C_B 0 (perfect separator), delta_F 1, eps_F 0', 1e-300, 1.0, 0.0),
    ]
    print('case | slope | x y z L | (5.1) binding')
    for name, CB, dF, eF in cases:
        s, p = best_slope(CB, dF, eF)
        print(f'{name} | {s:.1f} | ' + ' '.join(f'{v:.2f}' for v in p[:4]) + f' | {p[4]}', flush=True)


if __name__ == '__main__':
    main()
