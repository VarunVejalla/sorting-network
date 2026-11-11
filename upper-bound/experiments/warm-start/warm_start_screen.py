#!/usr/bin/env python3
"""Price the warm-start separator stage (WARM-START.md) on the tree model of chvatal/TREE-PRICING.md.

Stage: re-bag by wiring, full column sort S(L), one free row scramble, two-grid band repair covering
the stacked window F*W, depth 2 S(ceil(lg 4FW)). F = number of fragments whose height deviations add
in one new column (F = Fmul * k); W = deviation level counted as "non-deviant" in the previous stage.
Leak: far cells from deviant fragments, c * F^2 rows per column (attack fit c = 0.25 from
window_tail.py), eps = 2 c F^2 / m. Fringe: f = m * fom >= 4 F W. With --exact-fringe the fringe
term eps_F is set to 0 (deterministic capture by the height cap, WARM-START.md section 4).
Claim level: model / heuristic.

    python warm_start_screen.py [--exact-fringe] [--linear] [--power=p] [--bandless] [--gfr=g] [--fwin=g] [c,Fmul ...]
      (Fmul 0 = real F = A/nu; --bandless: stage = sort + scramble only, strays exported as leak)
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'chvatal', 'scripts'))
from ideal_limit_screen import attack_table  # noqa: E402
from tree_pricing import allowance  # noqa: E402


def S(q):
    return q * (q + 1) / 2


def screen(regime, dF, c, Fmul, exact_fringe=False, step=0.2, power=2, bandless=False, gfr=16, fwin=0):
    x = np.arange(1, 9 + 1e-9, step)
    z = np.arange(0.25, 9 + 1e-9, step)
    Ls = np.arange(6, 40 + 1e-9, 0.5)
    X, Z, L = np.meshgrid(x, z, Ls, indexing='ij')
    best = (math.inf, None)
    for yz in np.arange(step, 8 + 1e-9, step):
        Y = Z + yz
        k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
        fom = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
        m = 2.0 ** L
        f = m * fom
        epsF = np.zeros_like(f) if exact_fringe else attack_table(np.maximum(f, 4), dF)
        e = allowance(regime, X, Y, Z, dF, epsF)
        # Fmul > 0: F = Fmul * k (old assumption); Fmul == 0: real layout, F = A/nu (1 - 1/(Ak)^2)
        F = np.maximum(2.0, Fmul * k) if Fmul > 0 else np.maximum(2.0, A / nu * (1 - 1 / (A * k) ** 2))
        eps = 2 * c * F ** power / m
        ok0 = (e > 0) & (L >= 2 * (X + Y)) & (f >= 4) & (eps <= e)
        for lw in (range(2, 8) if not bandless else (0,)):
            W = 2.0 ** lw
            if bandless:   # no band: depth S(L); strays exported, leak c F^power; window f >= gfr F
                depth = S(L) + 0 * X
                ok = ok0 & (f >= gfr * F) & (f >= fwin * c * F ** power)   # fwin: fringe covers fwin x ell
            else:
                depth = S(L) + 2 * S(np.ceil(np.log2(4 * F * W)))
                ok = ok0 & (f >= 4 * F * W) & (np.log2(4 * F * W) <= L)
            s = np.where(ok, depth * (X + Y) / (X * Z), np.inf)
            i = np.unravel_index(np.argmin(s), s.shape)
            if s[i] < best[0]:
                best = (float(s[i]), (float(X[i]), float(Y[i]), float(Z[i]), float(L[i]), W, float(F[i]),
                                      float(depth[i])))
    return best


def main():
    args = sys.argv[1:]
    exact = '--exact-fringe' in args
    args = [a for a in args if a != '--exact-fringe']
    power = 1 if '--linear' in sys.argv else 2
    args = [a for a in args if a != '--linear']
    bandless = '--bandless' in args
    args = [a for a in args if a != '--bandless']
    for a in list(args):
        if a.startswith('--power='):
            power = float(a.split('=')[1]); args.remove(a)
    gfr, fwin = 16, 0
    for a in list(args):
        if a.startswith('--fwin='):
            fwin = float(a.split('=')[1]); args.remove(a)
    for a in list(args):
        if a.startswith('--gfr='):
            gfr = float(a.split('=')[1]); args.remove(a)
    cases = [tuple(float(t) for t in a.split(',')) for a in args] or [
        (0.25, 1), (0.25, 2), (1.5, 1), (1.5, 2), (1.5, 4), (6, 2), (6, 4)]
    print(f'bandless: {bandless} (f >= {gfr} F); exact fringe: {exact}; leak power {power}; slope (x y z L W F stage-depth)')
    for c, Fm in cases:
        for regime in ('R1', 'R2c'):
            v, p = min((screen(regime, dF, c, Fm, exact, power=power, bandless=bandless, gfr=gfr, fwin=fwin) for dF in (0.5, 0.75)), key=lambda t: t[0])
            print(f'c={c:<4} F={Fm:g}k {regime:3s}: {v:6.1f}  ' + ('' if p is None else ' '.join(f'{t:.2f}' for t in p)),
                  flush=True)


if __name__ == '__main__':
    main()
