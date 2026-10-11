#!/usr/bin/env python3
"""Run the typed exact simulator for designs U (Chvatal) and D2 (non-uniform) at several (x,y,z),d.
Reports: integrality/conservation checks, worst one-sided Lemma-4.2 residual / c (compare with
slackCoeff), worst a/c, smallest 2-adic valuation gap of the block sizes, worst G/c."""
import sys
from fractions import Fraction as Fr
from flowsim import Par, typed_sim, residual_onesided


def v2(n):
    n = int(n)
    if n == 0:
        return 10 ** 9
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def analyse(P, d, design):
    recs, ch = typed_sim(P, d, design)
    k, A, nu = P.k, P.A, P.nu
    slack = (A * nu * k - 2 * A * nu + 1) / (2 * A ** 2 * k ** 2)
    rstar = Fr(k - 1, 2 * A ** 2 * k ** 2)
    worst_res = Fr(0); worst_at = None
    worst_ac = Fr(0); worst_G = Fr(0)
    worst_vgap = 0
    for (t, i, s), r in recs.items():
        if t < 2 or r['role'] in ('topDesc', 'botRise'):
            continue
        c = r['c']
        res = residual_onesided(P, r) / c
        if res > worst_res:
            worst_res, worst_at = res, (t, i, s, r['role'])
        worst_ac = max(worst_ac, r['a'] / c)
        worst_G = max(worst_G, r['G'] / c)
        # geometry: need n | all row-block sizes with n = a/m ; record v2(a) - min v2(sizes)
        sizes = [r['pi'] / 2] + [b for b in r['blocks'].values()]
        vg = v2(r['a']) - min(v2(x) for x in sizes)
        worst_vgap = max(worst_vgap, vg)
    return dict(checks=ch, res=worst_res, res_at=worst_at, slack=slack, rstar=rstar,
                ac=worst_ac, G=worst_G, vgap=worst_vgap)


if __name__ == '__main__':
    triples = [(6, 12, 6), (6, 10, 6), (6, 9, 6), (6, 8, 6), (6, 7, 6), (6, 7, 5), (5, 7, 5),
               (6, 8, 5)]
    for (x, y, z) in triples:
        P = Par(x, y, z, lean7=(x, y, z) == (6, 12, 6))
        for d in (16, 20, 24):
            for des in ('U', 'D2'):
                R = analyse(P, d, des)
                print(f"({x},{y},{z}) d={d} tf={P.tf(d)} {des}: checks={R['checks']} "
                      f"res/c={float(R['res']):.3e} (slackCoeff={float(R['slack']):.3e}, "
                      f"r*={float(R['rstar']):.3e}) at {R['res_at']}  max a/c={float(R['ac']):.6f} "
                      f"max G/c={float(R['G']):.3e} v2gap={R['vgap']}")
        sys.stdout.flush()
