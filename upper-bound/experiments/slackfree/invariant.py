#!/usr/bin/env python3
"""Stage-0 gate, part 2: the scale-free finite-role invariant for the rounded D2 table (d2lean.py),
checked (a) symbolically in exact rationals for every schedule signature that occurs for
d = 14..DMAX, and (b) against the exact integer tables of d2lean.py.

All quantities are divided by c = c(i,t) of the bag in question.  Ratios used:
  c(i+1,t-1)/c(i,t) = A/nu,   c(i,t-2)/c(i,t) = nu^-2,   c(i-1,t-1)/c(i,t) = 1/(A nu),
  R_i/c(i,t) = 2^e,  e = (x+y-z) - (x+y) i + z t      (the only non-homogeneous datum: an exponent)
  p   = pi0/c at mid / botDesc  = (A nu k - 1)/(A^2 k^2)
  pT  = pi0/c at topRise        = nu/(A k)
  gam = Gam/c = (A nu)/2^39     (rounding grain of a sender, relative to its own c)

INVARIANT  (induction on t; every line is one linear inequality in rationals):
  (J)  every non-top bag y with y.l = t mod 2, alpha(t) < y.l <= omega(t):
         min(gL,gH) = 0 and h := max(gL,gH) <= gs * c(y.l,t);   top bags (y.l <= alpha(t)): G = 0.
       step:  h_y(t) <= h_p(t-1) + pi'_p/2 + Gam_p  and  pi'_p < pi0_p + Gam_p, hence
         (J-mid)  gs*(A nu) >= gs + p/2 + 3/2 gam        (parent mid/botDesc)
         (J-top)  gs*(A nu) >= pT/2 + 3/2 gam             (parent topRise, h_p = 0)
       and "min = 0" needs NO SPANNING at the parent (NS below).
  (A)  a-interval per signature (formula below), and for senders with blocks:
         a >= pi0 + Gam            (lo <= hi, hence b_j >= 0 via (L1))
         a - pi0 - Gam >= Gmax_child   (NS: no child interval contains [lo,hi))
         a <= eta * c
  (R)  residAt <= h + Gam <= (gs + gam) c =: rT c.
a-formulas (exact identities, generic lemmas):
  bottom sender (i = omega(t)):       a = R_i - G_x(t)          (all children subtrees empty, L2)
  children botRise/below at t-1:      a = R_i - G_x(t)
  otherwise                           a = [G_x(t-2) + pi'_x(t-2)]_{x cut at t-2} + sum_l pi'_l(t-1) - G_x(t)
"""
import sys
from fractions import Fraction as Fr
from collections import defaultdict
from flowsim import Par

CUTTERS = ('root', 'topDesc', 'topRise', 'mid', 'botDesc')


def consts(P):
    k, A, nu = P.k, P.A, P.nu
    Anu = A * nu
    p = (Anu * k - 1) / Fr(A * A * k * k)
    pT = nu / (A * k)
    gam = Anu / Fr(2 ** 39)
    gs = max((p / 2 + Fr(3, 2) * gam) / (Anu - 1), (pT / 2 + Fr(3, 2) * gam) / Anu)
    return dict(k=k, A=A, nu=nu, Anu=Anu, p=p, pT=pT, gam=gam, gs=gs, rT=gs + gam)


def roleat(P, d, i, t):
    if t < 0:
        return 'pre'
    if t == 0:
        return 'root' if i == 0 else 'below'
    if t > P.tf(d):
        return 'post'
    a, w = P.alpha(d, t), P.omega(d, t)
    if i < a:
        return 'above'
    if i > w:
        return 'below'
    if i % 2 != t % 2:
        return 'off'
    if t == P.tf(d):
        return 'final'
    return P.role(d, i, t)


def pi0r(K, role):
    """(pi0/c, has rounding adjust) for a sender of this role."""
    if role in ('mid', 'botDesc'):
        return K['p'], True
    if role == 'topRise':
        return K['pT'], True
    return Fr(0), False


def gmax(K, role):
    return Fr(0) if role in ('root', 'topDesc', 'topRise') else K['gs']


def signature(P, d, i, t):
    return (roleat(P, d, i, t), roleat(P, d, i, t - 2), roleat(P, d, i + 1, t - 1),
            roleat(P, d, i - 1, t - 1))


def e_of(P, i, t):
    return (P.x + P.y - P.z) - (P.x + P.y) * i + P.z * t


def a_interval(P, K, sig, e):
    """[a_lo, a_hi]/c and Gmax_child/c from the signature (formulas only)."""
    r, r2, rc, rp = sig
    nu, A = K['nu'], K['A']
    Gx_hi = gmax(K, r)
    if r in ('botDesc', 'botRise') or rc in ('botRise', 'below'):
        R = Fr(2) ** e
        return R - Gx_hi, R, Fr(2) ** (e - P.x), 'R-G'
    lo = hi = Fr(0)
    if r2 in CUTTERS:
        ratio = nu ** -2
        p2, adj = pi0r(K, r2)
        lo += p2 * ratio
        hi += (gmax(K, r2) + p2 + (K['gam'] if adj else 0)) * ratio
    elif r2 != 'above':
        return None, None, None, f'UNHANDLED t-2 role {r2}'
    if rc in ('topRise', 'mid', 'botDesc'):
        pc, adj = pi0r(K, rc)
        ratio = A / nu
        lo += P.k * pc * ratio
        hi += P.k * (pc + (K['gam'] if adj else 0)) * ratio
        Gch = (gmax(K, rc) + pc + K['gam']) * ratio      # child's G(t) <= h(t-1) + pi'(t-1)
    else:
        return None, None, None, f'UNHANDLED child role {rc}'
    return lo - Gx_hi, hi, Gch, 'C1'


def symbolic(P, K, dmin, dmax):
    sigs = {}
    fails = []
    for d in range(dmin, dmax + 1):
        TF = P.tf(d)
        for t in range(1, TF):
            for i in range(P.alpha(d, t), P.omega(d, t) + 1):
                if i % 2 != t % 2:
                    continue
                sig = signature(P, d, i, t)
                e = e_of(P, i, t)
                key = sig + ((e,) if (sig[0].startswith('bot') or sig[2] == 'botRise') else ())
                if key in sigs:
                    sigs[key][1] += 1
                    continue
                lo, hi, Gch, how = a_interval(P, K, sig, e)
                rec = dict(how=how, lo=lo, hi=hi, Gch=Gch, ok=True, why=[])
                if lo is None:
                    rec['ok'] = False; rec['why'].append(how)
                else:
                    r = sig[0]
                    pi0, adj = pi0r(K, r)
                    G = K['gam'] if adj else Fr(0)
                    if r in ('topRise', 'mid', 'botDesc'):
                        if not lo >= pi0 + G:
                            rec['ok'] = False; rec['why'].append('a<pi')
                        if not lo - pi0 - G >= Gch:
                            rec['ok'] = False; rec['why'].append('spanning possible')
                    if r == 'botRise' and lo < -K['gs']:
                        pass   # botRise: a = R - G >= 0 holds since G <= R (W >= 0)
                    rec['eta'] = hi
                sigs[key] = [rec, 1, d]
                if not rec['ok']:
                    fails.append((key, d, t, i, rec['why']))
    return sigs, fails


def data_check(P, K, ds, eta):
    from d2lean import run
    bad = defaultdict(int)
    ex = {}
    worst = dict(h=Fr(0), res=Fr(0), a=Fr(0))
    nrec = 0

    def chk(rec):
        nonlocal nrec
        nrec += 1
        d, t, i = rec['d'], rec['t'], rec['i']
        c = rec['cap']
        sig = signature(P, d, i, t)
        lo, hi, Gch, how = a_interval(P, K, sig, e_of(P, i, t))
        a = Fr(rec['a']) / c
        def b(key, info):
            bad[key] += 1; ex.setdefault(key, info)
        if lo is None:
            b('unhandled', sig); return
        if not (lo <= a <= hi):
            b('a_outside_formula_interval', (d, t, i, sig, float(a), float(lo), float(hi)))
        if a > eta:
            b('a>eta', (d, t, i))
        gL, gH = rec['gL'], rec['gH']
        top = sig[0] in ('topDesc', 'topRise')
        if top and (gL or gH):
            b('top_G_nonzero', (d, t, i))
        if not top:
            if min(gL, gH) != 0:
                b('min(gL,gH)!=0', (d, t, i, sig))
            h = Fr(max(gL, gH)) / c
            worst['h'] = max(worst['h'], h)
            if h > K['gs']:
                b('h>gs', (d, t, i, float(h)))
        if 'resid' in rec:
            r = rec['resid'] / c
            worst['res'] = max(worst['res'], r)
            if r > K['rT']:
                b('resid>rT', (d, t, i))
        worst['a'] = max(worst['a'], a)
        # no spanning child
        for u, cl, ch, bb, run_ in rec['blocks']:
            if cl > 0 and ch > 0:
                b('spanning', (d, t, i)); break
    for d in ds:
        run(P, d, 'D2', record=chk)
    return nrec, dict(bad), ex, worst


def cond42_margin(P, K, eta):
    from d2lean import constants, EPSB
    C = constants(P)
    k, A, nu = P.k, P.A, P.nu
    mu, sib, dl = C['mu'], C['sib'], C['delta']
    room = mu * A * nu - mu - (k - 1) * mu * sib - mu * dl * A * A * k - K['rT']
    return room / (EPSB * eta), C


if __name__ == '__main__':
    x, y, z = map(int, sys.argv[1:4])
    dmax = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    dlo, dhi = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (14, 60)
    P = Par(x, y, z, lean7=((x, y, z) == (6, 12, 6)))
    K = consts(P)
    print(f'# ({x},{y},{z})  p={float(K["p"]):.6e} pT={float(K["pT"]):.6e} gam={float(K["gam"]):.4e}')
    print(f'#   gs = {K["gs"]} = {float(K["gs"]):.6e}   rT = gs+gam = {float(K["rT"]):.6e}')
    jm = K['gs'] * K['Anu'] - (K['gs'] + K['p'] / 2 + Fr(3, 2) * K['gam'])
    jt = K['gs'] * K['Anu'] - (K['pT'] / 2 + Fr(3, 2) * K['gam'])
    print(f'#   (J-mid) slack = {float(jm):.3e} >= 0 : {jm >= 0};  (J-top) slack = {float(jt):.3e} >= 0 : {jt >= 0}')
    sigs, fails = symbolic(P, K, 14, dmax)
    eta = max(rec[0]['eta'] for rec in sigs.values() if rec[0]['ok'])
    print(f'# symbolic: {len(sigs)} (signature[,exponent]) classes over d=14..{dmax}; failures: {len(fails)}')
    for key, (rec, n, dfirst) in sorted(sigs.items(), key=lambda kv: str(kv[0])):
        if rec['lo'] is None:
            print(f'   {key}: {rec["why"]}')
            continue
        print(f'   {str(key):70s} n={n:6d} first d={dfirst:3d} {rec["how"]:4s} '
              f'a/c in [{float(rec["lo"]):.6e}, {float(rec["hi"]):.9f}] '
              f'Gchild<={float(rec["Gch"]):.3e} {"OK" if rec["ok"] else rec["why"]}')
    for f in fails[:10]:
        print('   FAIL', f)
    # d-independence: classes first seen only at small d
    print(f'#   max first-d of any class: {max(v[2] for v in sigs.values())}')
    print(f'#   eta (max formula a/c) = {float(eta):.9f}')
    m, C = cond42_margin(P, K, eta)
    print(f'#   cond (4.2) with rT, eta (formula bounds), eps_B=1/59e6: margin = {float(m):.4f}  '
          f'(rT = {float(K["rT"]/C["mu"]):.4f} mu)')
    nrec, bad, ex, worst = data_check(P, K, range(dlo, dhi + 1), eta)
    print(f'# data check d={dlo}..{dhi}: {nrec} sender records; violations: {bad}')
    for k_, v in ex.items():
        print('   ex', k_, v)
    print(f'#   data max h/c={float(worst["h"]):.6e} (gs {float(K["gs"]):.6e}), '
          f'resid/c={float(worst["res"]):.6e} (rT {float(K["rT"]):.6e}), a/c={float(worst["a"]):.9f}')
