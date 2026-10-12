#!/usr/bin/env python3
r"""Stage-0 gate: the D2 (cut-layout) flow table implemented LITERALLY in N, with rounding.

Exact Python integers / Fractions throughout.  Hash-consed over node classes (as compressed.py):
two bags with equal level, equal state (gL, gH) and equal (recursively) subtrees share a class.

FROZEN RULE (per bag b at level i, time t; state st_t(b) = (gL, gH), G = gL + gH):
  t = 0 : root (0,0); every other bag (0, R_i) with R_i = k^(d-i).
  sender x (active at t, i.e. alpha(t) <= i <= omega(t), i = t mod 2), children l_0..l_{k-1}:
     S_j  = sum_{q<j} G(l_q)            (prefix sums of the children's deficits)
     a    = S_k - G(x)                  (= R - G at a leaf)
     role = topDesc / topRise / mid / botDesc / botRise  (flowsim.Par.role)
     botRise : pi = a, no blocks, st(x) <- (gL, gH + a)   [all wires go up]
     topDesc : pi = 0
     else    : pi0 = Chvatal pi (closed form);   Gam = grain(i, t) (power of 2, see below)
               pi  = pi0 + ((a - pi0) mod Gam)        [pi-adjust: makes a - pi = 0 mod Gam]
     lo   = Gam * floor((gL + pi/2) / Gam)
     hi   = lo + (a - pi)
     cl_j = min(S_{j+1}, lo) - min(S_j, lo)
     ch_j = max(S_{j+1}, hi) - max(S_j, hi)
     down_j = G(l_j) - cl_j - ch_j            (= |[S_j,S_{j+1}) /\ [lo,hi)|)
     st(l_j) <- (cl_j, ch_j);   st(x) <- (lo, S_k - hi)      [G(x) <- G(x) + pi]
  grain(i,t) = 2^max(0, v2(c(i+1,t+1)) - 39)  = 16 * c(i+1,t+1)/2^43   (GRAIN_SHIFT = 39)
  other bags: unchanged.
Geometry (NodeGeomV) for a sender with a > 2^63 and sum down > 0:
     n = 2^(ceil(lg a) - 43), m = a/n, f = pi/(2n); need n | a, n | down_j, 2n | pi,
     f = 0 or (f >= 131040, f even), n >= 16, 2^42 < m <= 2^43.
Options: --nogrid (no rounding, no pi-adjust: reproduces compressed.py D2), --design U.
"""
import sys, math, argparse
from fractions import Fraction as Fr
from flowsim import Par

sys.setrecursionlimit(100000)
EPSF = Fr(1, 86000000)
DF = Fr(128, 4095)
EPSB = Fr(1, 59000000)


def v2(q):
    q = Fr(q)
    n, d = q.numerator, q.denominator
    if n == 0:
        return 10 ** 9
    return ((n & -n).bit_length() - 1) - ((d & -d).bit_length() - 1)


class Cls:
    __slots__ = ('lev', 'gL', 'gH', 'G', 'kids', 'id')


class D2:
    def __init__(s, P, d, design='D2', grid=True, shift=39, L=42, record=None):
        s.P, s.d, s.design, s.grid, s.shift, s.L = P, d, design, grid, shift, L
        s.k = P.k
        s.R = [s.k ** (d - i) for i in range(d + 1)]
        s.intern = {}
        s.nid = 0
        s.record = record          # callback(rec) per sending class
        s.fail = {}                # counters of violated checks
        s.ex = {}                  # first examples
        s.worst = {}
        s.n_senders = 0
        s.n_big = 0

    # ---------- bookkeeping ----------
    def bad(s, key, info):
        s.fail[key] = s.fail.get(key, 0) + 1
        s.ex.setdefault(key, info)

    def upd(s, key, val, info, mode='max'):
        cur = s.worst.get(key)
        if cur is None or (val > cur[0] if mode == 'max' else val < cur[0]):
            s.worst[key] = (val, info)

    def mk(s, lev, gL, gH, kids):
        key = (lev, gL, gH, tuple((c.id, n) for c, n in kids))
        c = s.intern.get(key)
        if c is None:
            c = Cls()
            c.lev, c.gL, c.gH, c.G, c.kids = lev, gL, gH, gL + gH, tuple(kids)
            c.id = s.nid
            s.nid += 1
            s.intern[key] = c
        return c

    def initial(s):
        c = None
        for i in range(s.d, -1, -1):
            kids = () if c is None else ((c, s.k),)
            c = s.mk(i, 0, 0 if i == 0 else s.R[i], kids)
        return c

    def active(s, i, t):
        return (i == 0) if t == 0 else s.P.active(s.d, i, t)

    def grain(s, i, t):
        if not s.grid:
            return 1
        e = v2(s.P.cap(s.d, i + 1, t + 1)) - s.shift
        return 2 ** max(0, e)

    # ---------- one stage ----------
    def step(s, root, t):
        s.t = t
        s.memo_a, s.memo_i = {}, {}
        s.alog = {}
        new = s.visit(root, None)
        # global wire count via multiplicities
        mult = {root.id: 1}
        order = [root]
        j = 0
        seen = {root.id}
        while j < len(order):
            c = order[j]; j += 1
            for kc, n in c.kids:
                mult[kc.id] = mult.get(kc.id, 0) + mult[c.id] * n
                if kc.id not in seen:
                    seen.add(kc.id); order.append(kc)
        tot = sum(mult[cid] * a for cid, a in s.alog.items())
        if tot != s.k ** s.d:
            s.bad('global_count', (t, tot))
        s.last_mult = mult
        return new

    def visit(s, c, recv):
        t = s.t
        if s.active(c.lev, t):
            if recv is not None:
                s.bad('active_child_of_active', (t, c.lev))
            if c.id not in s.memo_a:
                s.memo_a[c.id] = s.send(c)
            return s.memo_a[c.id]
        key = (c.id, recv)
        if key not in s.memo_i:
            gL, gH = c.gL, c.gH
            if recv is not None:
                gL, gH = recv
            kids = tuple((s.visit(kc, None), n) for kc, n in c.kids)
            s.memo_i[key] = s.mk(c.lev, gL, gH, kids)
        return s.memo_i[key]

    def send(s, c):
        P, d, t, k = s.P, s.d, s.t, s.k
        i = c.lev
        role = 'topDesc' if t == 0 else P.role(d, i, t)
        cap = P.cap(d, i, t)
        S = sum(kc.G * n for kc, n in c.kids) if c.kids else 0
        a = (S - c.G) if c.kids else s.R[i] - c.G
        s.alog[c.id] = a
        info = (d, t, i, role)
        if a < 0:
            s.bad('a_neg', info)
        if s.design == 'U' and t >= 1 and a != P.alloc(d, i, t):
            s.bad('U_alloc_mismatch', info + (a, P.alloc(d, i, t)))
        # ---- pi ----
        Gam = 1
        lo = hi = None
        if role == 'botRise' or not c.kids:
            pi = a
        elif role == 'topDesc' or t == 0:
            pi = 0
        else:
            pi0 = P.up(d, i, t)
            if pi0.denominator != 1:
                s.bad('pi0_nonint', info)
            pi0 = int(pi0)
            if s.design == 'D2':
                Gam = s.grain(i, t)
                pi = pi0 + ((a - pi0) % Gam)
            else:
                pi = pi0
        if pi % 2:
            s.bad('pi_odd', info)
        if pi > a:
            s.bad('pi_gt_a', info + (float(Fr(pi, 1) / cap), float(Fr(a) / cap)))
        # ---- blocks ----
        newkids, blocks = [], []          # blocks: list of (G_child, cl, ch, down, run)
        if role == 'botRise' or not c.kids:
            newkids = [(s.visit(kc, None), n) for kc, n in c.kids]
            newst = (c.gL, c.gH + pi)
        else:
            if s.design == 'U' and role != 'topDesc':
                beta = P.down(d, i, t)
                beta = int(beta)
                for kc, n in c.kids:
                    th = kc.G - beta
                    if th < 0:
                        s.bad('U_theta_neg', info)
                    newkids.append((s.visit(kc, (th, 0)), n))
                    blocks.append((kc.G, th, 0, beta, n))
                newst = (c.gL + pi // 2, c.gH + pi - pi // 2)
                lo = hi = None
            else:
                target = c.gL + pi // 2
                lo = Gam * (target // Gam)
                hi = lo + (a - pi)
                if lo < 0 or hi > S or lo > hi:
                    s.bad('cut_out_of_range', info + (lo, hi, S))
                pos = 0
                for kc, n in c.kids:
                    u = kc.G
                    q = 0
                    while q < n:
                        s0 = pos + q * u
                        s1 = s0 + u
                        cl = min(s1, lo) - min(s0, lo)
                        ch = max(s1, hi) - max(s0, hi)
                        b = u - cl - ch
                        if u > 0 and s1 <= lo:
                            run = min(n - q, max(1, (lo - s0) // u))
                        elif u > 0 and s0 >= lo and s1 <= hi:
                            run = min(n - q, max(1, (hi - s0) // u))
                        elif u > 0 and s0 >= hi:
                            run = n - q
                        else:
                            run = 1 if u > 0 else n - q
                        newkids.append((s.visit(kc, (cl, ch)), run))
                        blocks.append((u, cl, ch, b, run))
                        q += run
                    pos += u * n
                newst = (lo, S - hi)
            sb = sum(b * r for _, _, _, b, r in blocks)
            if sb != a - pi:
                s.bad('conservation', info + (sb, a - pi))
            if any(b < 0 for _, _, _, b, _ in blocks):
                s.bad('block_neg', info)
            if sum(r for *_, r in blocks) != k:
                s.bad('kidcount', info)
        if newst[0] + newst[1] != c.G + pi:
            s.bad('G_update', info)
        if newst[0] < 0 or newst[1] < 0:
            s.bad('state_neg', info + newst)
        new = s.mk(i, newst[0], newst[1], tuple(newkids))
        # ---------------- per-sender checks ----------------
        downsum = a - pi if blocks else 0
        if t >= 1:
            s.n_senders += 1
            rec = dict(d=d, t=t, i=i, role=role, a=a, pi=pi, gL=c.gL, gH=c.gH, G=c.G, cap=cap,
                       S=S, blocks=blocks, Gam=Gam, lo=lo, hi=hi, newst=newst, cls=c)
            if downsum > 0:
                s.upd('a/c', Fr(a) / cap, info)
                s.upd('G/c', Fr(c.G) / cap, info)
                res = s.resid(pi, blocks)
                rec['resid'] = res
                s.upd('resid/c', res / cap, info)
                s.upd('(resid-G)/c', (res - c.G) / cap, info)
                s.cond42(rec)
                if a > 2 ** 63:
                    s.n_big += 1
                    s.geom(rec)
            if s.record:
                s.record(rec)
        return new

    def resid(s, pi, blocks):
        """exact max_j residAt over blocks with down_j > 0 (INTERFACE 2.1), run-length aware."""
        # theta_q = G_q - down_q = cl + ch ; T_j = sum_{q<j} theta
        tot = sum((u - b) * r for u, _, _, b, r in blocks)
        best = Fr(0)
        T = 0
        for u, cl, ch, b, r in blocks:
            th = u - b
            if b > 0:
                for jj in (0, r - 1):
                    left = T + jj * th
                    right = tot - left - th
                    v = max(Fr(0), left - Fr(pi, 2)) + max(Fr(0), right - Fr(pi, 2))
                    if v > best:
                        best = v
            T += th * r
        return best

    def geom(s, rec):
        a, pi = rec['a'], rec['pi']
        info = (rec['d'], rec['t'], rec['i'], rec['role'])
        e = (a - 1).bit_length() - 43          # ceil(lg a) - 43
        n = 2 ** e
        m = a // n
        ok = True
        why = []
        if a % n:
            ok = False; why.append('n!|a')
        if pi % (2 * n):
            ok = False; why.append('2n!|pi')
        else:
            f = pi // (2 * n)
            if not (f == 0 or (f >= 131040 and f % 2 == 0)):
                ok = False; why.append(f'f={f}')
            s.upd('f_max', f, info)
            if f > 0:
                s.upd('f_min', f, info, mode='min')
        for _, _, _, b, _ in rec['blocks']:
            if b % n:
                ok = False; why.append('n!|block'); break
        if not (2 ** 42 < m <= 2 ** 43) or n < 16:
            ok = False; why.append('window')
        if a > rec['cap']:
            s.bad('big_a_gt_c (needs fix (a))', info + (float(Fr(a) / rec['cap']),))
        if not ok:
            s.bad('geom', info + tuple(why))

    def cond42(s, rec):
        P = s.P
        k, A, nu = P.k, P.A, P.nu
        if not hasattr(s, 'K42'):
            s.K42 = constants(P)
        K = s.K42
        c = rec['cap']
        rhs = K['mu'] * A * nu * c
        other = K['mu'] * c + (k - 1) * K['mu'] * K['sib'] * c + K['mu'] * K['delta'] * A * A * k * c
        room = rhs - other - rec['resid']
        marg = room / (EPSB * rec['a']) if rec['a'] > 0 else Fr(10 ** 9)
        s.upd('cond42_margin', marg, (rec['d'], rec['t'], rec['i'], rec['role'],
                                       float(rec['resid'] / K['mu'] / c)), mode='min')


def constants(P):
    k, A, nu = P.k, P.A, P.nu
    Anu = A * nu
    mu43 = nu / (A * k * k)
    mu44 = DF * (Anu * k - 1) / (2 * A * A * k * k)
    mu = min(mu43, mu44) * (1 - Fr(1, 1024))
    a2 = A * k / nu
    c0 = EPSF / (A * nu)
    lo = (1 - math.sqrt(float(1 - 4 * a2 * c0))) / (2 * float(a2))
    dl = Fr(math.ceil(lo * 2 ** 60 * (1 + 1e-12)), 2 ** 60)
    while not (c0 + dl * dl * a2 <= dl):
        dl += Fr(1, 2 ** 60)
    sib = dl * k * A * A / (1 - dl ** 2 * k ** 2 * A ** 2)
    return dict(mu=mu, delta=dl, sib=sib, mu43=mu43, mu44=mu44)


def run(P, d, design='D2', grid=True, record=None, final_check=True):
    S = D2(P, d, design, grid, record=record)
    root = S.initial()
    TF = P.tf(d)
    for t in range(TF):
        root = S.step(root, t)
    S.root_final = root
    if final_check:
        lam = P.alpha(d, TF)
        if lam != P.omega(d, TF):
            S.bad('alpha_ne_omega_at_tf', (d, TF))
        # final: every bag at level lam has G = 0 (a = R) and nothing elsewhere
        def walk(c, seen):
            if c.id in seen:
                return
            seen.add(c.id)
            if c.lev < lam and c.G != 0:
                S.bad('final_top_G_nonzero', (d, c.lev, c.G))
            if c.lev == lam:
                Sk = sum(kc.G * n for kc, n in c.kids) if c.kids else 0
                a = (Sk - c.G) if c.kids else S.R[c.lev] - c.G
                if a != S.R[c.lev] or c.G != 0:
                    S.bad('final_a_ne_R', (d, c.lev, a, S.R[c.lev]))
                return
            for kc, _ in c.kids:
                walk(kc, seen)
        walk(root, set())
        S.lam = lam
    return S


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('x', type=int); ap.add_argument('y', type=int); ap.add_argument('z', type=int)
    ap.add_argument('ds', nargs='+')
    ap.add_argument('--design', default='D2')
    ap.add_argument('--nogrid', action='store_true')
    ap.add_argument('--general', action='store_true', help='general schedule even for (6,12,6)')
    a = ap.parse_args()
    lean7 = (a.x, a.y, a.z) == (6, 12, 6) and not a.general
    P = Par(a.x, a.y, a.z, lean7=lean7)
    ds = []
    for tok in a.ds:
        if '-' in tok:
            lo_, hi_ = map(int, tok.split('-')); ds += list(range(lo_, hi_ + 1))
        else:
            ds.append(int(tok))
    K = constants(P)
    print(f'# ({a.x},{a.y},{a.z}) design={a.design} grid={not a.nogrid} mu={float(K["mu"]):.4e} '
          f'delta={float(K["delta"]):.4e} lean7={lean7}')
    for d in ds:
        S = run(P, d, a.design, not a.nogrid)
        w = S.worst
        def g(key, fl=True):
            v = w.get(key)
            return None if v is None else (float(v[0]) if fl else v[0])
        print(f'd={d} tf={P.tf(d)} lam={S.lam} classes={S.nid} senders={S.n_senders} big={S.n_big} '
              f'fails={S.fail} a/c={g("a/c"):.9f} G/c={g("G/c"):.4e} resid/c={g("resid/c"):.4e} '
              f'(resid-G)/c={g("(resid-G)/c"):.3e} cond42margin={g("cond42_margin"):.4f}@{w["cond42_margin"][1]} '
              f'f=[{w.get("f_min",(None,))[0]},{w.get("f_max",(None,))[0]}]')
        if S.ex:
            print('   examples:', {k_: v_ for k_, v_ in list(S.ex.items())[:6]})
        sys.stdout.flush()
