#!/usr/bin/env python3
"""Exact flow simulation of the sided, centred design (INDUCTION.md; REVIEW-centring.md items 2 and 4).

Schedule and roles: Chvatal's (../slackfree/flowsim.py), as in ../../best/notes/sub800/designP_sim.py.
Per node class: deficit G = R - W split as G = G_L + G_H (low / high ancestral-side deficits).
Design C (mid, botDesc, topRise senders; topDesc: theta = 0; botRise: no blocks):
  theta_first = pi/2 + G_L + o,  theta_last = pi/2 + G_H - o,  interior theta = 0,
  first child (G_L', G_H') = (theta_first, 0), last child = (0, theta_last), interior (0, 0);
  sender afterwards: G_L += pi/2, G_H += pi/2.
  o = OFRAC * c (design constant per capacity; default the centred w/2 ~ mu A nu / (2 (A nu - 1))).
Records, per role: negative blocks, max a/c (eta), max G/c, and the crossing-distance margin
  min (X_1 - pi/2)/a  with X_1 = G_first_child - G_L(sender)  (own child-1 keys held; REVIEW issue 1 needs
  X_1 - pi/2 to be a sizeable fraction of a so that the F1|B1 crossings that matter are far in rank).
Usage:  python -I width_sim.py X Y Z D [D ...]   (env EPSB, Q, DELTA, OFRAC; SPILL on by default)
Width certificate (REVIEW-v5 item B): each class carries the half-width of its N_L interval
(relative to its capacity); per sender the order-0 ratio intruders/(mu c_child) must be <= 1.
"""
import os
import sys
import math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "slackfree"))
sys.path.insert(0, HERE)
from flowsim import Par  # noqa: E402

sys.setrecursionlimit(10000)
SPILL = os.environ.get('SPILL', '1') == '1'
TYPEMID = os.environ.get('TYPEMID', '0') == '1'


class Cls:
    __slots__ = ("lev", "G", "GL", "kids", "hw", "cent", "pinfo")

    def __init__(s, lev, G, GL, kids, hw=0.0, cent=None, pinfo=None):
        s.lev, s.G, s.GL, s.kids, s.hw, s.cent, s.pinfo = lev, Fr(G), Fr(GL), kids, hw, cent, pinfo


class Sim:
    def __init__(s, P, d, ofrac, epsB=2e-5, q=24, delta=2e-6, mu=None):
        s.P, s.d, s.k, s.ofrac = P, d, P.k, ofrac
        s.epsB, s.q, s.delta = epsB, q, delta
        s.A2 = float(P.A) ** 2 if hasattr(P, "A") else 0.0
        s.Anu = None
        s.mu = mu
        s._tail = {}
        s.configs = set()
        s.box = {}
        s.tagdata, s.trans = {}, {}
        s.R = [s.k ** (d - i) for i in range(d + 1)]
        s.intern = {}
        s.stats = {}

    def tail(s, dist):
        ct = os.environ.get("CERT_TAIL")             # certified tail at margin >= CERT_TAIL_W rows (monotone in W)
        if ct is not None:
            if dist * 2.0 ** s.q >= float(os.environ.get("CERT_TAIL_W", "131072")):
                return float(ct)
            return 1e9                               # forces Property B in cross() via the caller below
        key = round(dist, 3)
        if key not in s._tail:
            import screen as Sc
            s._tail[key] = Sc.tail_frac(s.q, max(key, 1e-6) * 2.0 ** s.q)
        return s._tail[key]

    def note(s, role, key, val, better):
        r = s.stats.setdefault(role, {})
        if key not in r or better(val, r[key][0]):
            r[key] = (val, (s.t,))

    def mk(s, lev, G, GL, kids, hw=0.0, cent=None, pinfo=None):
        hw = math.ceil(hw * 1e7) / 1e7          # quantise upward (relative half-width)
        if cent is not None:
            cent = round(cent * 1e6) / 1e6      # centre: design constant per class (rounding moves it inside hw slack)
        if pinfo is not None:
            pinfo = (pinfo[0], math.ceil(pinfo[1] * 1e4) / 1e4, math.ceil(pinfo[2] * 1e8) / 1e8)
        key = (lev, G, GL, hw, cent, pinfo, tuple((id(c), n) for c, n in kids))
        c = s.intern.get(key)
        if c is None:
            c = Cls(lev, G, GL, tuple(kids), hw, cent, pinfo)
            s.intern[key] = c
        return c

    def initial(s):
        c = None
        for i in range(s.d, -1, -1):
            kids = () if c is None else ((c, s.k),)
            G = 0 if i == 0 else s.R[i]
            c = s.mk(i, G, Fr(G, 2), kids)
        return c

    def active(s, i):
        return (i == 0) if s.t == 0 else s.P.active(s.d, i, s.t)

    def step(s, root, t):
        s.t, s.memo_a, s.memo_i = t, {}, {}
        return s.visit(root, None, None)

    def visit(s, c, newG, newGL, newhw=None, newcent=None, newpinfo=None):
        if s.active(c.lev):
            if id(c) not in s.memo_a:
                s.memo_a[id(c)] = s.send(c)
            return s.memo_a[id(c)]
        key = (id(c), newG, newGL, newhw, newcent, newpinfo)
        if key not in s.memo_i:
            G = c.G if newG is None else newG
            GL = c.GL if newGL is None else newGL
            hw = c.hw if newhw is None else newhw
            cent = c.cent if newcent is None else newcent
            pinfo = c.pinfo if newpinfo is None else newpinfo
            kids = tuple((s.visit(kc, None, None), n) for kc, n in c.kids)
            s.memo_i[key] = s.mk(c.lev, G, GL, kids, hw, cent, pinfo)
        return s.memo_i[key]

    def send(s, c):
        P, d, t, k = s.P, s.d, s.t, s.k
        i = c.lev
        role = "topDesc" if t == 0 else P.role(d, i, t)
        a = sum(kc.G * n for kc, n in c.kids) - c.G if c.kids else s.R[i] - c.G
        cap = P.cap(d, i, t)
        pi = a if role == "botRise" else (Fr(0) if t == 0 else P.up(d, i, t))
        GL, GH = c.GL, c.G - c.GL
        if role == "botRise" or not c.kids:
            kids = tuple((s.visit(kc, None, None), n) for kc, n in c.kids)
            return s.mk(i, c.G + pi, GL + pi / 2, kids)
        flat = [[kc, n] for kc, n in c.kids]
        first, last = flat[0][0], flat[-1][0]
        if role == "topDesc":
            thetas = [(kc, n, Fr(0), Fr(0)) for kc, n in flat]
        else:
            o = (Fr(c.cent).limit_denominator(10 ** 9) * cap) if (TYPEMID and c.cent is not None) else s.ofrac * cap
            tf = pi / 2 + GL + o
            tl = pi / 2 + GH - o
            mid = []
            for idx, (kc, n) in enumerate(flat):
                cnt = n - (1 if idx == 0 else 0) - (1 if idx == len(flat) - 1 else 0)
                mid += [(kc, 1, Fr(0), Fr(0))] * cnt
            thetas = [(first, 1, tf, tf)] + mid + [(last, 1, tl, Fr(0))]
            if SPILL:
                # spill rule: low deficit fills children from the low end, high deficit from the high end,
                # each child's theta capped at its own deficit G (its keys held outside its subtree + here)
                seq = [first] + [m_[0] for m_ in mid] + [last]
                caps = [kc.G for kc in seq]
                th = [Fr(0)] * len(seq)
                low, high = tf, tl
                for j in range(len(seq)):
                    take = min(low, caps[j]); th[j] += take; low -= take
                    if low == 0:
                        break
                for j in range(len(seq) - 1, -1, -1):
                    take = min(high, caps[j] - th[j]); th[j] += take; high -= take
                    if high == 0:
                        break
                assert low == 0 and high == 0, (t, i, role)
                spilled = sum(1 for j in range(1, len(seq) - 1) if th[j] > 0)
                if spilled:
                    s.note(role, "spill_children_max", spilled, lambda v, w: v > w)
                    s.note(role, "spill_a_over_c_max", a / cap, lambda v, w: v > w)
                thetas = [(seq[j], 1, th[j], th[j] if j < len(seq) // 2 else Fr(0)) for j in range(len(seq))]
            if t >= 1:
                X1 = first.G - GL
                s.note(role, "cross_margin_min", (X1 - pi / 2) / a, lambda v, w: v < w)
        # ---- width certificate (REVIEW-v5 item B): per-node intruders vs the child's order-0 budget ----
        kidhw = {}
        if role != "topDesc" and t >= 1:
            fa, fc_ = float(a), float(cap)
            cc = float(P.cap(d, i + 1, t + 1)) if i + 1 <= d else fc_ * float(s.Anu)
            h = c.hw * fc_
            D1 = s.mu * s.delta * k * s.A2 * fc_ / (1 - (s.delta * k) ** 2 * s.A2)
            intr = h + k * D1 / 2 + s.mu * s.delta * s.A2 * k * fc_ + s.epsB * fa + float(os.environ.get("ROUNDF", "0.1")) * s.mu * cc
            s.note(role, "order0_ratio_max", intr / (s.mu * cc), lambda v, w: v > w)
            if os.environ.get("TRANS"):
                tag = role if role != "botDesc" else "bD%d" % round(math.log2(max(fa / fc_, 1e-12)))
                if os.environ.get("TRANS_LOCBIN") and c.pinfo is not None:   # split by incoming local term
                    tag += "|L%d" % round(c.pinfo[2] / s.mu * 50)
                td = s.tagdata.setdefault(tag, dict(rf=0.0, e=0.0, D=0.0))
                td["rf"] = max(td["rf"], fc_ / (s.mu * cc))          # ratio = hw_rel * c / (mu c') + ...
                td["e"] = max(td["e"], s.epsB * fa / (s.mu * cc))
                td["D"] = max(td["D"], (k * D1 / 2 + s.mu * s.delta * s.A2 * k * fc_) / (s.mu * cc))
                if c.pinfo is not None:
                    key2 = (c.pinfo[0], tag)
                    cf, lc = s.trans.get(key2, (0.0, 0.0))
                    s.trans[key2] = (max(cf, c.pinfo[1]), max(lc, c.pinfo[2]))
                s.curtag = tag
            if os.environ.get("BOXTERMS"):
                terms = dict(h=h / (s.mu * cc), D=(k * D1 / 2 + s.mu * s.delta * s.A2 * k * fc_) / (s.mu * cc),
                             e=s.epsB * fa / (s.mu * cc))
                rk = role if role != "botDesc" else "botDesc a/c~2^%d" % round(math.log2(max(fa / fc_, 1e-12)))
                bx = s.box.setdefault(rk, {})
                for kk, vv in terms.items():
                    bx[kk] = max(bx.get(kk, 0.0), vv)
            if os.environ.get("CONFIGS"):
                s.configs.add((role, round(fa / fc_, 9), round(float(pi) / fc_, 9), round(float(c.G) / fc_, 9),
                               round(float(GL) / fc_, 9), round(cc / fc_, 6)))
            # REVIEW-v6 issue 1: keys of range(w_1') in u's bag = G(w_1') - G_L(u) (not G_L(w) - G_L(u))
            g11 = first.kids[0][0].G if first.kids else first.GL
            Y = max(0.0, float(g11 - GL))
            b1 = float(first.G - thetas[0][2])
            dB = (Y - float(pi) / 2) / fa
            dL = (b1 + float(pi) / 2 - Y) / fa
            bandw = float(os.environ.get("BAND2W_FRAC", "0"))      # band repair: margin shrinks by 2W/m (L3 step 4)
            def cross(dist):
                if dist - bandw >= 0.005:
                    return min(s.tail(dist - bandw) * fa, s.epsB * fa / 2)
                return s.epsB * fa / 2
            cB, cL = cross(dB), cross(dL)
            s.note(role, "dist_min", min(dB, dL), lambda v, w: v < w)
            hw_end = (s.mu * cc + 2 * h + cB + cL) / 2 / cc
            hw_int = (s.mu * cc + h + s.epsB * fa / 2 + k * D1 / 2) / 2 / cc
            hw_spill = (s.mu * cc + 2 * h + s.epsB * fa) / 2 / cc
            kidcent = {}
            s.kidpinfo = {}
            ptag = getattr(s, "curtag", None)
            for j, (kc, n, th, thL) in enumerate(thetas):
                if ptag is not None:
                    if j == 0 or j == len(thetas) - 1:
                        s.kidpinfo[j] = (ptag, fc_ / cc, (cB + cL) / (2 * cc))
                    elif th > 0:
                        s.kidpinfo[j] = (ptag, fc_ / cc, s.epsB * fa / (2 * cc))
                    else:
                        s.kidpinfo[j] = (ptag, fc_ / (2 * cc), (s.epsB * fa / 2 + k * D1 / 2) / (2 * cc))
                if j == 0 or j == len(thetas) - 1:
                    kidhw[j] = hw_end
                    kidcent[j] = (s.mu * cc + cB - cL) / 2 / cc
                elif th > 0:
                    kidhw[j] = hw_spill
                    kidcent[j] = s.mu / 2
                else:
                    kidhw[j] = hw_int
                    kidcent[j] = (s.mu * cc - (h + s.epsB * fa / 2 + k * D1 / 2)) / 2 / cc
            s.kidcent = kidcent
        elif role == "topDesc":
            if t >= 1:   # REVIEW-v6: topDesc sends at t >= 1 (no outsiders, exact X): intruders = crossings
                ccx = float(P.cap(d, i + 1, t + 1)) if i + 1 <= d else float(cap) * float(s.Anu)
                rnd = float(os.environ.get("ROUNDF", "0.1"))
                s.note(role, "order0_ratio_max", (s.epsB * float(a) + rnd * s.mu * ccx) / (s.mu * ccx), lambda v, w: v > w)
            # topDesc senders hold no outsiders and have exact X (R1 sec. 4): children's N_L comes only from the
            # sender's separator crossings at their cuts, |N_L| <= eps_B a/2, centred (type-specific midpoint)
            cc = float(P.cap(d, i + 1, t + 1)) if i + 1 <= d else float(cap) * float(s.Anu)
            # oversized topDesc senders (the root in the early oscillation phase) use the precise root
            # separator of R1 (4.1), eps_* <= mu/k; Lemma 3.2 makes every other topDesc node small
            eps_td = float(s.mu) / k if float(a) > cc else s.epsB
            for j in range(len(thetas)):
                kidhw[j] = eps_td * float(a) / 2 / cc
            s.kidcent = {j: 0.0 for j in range(len(thetas))}
        kc_cent = getattr(s, "kidcent", {}) if kidhw else {}
        kc_pinfo = getattr(s, "kidpinfo", {}) if kidhw else {}
        s.kidcent = {}
        s.kidpinfo = {}
        s.curtag = None
        T = Fr(0)
        newkids = []
        for j, (kc, n, th, thL) in enumerate(thetas):
            b = kc.G - th
            if b < 0:
                s.note(role, "neg_block_min", b / cap, lambda v, w: v < w)
            T += n * th
            newkids.append((s.visit(kc, th, thL, kidhw.get(j), kc_cent.get(j), kc_pinfo.get(j)), n))
        assert T == pi + c.G or role == "topDesc"
        if t >= 1:
            s.note(role, "a_over_c_max", a / cap, lambda v, w: v > w)
            s.note(role, "G_over_c_max", c.G / cap, lambda v, w: v > w)
        merged = []
        for kc, n in newkids:
            if merged and merged[-1][0] is kc:
                merged[-1] = (kc, merged[-1][1] + n)
            else:
                merged.append((kc, n))
        return s.mk(i, c.G + pi, GL + pi / 2, tuple(merged))


def main():
    x, y, z = map(int, sys.argv[1:4])
    k, A, nu = 2 ** x, 2 ** y, Fr(1, 2 ** z)
    Anu = A * nu
    dF = Fr(1, 8)
    mu = (1 - Fr(1, 1024)) * min(nu / (A * k * k), dF * (Anu * k - 1) / (2 * A * A * k * k))
    ofrac = Fr(os.environ["OFRAC"]) if "OFRAC" in os.environ else mu * Anu / (2 * (Anu - 1))
    epsB = float(os.environ.get("EPSB", "2e-5"))
    q = int(os.environ.get("Q", "24"))
    delta = float(os.environ.get("DELTA", "2e-6"))
    for d in map(int, sys.argv[4:]):
        P = Par(x, y, z)
        S = Sim(P, d, ofrac, epsB, q, delta, float(mu))
        S.A2 = float(A) ** 2
        S.Anu = Anu
        root = S.initial()
        for t in range(P.tf(d)):
            root = S.step(root, t)
        print(f"({x},{y},{z}) d={d} tf={P.tf(d)} o/c={float(ofrac):.3e} classes={len(S.intern)} local_configs={len(S.configs)}")
        if os.environ.get("TRANS"):
            rnd = float(os.environ.get("ROUNDF", "0.1"))
            mu_ = float(mu)
            hwb = {tg: 0.0 for tg in S.tagdata}
            for _ in range(200):          # box recursion: hw[tag] = max over p->tag of mu/2 + coef hw[p] + loc
                new = {}
                for (pt, tg), (cf, lc) in S.trans.items():
                    if tg in hwb:
                        v = mu_ / 2 + cf * hwb.get(pt, mu_) + lc
                        new[tg] = max(new.get(tg, 0.0), v)
                for tg in hwb:
                    hwb[tg] = max(hwb[tg], new.get(tg, mu_ / 2))
            worst = 0.0
            for tg, td in sorted(S.tagdata.items()):
                rb = hwb[tg] * td["rf"] + td["D"] + td["e"] + rnd
                worst = max(worst, rb)
                print("   transbox %-6s hw <= %.3f mu  ratio bound %.4f" % (tg, hwb[tg] / mu_, rb))
            print("   transbox worst ratio bound %.4f (transitions %d)" % (worst, len(S.trans)))
            if os.environ.get("TRANS_DUMP"):
                import json
                json.dump(dict(mu=str(mu), round=os.environ.get("ROUNDF", "0.1"),
                               tags={tg: td for tg, td in S.tagdata.items()},
                               trans=[[pt, tg, cf, lc] for (pt, tg), (cf, lc) in S.trans.items()]),
                          open(os.environ["TRANS_DUMP"], "w"), indent=1)
        if os.environ.get("BOXTERMS"):
            rnd = float(os.environ.get("ROUNDF", "0.1"))
            for role, bx in sorted(S.box.items()):
                print("   box %-8s %s  -> sum of maxima + ROUND = %.4f" % (role, {kk: round(vv, 4) for kk, vv in bx.items()}, sum(bx.values()) + rnd))
        if os.environ.get("CONFIGS"):
            import pickle
            pickle.dump(S.configs, open(f"configs_d{d}.pkl", "wb"))
        for role, r in sorted(S.stats.items()):
            print("   %-8s %s" % (role, {kk: (round(float(v[0]), 6), v[1]) for kk, v in r.items()}))


if __name__ == "__main__":
    main()
