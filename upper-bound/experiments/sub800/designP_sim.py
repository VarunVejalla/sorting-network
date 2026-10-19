#!/usr/bin/env python3
"""Hash-consed exact simulation of the one-sided optimal flow table ('design P', SLACKFREE.md sec. 3)
at general (x, y, z), using the schedule of ../slackfree/flowsim.py (Chvatal's alpha/omega envelopes).

State: per node the deficit G = R - W (keys of its range outside its subtree).  An active sender x
with children deficits U_l (= G_l), capacity c and up-flow pi sends b_l = U_l - theta_l to child l,
with sum theta = pi + G_x; afterwards G_l := theta_l, G_x := G_x + pi  (exact bookkeeping, SLACKFREE sec. 2).

Design P (real-valued):  theta_end = pi/2 + G_x - r c (first and last child),
                          theta_int = (2 r c - G_x)/(k - 2),       r = (k-1)/(2 A^2 k^2).
Per sender we record: negative blocks, one-sided residual max_l (L_l^+ + R_l^+)/c with
L_l = T_{l-1} - pi/2, R_l = pi/2 + G_x - T_l (T = prefix sums of theta), G/c and a/c.

Usage:  python -I designP_sim.py X Y Z D [D ...]
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "slackfree"))
from flowsim import Par  # noqa: E402

sys.setrecursionlimit(10000)
T_MIN = int(os.environ.get("T_MIN", "1"))   # record senders from this stage on
GEOM_CUT = int(os.environ.get("GEOM_CUT", "45"))    # senders above 2^GEOM_CUT use the scramble separator
GEOM_M = int(os.environ.get("GEOM_M", str(2 ** 26 - 2 ** 20)))     # target rows M
ROWS_Q = int(os.environ.get("ROWS_Q", "26"))
ROWS_LO = float(os.environ.get("ROWS_LO", "25.6"))
F_CLASSES = [int(v) for v in os.environ.get("F_CLASSES", ",".join(str(round(7934 * 1.3 ** j)) for j in range(18))).split(",")]
DELTA_F = Fr(os.environ.get("DELTA_F", "1/8"))
MU = (1 - Fr(1, 1024)) * Fr(os.environ.get("MU44", "63/4194304"))   # (1-2^-10) mu44 at (16, 32, 1/8)


def divisors_upto(g, top):
    """divisors n of g with n >= 1 and n <= top... (all divisors; g = odd * 2^v, odd part small)."""
    v = 0
    o = g
    while o % 2 == 0:
        o //= 2
        v += 1
    odd = [q for q in range(1, int(o ** 0.5) + 1) if o % q == 0]
    odd = sorted(set(odd + [o // q for q in odd]))
    for q in odd:
        for j in range(v + 1):
            yield q * 2 ** j


class Cls:
    __slots__ = ("lev", "G", "kids")

    def __init__(s, lev, G, kids):
        s.lev, s.G, s.kids = lev, Fr(G), kids


class Sim:
    def __init__(s, P, d, design="P"):
        s.P, s.d, s.k, s.design = P, d, P.k, design
        s.R = [s.k ** (d - i) for i in range(d + 1)]
        s.intern = {}
        s.r = Fr(s.k - 1, 2 * P.A ** 2 * s.k ** 2)
        s.stats = dict(neg=0, senders=0, maxclasses=0, cons=0)
        s.worst = dict(res=Fr(0), G=Fr(0), ac=Fr(0), negmin=Fr(0))
        s.where = {}
        s.geom, s.fvals, s.geom_bad, s.ratios = {}, set(), [], {}

    def mk(s, lev, G, kids):
        key = (lev, G, tuple((id(c), n) for c, n in kids))
        c = s.intern.get(key)
        if c is None:
            c = Cls(lev, G, tuple(kids))
            s.intern[key] = c
        return c

    def initial(s):
        c = None
        for i in range(s.d, -1, -1):
            kids = () if c is None else ((c, s.k),)
            c = s.mk(i, 0 if i == 0 else s.R[i], kids)
        return c

    def active(s, i):
        return (i == 0) if s.t == 0 else s.P.active(s.d, i, s.t)

    def step(s, root, t):
        s.t, s.memo_a, s.memo_i, s.wires = t, {}, {}, 0
        new = s.visit(root, None, 1)
        return new

    def visit(s, c, newG, mult):
        if s.active(c.lev):
            key = id(c)
            if key not in s.memo_a:
                s.memo_a[key] = s.send(c)
            return s.memo_a[key]
        key = (id(c), newG)
        if key not in s.memo_i:
            G = c.G if newG is None else newG
            kids = tuple((s.visit(kc, None, 0), n) for kc, n in c.kids)
            s.memo_i[key] = s.mk(c.lev, G, kids)
        return s.memo_i[key]

    def send(s, c):
        P, d, t, k = s.P, s.d, s.t, s.k
        i = c.lev
        role = "topDesc" if t == 0 else P.role(d, i, t)
        a = sum(kc.G * n for kc, n in c.kids) - c.G if c.kids else s.R[i] - c.G
        cap = P.cap(d, i, t)
        if role == "botRise":
            pi = a
        elif t == 0:
            pi = Fr(0)
        else:
            pi = P.up(d, i, t)
        if role == "botRise" or not c.kids:
            kids = tuple((s.visit(kc, None, 0), n) for kc, n in c.kids)
            return s.mk(i, c.G + pi, kids)
        # expand the children into a flat list of (class, count) with the two end children split off
        flat = []
        for kc, n in c.kids:
            flat.append([kc, n])
        assert sum(n for _, n in flat) == k
        first, last = flat[0][0], flat[-1][0]
        if role == "topDesc":
            thetas = [(kc, n, Fr(0)) for kc, n in flat]
        else:
            r = s.r * cap
            if s.design == "P":
                te = pi / 2 + c.G - r
                ti = (2 * r - c.G) / (k - 2)
                tis = [ti] * (k - 2)
            else:                                   # 'Pint': integer rule
                assert pi.denominator == 1 and pi % 2 == 0 and c.G.denominator == 1, (t, i, role, pi, c.G)
                sv = 0 if c.G == 0 else -((-Fr(r).numerator) // Fr(r).denominator)      # ceil(r* c)
                te = pi / 2 + c.G - sv
                I = 2 * sv - c.G
                if I < 0:
                    s.stats["neg"] += 1
                    s.where.setdefault("negI", (t, i, role, int(c.G), sv))
                q, rem = divmod(int(I), k - 2)
                # spread the remainder symmetrically from the middle outwards
                order = sorted(range(k - 2), key=lambda j: abs(j - (k - 3) / 2))
                tis = [Fr(q)] * (k - 2)
                for j in order[:rem]:
                    tis[j] += 1
            # interior children in order: expand runs, with the interior thetas tis
            mid = []
            pos = 0
            for idx, (kc, n) in enumerate(flat):
                cnt = n - (1 if idx == 0 else 0) - (1 if idx == len(flat) - 1 else 0)
                for _ in range(cnt):
                    mid.append((kc, 1, tis[pos]))
                    pos += 1
            assert pos == k - 2
            thetas = [(first, 1, te)] + mid + [(last, 1, te)]
        # blocks, residual
        T = Fr(0)
        worst_res = Fr(0)
        newkids = []
        for kc, n, th in thetas:
            b = kc.G - th
            if b < 0:
                s.stats["neg"] += 1
                s.worst["negmin"] = min(s.worst["negmin"], b / cap)
                s.where.setdefault("neg", (t, i, role, float(b / cap), float(kc.G / cap), float(th / cap)))
            if role != "topDesc":
                # the residual is maximized at the first or last of a run of equal thetas
                for q in sorted({0, n - 1}):
                    Lq = T + q * th - pi / 2
                    Rq = pi / 2 + c.G - (T + (q + 1) * th)
                    v = (max(Lq, 0) + max(Rq, 0)) / cap
                    worst_res = max(worst_res, v)
            T += n * th
            newkids.append((s.visit(kc, th, 0), n))
        if T != pi + c.G:
            s.stats["cons"] += 1
        if t >= T_MIN and role != "topDesc":
            s.stats["senders"] += 1
            exc = worst_res * cap - s.r * cap
            if exc > s.worst.get("exc", Fr(-10 ** 9)):
                s.worst["exc"] = exc
                s.where["exc"] = (t, i, role, float(cap), int(c.G) if c.G.denominator == 1 else float(c.G))
            if worst_res > s.worst["res"]:
                s.worst["res"] = worst_res
                s.where["res"] = (t, i, role, float(c.G / cap))
            s.worst["G"] = max(s.worst["G"], c.G / cap)
            s.worst["ac"] = max(s.worst["ac"], a / cap)
        # separator geometry for large senders (padded rectangle, arbitrary column count):
        # fringe classes F_CLASSES; for a class f take n = floor(pi/(2f)) (so f n <= pi/2: the
        # certified f rows lie inside the up-port), need support mu c <= delta_F f n ((4.4) form) and
        # rows m = ceil(a/n) in [2^ROWS_LO, 2^ROWS_Q).  Use the first class that works.
        if t >= T_MIN and role not in ("topDesc", "botRise") and a > 2 ** GEOM_CUT:
            hit = None
            for f in F_CLASSES:
                n = int(pi / 2) // f
                if n < 16:
                    continue
                m = -((-a.numerator) // (n * a.denominator))
                if MU * cap <= DELTA_F * f * n and 2 ** ROWS_LO <= m < 2 ** ROWS_Q:
                    hit = (f, n, m)
                    break
            key = (role, hit is not None)
            s.geom[key] = s.geom.get(key, 0) + 1
            if hit:
                s.fvals.add(hit[0])
                s.mlo = min(getattr(s, "mlo", 10 ** 30), hit[2]); s.mhi = max(getattr(s, "mhi", 0), hit[2])
            elif len(s.geom_bad) < 4:
                s.geom_bad.append((t, i, role, float(a / cap)))
            rr = s.ratios.setdefault(role, [Fr(10), Fr(0)])
            rr[0] = min(rr[0], a / cap); rr[1] = max(rr[1], a / cap)
        # merge equal consecutive kids
        merged = []
        for kc, n in newkids:
            if merged and merged[-1][0] is kc:
                merged[-1] = (kc, merged[-1][1] + n)
            else:
                merged.append((kc, n))
        return s.mk(i, c.G + pi, tuple(merged))


def run(x, y, z, d, design="P"):
    P = Par(x, y, z)
    S = Sim(P, d, design)
    root = S.initial()
    for t in range(P.tf(d)):
        root = S.step(root, t)
    S.stats["classes"] = len(S.intern)
    return P, S


def main():
    x, y, z = map(int, sys.argv[1:4])
    design = os.environ.get("DESIGN", "P")
    for d in map(int, sys.argv[4:]):
        P, S = run(x, y, z, d, design)
        print(f"({x},{y},{z}) d={d} tf={P.tf(d)}: r*={float(S.r):.4e}  residual/c max={float(S.worst['res']):.4e} "
              f"(ratio to r* {float(S.worst['res'] / S.r):.4f}) at {S.where.get('res')}; G/c max={float(S.worst['G']):.4e}; "
              f"a/c max={float(S.worst['ac']):.6f}; integer excess over r*c max={float(S.worst.get('exc', 0)):.3f} wires at {S.where.get('exc')}; neg blocks={S.stats['neg']} (min b/c {float(S.worst['negmin']):.3e}, "
              f"first {S.where.get('neg')}); cons errors={S.stats['cons']}; classes={S.stats['classes']}", flush=True)
        print(f"   geometry (a > 2^{GEOM_CUT}, rows in [2^{ROWS_LO}, 2^{ROWS_Q})): {S.geom}; classes used {sorted(S.fvals)}; "
              f"m in [{getattr(S, 'mlo', None)}, {getattr(S, 'mhi', None)}]; failures {S.geom_bad}", flush=True)
        print("   a/c range by role (a > 2^%d): %s" % (GEOM_CUT, {r: (float(v[0]), float(v[1])) for r, v in S.ratios.items()}), flush=True)


if __name__ == "__main__":
    main()
