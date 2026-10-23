#!/usr/bin/env python3
"""Interval-arithmetic (mpmath.iv) certification of rd_sparse.escapes_merged / worst_merged (regime A).

Same pattern as rd_scaled_iv.py: (D, ratio), lam, s, c, t are chosen by the float search (the float code's
own grids); the bound at that choice is re-evaluated in interval arithmetic and its upper end used.
  * a_coll_sup_ln: (lam j + max(v0, 2 R Lc)) / (1 - 1/(2 lam)), v0 = R (g0 + E0 + Lc x)/s, at the argmin
    (lam, s); q0 = e R u / (lam e^x) < 1 and q0 e^s < 1 checked in interval arithmetic.
  * mult_sup_ln: max(v0, Lc), v0 = (e^x Y + E0 + Lc x)/t, Y = sum_{c<k<=K} binom(H,k) p^k e^{t(k-c)} plus the
    geometric tail past K (ratio (H-K)/(K+1) p e^t < 1 checked), p = s2 e^{-x}; exact binomials.
  * x = ln n0 is replaced by a certified LOWER bound of max(40 ln 2, j_a/(100 J)) (the float value may
    exceed the true one by an ulp; every claim is "for all n >= e^x", so a smaller x is the stronger claim).
  * ln(1/ETA) uses ln(10^4) (>= the float ln(1/1e-4)).
  * level offset floor: d - ceil(b0) as the float code when ceil(b0) >= b0 is certified; when the float b0
    underflows to 0 (x >= 700) the floor d - b0_up is used instead (the float d - 0 is not a lower bound).
NOT certified: the sup-over-n (Moebius / t(n) = t* + x) reductions stated in rd_sparse.py, the monotone
average closure of worst_merged, monotonicity in j of the j-interval convention.
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rd_sparse as A  # noqa: E402
import route_d_rigorous as RD  # noqa: E402
from rd_scaled_iv import I, U, upf, upfrac, lt, ivmin_up, STATS, E_IV  # noqa: E402
from mpmath import iv  # noqa: E402

CS = RD.CS


def ivmax_up(*xs):
    """degenerate interval at the largest upper end (upper bound of a max)."""
    best = I(xs[0])
    for x in xs[1:]:
        x = I(x)
        if lt(best, x) or upf(x) > upf(best) or x.b > best.b:
            best = x
    return U(best)


# ------------------------------------------------------------------ float searches with witnesses
def a_coll_cands(j, R, u, ln_n0, E0, Lc):
    """rd_sparse.a_coll_sup_ln candidate list [(value, lam, s)] sorted (min = the float value)."""
    out = []
    for lam in (0.6, 0.75, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0):
        lq0 = math.log(math.e * R * u / lam) - ln_n0
        if lq0 >= 0:
            continue
        for s in [0.05 * 1.1 ** i for i in range(200)]:
            lqe = lq0 + s
            if lqe >= -1e-12:
                break
            q0, qe = math.exp(lq0), math.exp(lqe)
            lg0 = ln_n0 + 2 * lqe - math.log((1 - q0) * (1 - qe))
            g0 = math.exp(lg0) if lg0 < 700 else math.inf
            v0 = R * (g0 + E0 + Lc * ln_n0) / s
            xD = max(v0, 2 * R * Lc)
            out.append(((lam * j + xD) / (1 - 1 / (2 * lam)), lam, s))
    out.sort()
    return out


def mult_float(Hh, s2, ln_n0, E0, Lc, c):
    """rd_sparse.mult_sup_ln, returning (value, argmin t)."""
    if Hh <= c:
        return 0.0, None
    lp0 = math.log(s2) - ln_n0
    K = min(Hh, c + 400)
    best, bt = math.inf, None
    for t in [0.02 * 1.12 ** i for i in range(120)]:
        if t > 600:
            break
        terms = [RD.lbinom(Hh, k) + k * lp0 + t * (k - c) for k in range(c + 1, K + 1)]
        mx = max(terms)
        lse = mx + math.log(sum(math.exp(x - mx) for x in terms))
        if K < Hh:
            lr = math.log((Hh - K) / (K + 1)) + lp0 + t
            if lr >= 0:
                continue
            tail = terms[-1] + lr - math.log1p(-math.exp(lr))
            lse = max(lse, tail) + math.log1p(math.exp(-abs(lse - tail)))
        lY = ln_n0 + lse
        if lY > 600:
            continue
        v0 = (math.exp(lY) + E0 + Lc * ln_n0) / t
        v = max(v0, Lc)
        if v < best:
            best, bt = v, t
    return best, bt


# ------------------------------------------------------------------ interval evaluations
def a_coll_iv(j, R, u, x, E0, Lc, lam, s):
    L, Sv = I(lam), I(s)
    lq0 = iv.log(E_IV * R * u / L) - x
    lqe = lq0 + Sv
    if not lt(lqe, 0):
        return None
    q0, qe = iv.exp(lq0), iv.exp(lqe)
    g0 = iv.exp(x + 2 * lqe) / ((1 - q0) * (1 - qe))
    v0 = I(R) * (g0 + E0 + I(Lc) * x) / Sv
    xD = ivmax_up(v0, 2 * I(R) * I(Lc))
    STATS["iv_evals"] += 1
    return U((L * I(j) + xD) / (1 - 1 / (2 * L)))


def mult_iv(Hh, s2, x, E0, Lc, c, t):
    if Hh <= c:
        return iv.mpf(0)
    K = min(Hh, c + 400)
    p = I(s2) * iv.exp(-x)
    T = I(t)
    et = iv.exp(T)
    k0 = c + 1
    term = I(math.comb(Hh, k0)) * p ** k0 * et
    Y = iv.mpf(0)
    for k in range(k0, K + 1):
        Y += term
        if k < K:
            term = term * (Hh - k) / (k + 1) * p * et
    if K < Hh:
        r = I(Fr(Hh - K, K + 1)) * p * et
        if not lt(r, 1):
            return None
        Y += term * r / (1 - r)
    v0 = (iv.exp(x) * Y + E0 + I(Lc) * x) / T
    STATS["iv_evals"] += 1
    return ivmax_up(v0, I(Lc))


# ------------------------------------------------------------------ escapes_merged: plan + certificate
def ln_n0_lo(ja, CJ=100 * 5e5, floor_log2=40):
    """certified lower bound of max(floor_log2 ln 2, ja/CJ), as an exact point interval."""
    v = max(I(floor_log2) * iv.log(iv.mpf(2)), I(ja) / I(CJ), key=lambda z: z.a)
    return iv.mpf(v.a)


def escapes_merged_plan(j, f, s2, ln_n0, D, ratio=2.0):
    """float value (as rd_sparse.escapes_merged) and the data needed to certify it."""
    b0 = j * math.exp(-ln_n0) if ln_n0 < 700 else 0.0
    top = b0 + math.sqrt(2 * j) + 2
    Lc = s2 + 1.0
    E0 = s2 * (1 - math.log(s2)) + 2 * math.log(top + 2) + math.log(1 / A.ETA) + 4 + math.log(len(CS)) + math.log(64)
    cb = math.ceil(b0)
    base = cb + D
    P = dict(j=j, f=f, s2=s2, D=D, ratio=ratio, cb=cb, base=base, ctop=math.ceil(top))
    if base >= top:
        P["val"] = s2 * top - f * s2
        P["trivial"] = True
        return P
    levels = []
    ksum = 0.0
    d = base
    while d < top:
        R = min(math.ceil(top), int(d * ratio) + 1)
        u = (R - d) * s2
        cands = a_coll_cands(math.ceil(j), R, u, ln_n0, E0, Lc)
        Av = cands[0][0] if cands else math.inf
        kk = min(Av / (d - cb) ** 2, s2 * (R - d))
        levels.append(dict(d=d, R=R, u=u, cands=cands[:6], k=kk))
        ksum += kk
        d = R
    Htot = int(math.ceil(top) - base)
    mc = []
    for c in CS:
        if c <= Htot or c == 1:
            m, t = mult_float(Htot, s2, ln_n0, E0, Lc, c)
            mc.append((c * ksum + m, c, t))
    mc.sort()
    cnt = mc[0][0]
    P.update(levels=levels, Htot=Htot, mc=mc[:4], trivial=False, val=s2 * base + min(s2 * Htot, cnt) - f * s2)
    return P


def escapes_merged_cert(P, x):
    """certified upper bound (interval upper end) of the plan P, valid for every n >= e^x (x <= float ln n0)."""
    j, f, s2 = P["j"], P["f"], P["s2"]
    b0 = I(j) * iv.exp(-x)
    top = U(b0 + iv.sqrt(2 * I(j)) + 2)
    if P["trivial"]:
        return U(I(s2) * top - I(f) * s2)
    if math.ceil(upfrac(top)) != P["ctop"]:
        return None                                  # float rounding changed the level structure: refuse
    cb = P["cb"]
    if Fr(cb) >= upfrac(b0):
        off_shift = I(cb)
    else:
        off_shift = U(b0)                            # float b0 underflowed: use the true b0 upper end
    Lc = s2 + 1.0
    E0 = U(I(s2) * (1 - iv.log(I(s2))) + 2 * iv.log(top + 2) + iv.log(iv.mpf(10 ** 4)) + 4
           + iv.log(iv.mpf(len(CS))) + iv.log(iv.mpf(64)))
    ksum = iv.mpf(0)
    for L in P["levels"]:
        triv = I(s2) * (L["R"] - L["d"])
        Ac = None
        for v, lam, s in L["cands"]:
            Ac = a_coll_iv(math.ceil(j), L["R"], L["u"], x, E0, Lc, lam, s)
            if Ac is not None:
                break
        off = I(L["d"]) - off_shift
        assert lt(0, off)
        kc = triv if Ac is None else ivmin_up(Ac / (off * off), triv)
        ksum = U(ksum + kc)
    best = None
    for v, c, t in P["mc"]:
        if t is None:
            m = iv.mpf(0) if P["Htot"] <= c else None
        else:
            m = mult_iv(P["Htot"], s2, x, E0, Lc, c, t)
        if m is not None:
            best = ivmin_up(best, c * ksum + m)
            break
    cnt = ivmin_up(best, I(s2) * P["Htot"])
    return U(I(s2) * P["base"] + cnt - I(f) * s2)


DS = (500, 1000, 2000, 3000)
RATIOS = (1.6, 2.0, 4.0)


def load_merged_iv(j, f, s, ln_n0, x):
    """(float load as rd_sparse.load_merged, certified load)."""
    plans = sorted((escapes_merged_plan(j, f, s, ln_n0, D, r) for D in DS for r in RATIOS), key=lambda P: P["val"])
    Lf = plans[0]["val"] + f * s
    Lc = None
    for P in plans[:3]:
        c = escapes_merged_cert(P, x)
        if c is not None:
            Lc = ivmin_up(Lc, c)
            if upf(Lc) <= plans[min(len(plans) - 1, plans.index(P) + 1)]["val"]:
                break
    return Lf, (None if Lc is None else U(Lc + I(f) * s))


def worst_merged_iv(j, f, ln_n0, x, smax=10 ** 9):
    """worst_merged with every load certified: returns (worst float, worst cert (upper), s)."""
    wf, wc = -math.inf, -math.inf
    s = 1
    while s <= 64 and s <= max(1, j / f):
        Lf, Lc = load_merged_iv(j, f, s, ln_n0, x)
        wf = max(wf, Lf - f * s)
        wc = max(wc, upf(Lc - I(f) * s) if Lc is not None else math.inf)
        if Lc is not None and lt(Lc, I(f) * s):
            return wf, wc, s
        s += 1
    sa = s - 1
    La_f, La_c = load_merged_iv(j, f, sa, ln_n0, x)
    while sa <= max(1, j / f) and sa <= smax:
        sb = max(sa + 1, int(sa * 1.05))
        Lb_f, Lb_c = load_merged_iv(j, f, sb, ln_n0, x)
        wf = max(wf, min(sb * (La_f / sa - f), Lb_f - f * sa))
        if La_c is None or Lb_c is None:
            wc = math.inf
        else:
            wc = max(wc, min(upf(sb * (La_c / sa - f)), upf(Lb_c - I(f) * sa)))
        if Lb_c is not None and lt(Lb_c, I(f) * sb):
            return wf, wc, sb
        sa, La_f, La_c = sb, Lb_f, Lb_c
    return wf, wc, sa


if __name__ == "__main__":
    j, f = float(sys.argv[1]), 3967.0
    ln0 = max(40 * math.log(2), j / 5e7)
    x = ln_n0_lo(j)
    print(worst_merged_iv(j, f, ln0, x), A.worst_merged(j, f, ln0), STATS)
