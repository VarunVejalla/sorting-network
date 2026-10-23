#!/usr/bin/env python3
"""Interval-arithmetic (mpmath.iv, outward rounding) certification of rd_scaled.escapes_cell (regime B).

Pattern (as ../sub500-screen/cert_walk_n.py): every free parameter (lam, t, kappa, s, c, the alpha / kappa
sub-intervals of an exclusion) is a float chosen by a float search; only the final inequality at that
parameter is evaluated in interval arithmetic, upper bounds taken at the upper end of the enclosure.
Nothing in rd_scaled.py is changed: its functions are called for the float plan, and every number that
enters the certified total is re-derived here.

Per level of escapes_cell (see IV-CERT.md for the full list):
  * A* : "every alpha in [A, amax] is excluded" is re-proved by a top-down geometric cover of [A, amax_up]
         (cells of ratio >= RMIN_A); each cell [a0, a1] is checked at its upper end a1 (q, nlnG and the
         count entropy are nondecreasing in alpha) against a0.  The certified A is the lowest point of the
         contiguous certified run from amax down (so a failure mid-range acts like the float restart).
  * k_bool : the same for "every kappa in [k, nu] is excluded", top cell up to nu_up (exact nu).
  * A_coll, mult_excess, high-rows t-min, round-1 tail: closed forms evaluated at the float argmin.
  * kmax_sources : exact rational arithmetic at the certified A.
  * min over alternatives: any certified alternative is a valid upper bound; the float argmin is
    certified first (lazy), others only if needed.
Soundness repairs relative to the float code (flagged in IV-CERT.md):
  * ln_count_s / k_bool_s entropies use H restricted to [0, 1/2] (resp. the sup of H over the kappa cell),
    since nu H(kap/nu) is not monotone for kap > nu/2 and underestimates the count there;
  * level caps / floors / offsets computed exactly (Fraction), not in float;
  * round1_level_tail entropy uses x ln(e/x) with x = min(alpha/d^2, 1).
NOT certified here (documented): the cell-monotonicity conventions in (b, sigma), the "monotone average"
closure, the extension of the round-1 tail exclusion from d0 to every d >= d0, the constant c_ln = 80
of eps_level, and the probabilistic lemmas themselves.
"""
import math
import os
import sys
from fractions import Fraction as Fr

import numpy as np
from mpmath import iv, libmp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rd_scaled as S  # noqa: E402

iv.dps = 40
IVT = type(iv.mpf(1))
LN2 = iv.log(iv.mpf(2))
E_IV = iv.exp(iv.mpf(1))
RMIN_A = 1.02          # finest alpha-cell ratio in A* covers (float code: steps of 1.1)
RMIN_K = 1.01          # finest kappa-cell ratio in k_bool covers (float code: grid 1.05)
RMIN_T = 1.005         # round-1 tail cells (float code: 1.01)
STATS = {"A_fail": 0, "kb_fail": 0, "tail_fail": 0, "iv_evals": 0}
FAILS = []             # (kind, args) of covers that certified nothing (the trivial bound was used instead)

_ORIG_N0 = S.n0_of_b
NMIN = 2.0 ** 40


def configure(CJ=100 * 5e5, nmin=2.0 ** 30):
    """as coverB.py: S.CJ = 100 * 5e5 and floor n >= nmin via n0_of_b."""
    global NMIN
    NMIN = nmin
    S.CJ = CJ
    S.n0_of_b = lambda b, nm=nmin: _ORIG_N0(b, nm)


# ------------------------------------------------------------------ interval helpers
def I(x):
    if isinstance(x, IVT):
        return x
    if isinstance(x, Fr):
        return iv.mpf(x.numerator) / x.denominator
    if isinstance(x, (int, np.integer)):
        return iv.mpf(int(x))
    x = float(x)
    assert math.isfinite(x), x
    return iv.mpf(x)          # exact (doubles have 53 bits < iv precision)


def U(x):
    """degenerate interval at the upper end (use only where the consumer is nondecreasing in x)."""
    x = I(x)
    return iv.mpf(x.b)


def upf(x):
    """a float >= every point of x."""
    r = I(x)._mpi_[1]
    f = libmp.to_float(r, rnd=libmp.round_ceiling)
    if f == 0.0 and libmp.mpf_sign(r) > 0:
        f = 5e-324
    return f


def lof(x):
    r = I(x)._mpi_[0]
    f = libmp.to_float(r, rnd=libmp.round_floor)
    if f == 0.0 and libmp.mpf_sign(r) < 0:
        f = -5e-324
    return f


def upfrac(x):
    p, q = libmp.to_rational(I(x)._mpi_[1])
    return Fr(p, q)


def lt(x, y):
    """certified x < y (every point of x below every point of y)."""
    return libmp.mpf_lt(I(x)._mpi_[1], I(y)._mpi_[0])


def ivmin_up(*xs):
    """upper end of min of several upper-bounded quantities."""
    best = None
    for x in xs:
        if x is None or (isinstance(x, float) and x == math.inf):
            continue
        x = U(x)
        if best is None or libmp.mpf_lt(x._mpi_[1], best._mpi_[1]):
            best = x
    return best


HALF = libmp.from_rational(1, 2, 200)


def Hpt_up(r):
    """upper end of H at the exact point r (raw mpf), r in [0, 1]."""
    if not libmp.mpf_gt(r, libmp.fzero) or not libmp.mpf_lt(r, libmp.fone):
        return iv.mpf(0)
    x = iv.mpf(libmp.to_rational(r)[0]) / libmp.to_rational(r)[1]
    return iv.mpf((-x * iv.log(x) - (1 - x) * iv.log(1 - x)).b)


def Hsup(x0, x1):
    """upper bound of sup H on [x0, x1] (numbers or intervals; H increasing on [0, 1/2], decreasing after)."""
    xl = I(x0)._mpi_[0]
    xh = I(x1)._mpi_[1]
    if libmp.mpf_le(xh, HALF):
        return Hpt_up(xh)
    if libmp.mpf_ge(xl, HALF):
        return Hpt_up(xl)
    return iv.mpf(LN2.b)


def Hmon(x):
    """sup of H on [0, x]: H(min(x, 1/2)) -- the sound entropy of {subsets of size <= x u}."""
    return Hsup(0, x)


def Hmon_f(x):
    return S.H(min(x, 0.5))


def Hsup_f(x0, x1):
    if x1 <= 0.5:
        return S.H(max(x1, 0.0))
    if x0 >= 0.5:
        return S.H(min(x0, 1.0))
    return math.log(2)


def nlog1m(q):
    """enclosure of -ln(1 - q), q in [0, 1)."""
    q = I(q)
    assert lt(q, 1)
    if lt(q, Fr(1, 10 ** 6)):
        return iv.mpf([0, (q / (1 - q)).b])          # q <= -ln(1-q) <= q/(1-q)
    return -iv.log(1 - q)


def log1p_up(y):
    """enclosure (upper end valid) of ln(1 + y), y >= 0."""
    y = I(y)
    if lt(y, Fr(1, 10 ** 6)):
        return iv.mpf([0, y.b])
    return iv.log(1 + y)


# ------------------------------------------------------------------ eps, n0
def n0_lo(b):
    """certified lower bound for n0_of_b (eps is decreasing in n, so the lower end is conservative)."""
    x = I(S.CJ) / I(b)
    if lt(E_IV, x):
        v = x * iv.log(x)
        return max(Fr(NMIN), Fr(lof(v)))
    return Fr(NMIN)


def eps_up(R, b, n0):
    """eps_level(R, b, n0) upper: c_ln max(1, ln m)/m is decreasing in m; m = max(n0, R^2/(2b)) lower."""
    m = max(Fr(n0), Fr(lof(I(R) * I(R) / (2 * I(b)))))
    mi = I(m)
    L = iv.log(mi)
    num = L if lt(1, L) else iv.mpf([1, max(1.0, upf(L))])
    return U(80 * num / mi)


# ------------------------------------------------------------------ generic top-down cover
def cover_down(x_lo, x_hi, find, check, rmin):
    """smallest x in [x_lo, x_hi] such that [x, x_hi] is a union of cells [a0, a1] each with a float
    witness w = find(a0, a1) and check(a0, a1, w) True (interval-certified). Returns x_hi if none."""
    def cov(a0, a1, depth):
        w = find(a0, a1)
        if w is not None:
            STATS["iv_evals"] += 1
            if check(a0, a1, w):
                return a0
        if a1 / a0 <= rmin or depth > 80:
            return a1
        m = math.sqrt(a0) * math.sqrt(a1)
        if not (a0 < m < a1):
            return a1
        x = cov(m, a1, depth + 1)
        if x > m:
            return x
        return cov(a0, m, depth + 1)
    if not (0 < x_lo < x_hi):
        return x_hi
    return cov(x_lo, x_hi, 0)


# ------------------------------------------------------------------ A* (Kingman exclusion)
def E_count_f(a, nu, d, R, e_s):
    kap = min(nu, a / (d * d))
    if kap <= 0:
        return e_s
    return nu * Hmon_f(kap / nu) + kap * math.log(R - d + 1) + e_s


def E_count_iv(a, nu, d, R, e_s):
    """ln_count_s (sound: H on [0, 1/2]) + e_s at alpha = a, upper; nondecreasing in a, nu, e_s."""
    nu = U(nu)
    kap_q = I(a) / (I(d) * I(d))
    kap = ivmin_up(nu, kap_q)
    if not lt(0, kap):
        return U(e_s)
    return U(nu * Hmon(kap / nu) + kap * iv.log(I(R - d + 1)) + U(e_s))


def cert_A_star(b, R, d, nu, e_s, A_float):
    """certified upper bound for A_star_s(b, R, d, nu, e_s): every alpha in [A, amax] excluded."""
    nu_u, es_u = U(nu), U(e_s)
    amax = ivmin_up(nu_u * R * R, I(R) * I(b))
    amax_f = upf(amax)
    if A_float >= amax_f * (1 - 1e-12):
        return amax
    nu_f, es_f = upf(nu_u), upf(es_u)

    def find(a0, a1):
        E = E_count_f(a1, nu_f, d, R, es_f)
        for lam in S.LAMS:
            if lam * b >= a0:
                continue
            for k in S.KAPPAS:
                t = k / R
                v = S.nlnG_s(a1, t, R, lam)
                if v < math.inf and lam * b + (v + E) / t < a0 * (1 - 1e-9):
                    return (lam, t)
        return None

    def check(a0, a1, w):
        lam, t = w
        tt, L = I(t), I(lam)
        s = tt * R
        q = I(a1) * (iv.exp(s) - 1 - s) / (I(R) * R * (iv.exp(tt * L) - 1))
        if not lt(q, 1):
            return False
        v = nlog1m(q)
        E = E_count_iv(a1, nu_u, d, R, es_u)
        return lt(L * I(b) + (v + E) / tt, a0)

    x = cover_down(A_float, amax_f, find, check, RMIN_A)
    if x >= amax_f:
        STATS["A_fail"] += 1
        FAILS.append(("A_star", b, R, d, upf(nu_u), upf(es_u), A_float))
        return amax
    return ivmin_up(I(x), amax)


# ------------------------------------------------------------------ k_bool
def cert_k_bool(b, d, nu, e_s, k_float):
    """certified upper bound for k_bool_s: every kappa in [k, nu] excluded (cells [klo, kk]):
    klo d > lam b + (-ln(1 - q(kk)) + nu_up sup_{[klo/nu_up, kk/nu_lo]} H + e_s)/t."""
    nu = I(nu)
    nu_u = U(nu)
    nu_hi_f, nu_lo_f = upf(nu), lof(nu)
    es_u = U(e_s)
    es_f = upf(es_u)
    if k_float >= nu_lo_f * (1 - 1e-12):           # float k_bool returned nu itself: trivial bound
        return nu_u

    def find(klo, kk):
        E = nu_hi_f * Hsup_f(klo / nu_hi_f, min(1.0, kk / nu_lo_f)) + es_f
        lhs = klo * d * (1 - 1e-9)
        for lam in S.LAMS_B:
            if lam * b >= lhs:
                continue
            for tt in S.TT_B:
                if tt * lam > 700:
                    continue
                q = kk * (math.expm1(tt) - tt) / math.expm1(tt * lam)
                if q >= 1:
                    continue
                if lam * b + (-math.log1p(-q) + E) / tt < lhs:
                    return (lam, tt)
        return None

    def check(klo, kk, w):
        lam, tt = w
        L, T = I(lam), I(tt)
        q = I(kk) * (iv.exp(T) - 1 - T) / (iv.exp(T * L) - 1)
        if not lt(q, 1):
            return False
        x1 = I(kk) / iv.mpf(nu.a)
        Hs = Hsup(I(klo) / nu_u, x1 if lt(x1, 1) else iv.mpf(1))
        E = nu_u * Hs + es_u
        return lt(L * I(b) + (nlog1m(q) + E) / T, I(klo) * d)

    x = cover_down(k_float, nu_hi_f, find, check, RMIN_K)
    if x >= nu_hi_f:
        STATS["kb_fail"] += 1
        FAILS.append(("k_bool", b, d, nu_hi_f, es_f, k_float))
        return nu_u
    return ivmin_up(I(x), nu_u)


# ------------------------------------------------------------------ collision branch
def A_coll_cands(b, R, nu, e_s):
    out = []
    for lam in (0.6, 0.75, 1.0, 1.5, 2.0, 3.0):
        q = math.e * R * nu / lam
        if q >= 1:
            continue
        for i in range(200):
            s = 0.05 * 1.1 ** i
            ls = math.log(q) + s
            if ls >= -1e-12:
                break
            qe = math.exp(ls)
            g = math.log1p(qe * qe / ((1 - q) * (1 - qe)))
            out.append(((lam * b + R * (g + e_s) / s) / (1 - 1 / (2 * lam)), lam, s))
    out.sort()
    return out


def cert_A_coll(b, R, nu, e_s):
    nu_u, es_u = U(nu), U(e_s)
    cands = A_coll_cands(b, R, upf(nu_u), upf(es_u))
    for v, lam, s in cands[:6]:
        L, Sv = I(lam), I(s)
        q = E_IV * R * nu_u / L
        qe = q * iv.exp(Sv)
        if not (lt(q, 1) and lt(qe, 1)):
            continue
        g = log1p_up(qe * qe / ((1 - q) * (1 - qe)))
        STATS["iv_evals"] += 1
        return U((L * I(b) + I(R) * (g + es_u) / Sv) / (1 - 1 / (2 * L)))
    return None


# ------------------------------------------------------------------ kmax_sources (exact)
def cert_kmax(A, d, sigma):
    if A is None:
        return None
    Aq = upfrac(A)
    sg = Fr(sigma)

    def S3(x):
        return Fr(x * (x + 1) * (2 * x + 1), 6)

    def F(w):
        return S3(d + w - 1) - S3(d - 1)
    lo, hi = 0, 1
    while sg * F(hi) <= Aq:
        hi *= 2
        if hi > 1 << 40:
            return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if sg * F(mid) <= Aq:
            lo = mid
        else:
            hi = mid
    rem = Aq - sg * F(lo)
    return I(sg * lo + min(sg, rem / (d + lo) ** 2))


# ------------------------------------------------------------------ multiplicity excess
def _mult_K(Hh, sigma):
    return min(Hh, int(Hh * sigma + 12 * math.sqrt(Hh * sigma + 1) + 80))


def mult_float(Hh, sigma, e_s, c=1):
    """rd_scaled.mult_excess_s, returning (value, argmin t)."""
    if Hh <= c:
        return 0.0, None
    from math import lgamma, log
    K = _mult_K(Hh, sigma)
    ks = np.arange(K + 1)
    lp = np.array([lgamma(Hh + 1) - lgamma(k + 1) - lgamma(Hh - k + 1) + k * log(sigma) + (Hh - k) * math.log1p(-sigma)
                   for k in range(K + 1)])
    rK = (Hh - K) / (K + 1) * sigma / (1 - sigma) if K < Hh else 0.0
    if K <= c:
        return (0.0, None) if K == Hh else (math.inf, None)
    base = lp[c + 1:]
    kk = ks[c + 1:]
    best, bt = math.inf, None
    for t in [0.02 * 1.12 ** i for i in range(140)]:
        if t > 700:
            break
        x = base + t * (kk - c)
        mx = float(x.max())
        lse = mx + math.log(float(np.exp(x - mx).sum()))
        if K < Hh:
            q = rK * math.exp(t)
            if q >= 1:
                continue
            xl = lp[K] + t * (K - c) + math.log(q / (1 - q))
            lse = max(lse, xl) + math.log1p(math.exp(min(lse, xl) - max(lse, xl)))
        if lse > 600:
            continue
        v = (math.log1p(math.exp(lse)) + e_s) / t
        if v < best:
            best, bt = v, t
    return best, bt


def mult_iv(Hh, sigma, e_s, c, t):
    """per n: (ln(1 + Y) + e_s)/t, Y = sum_{k>c} P(Bin(Hh, sigma) = k) e^{t(k-c)} (geometric tail past K)."""
    if Hh <= c:
        return iv.mpf(0)
    K = _mult_K(Hh, sigma)
    if K <= c:
        return iv.mpf(0) if K == Hh else None
    sg = I(sigma)
    r = sg / (1 - sg)
    T = I(t)
    et = iv.exp(T)
    k0 = c + 1
    term = I(math.comb(Hh, k0)) * sg ** k0 * iv.exp((Hh - k0) * iv.log(1 - sg)) * et
    Y = iv.mpf(0)
    for k in range(k0, K + 1):
        Y += term
        if k < K:
            term = term * (Hh - k) / (k + 1) * r * et
    if K < Hh:
        q = I(Fr(Hh - K, K + 1)) * r * et
        if not lt(q, 1):
            return None
        Y += term * q / (1 - q)
    STATS["iv_evals"] += 1
    return U((log1p_up(Y) + U(e_s)) / T)


def cert_mult(Hh, sigma, e_s, c):
    v, t = mult_float(Hh, sigma, upf(e_s), c)
    if v == math.inf:
        return None
    if t is None:
        return mult_iv(Hh, sigma, e_s, c, 1.0)
    return mult_iv(Hh, sigma, e_s, c, t)


# ------------------------------------------------------------------ round-1 level tail
def cert_tail(b, d0, ratio, n0, best_float):
    """certified (w_tail, N_tail) of round1_level_tail at d0: every alpha in [ahat, R b] excluded at d0
    (cells [a0, a1], q(a1) <= 1/2, entropy with x = min(a1/d^2, 1)).  The extension to every level
    d_i = d0 ratio^i >= d0 is the float code's (unverified) relative-monotonicity claim."""
    if best_float == math.inf:
        return None, None
    d = I(d0)
    Rr = I(ratio) * d
    amax = U(Rr * I(b))
    amax_f = upf(amax)
    SS = [0.5 * 0.7 ** i for i in range(80)]
    epsR = eps_up(Rr.a, b, n0)          # eps_level is nonincreasing in R: R at its lower end
    eps_f = upf(epsR)
    df = float(d0)
    Rf = upf(Rr)

    def ent_f(a1):
        x = a1 / (df * df)
        xm = min(x, 1.0)
        return xm * math.log(math.e / xm) + x * math.log(Rf - df + 1) + eps_f

    def find(a0, a1):
        ent = ent_f(a1)
        for lam in (0.8, 1.0, 1.25, 1.5, 2.0, 3.0):
            for s_ in SS:
                g_ = math.expm1(s_) - s_
                q = a1 * g_ / (Rf * 0.999999 * s_ * lam)
                if q > 0.5:
                    continue
                if a0 * (1 - 1e-9) > lam * b + a1 * g_ / (s_ * s_ * lam * (1 - q)) + Rf * ent / s_:
                    return (lam, s_)
        return None

    def check(a0, a1, w):
        lam, s_ = w
        L, Sv = I(lam), I(s_)
        g_ = iv.exp(Sv) - 1 - Sv
        a1i = I(a1)
        q = a1i * g_ / (Rr * Sv * L)
        if not lt(q, Fr(1, 2)):
            return False
        x = a1i / (d * d)
        xm = x if lt(x, 1) else iv.mpf(1)
        ent = xm * iv.log(E_IV / xm) + x * iv.log(Rr - d + 1) + epsR
        rhs = L * I(b) + a1i * g_ / (Sv * Sv * L * (1 - q)) + Rr * ent / Sv
        return lt(rhs, a0)

    x = cover_down(best_float, amax_f, find, check, RMIN_T)
    if x >= amax_f:
        STATS["tail_fail"] += 1
        return None, None
    ah = I(x)
    rt = I(ratio)
    return U(ah * rt / (d * (rt - 1))), U(ah / (d * d * (1 - 1 / (rt * rt))))


# ------------------------------------------------------------------ high rows (cached per b, D)
_HR_CACHE = {}


def high_rows_base(b, D, n0f, ratio=1.6, dclose=1e6):
    """float and certified (w, N) of high_rows_s (sigma-free part)."""
    key = (b, D, n0f, ratio, dclose)
    if key in _HR_CACHE:
        return _HR_CACHE[key]
    n0 = n0_lo(b)
    w = N = 0.0
    wc = Nc = iv.mpf(0)
    d = D
    dclose = max(dclose, 1000.0 * b)
    while d < dclose:
        R = int(d * ratio) + 1
        e = S.eps_level(R, b, n0f)
        a = S.A_star_s(b, R, d, 1.0, e)
        if a >= 0.99 * R * R:
            wt0, Nt0, ah0 = S.round1_level_tail(b, d, ratio, n0f)
            if wt0 < math.inf:
                break
        w += a / d
        N += a / (d * d)
        ac = cert_A_star(b, R, d, iv.mpf(1), eps_up(R, b, n0), a)
        wc = U(wc + ac / d)
        Nc = U(Nc + ac / (I(d) * d))
        d = R
    wt, Nt, ahat = S.round1_level_tail(b, d, ratio, n0f)
    w += wt
    N += Nt
    wtc, Ntc = cert_tail(b, d, ratio, n0, ahat)
    if wtc is None:
        wc = Nc = None
    else:
        wc, Nc = U(wc + wtc), U(Nc + Ntc)
    N = min(N, 1.0)
    if Nc is not None and not lt(Nc, 1):
        Nc = iv.mpf(1)
    res = (w, N, wc, Nc, n0)
    _HR_CACHE[key] = res
    return res


def high_rows_cert(b, sigma, D, n0f):
    """returns (float value as rd_scaled.high_rows_s, certified upper)."""
    w, N, wc, Nc, n0 = high_rows_base(b, D, n0f)
    pe = N * (math.log(math.e / N) + math.log(math.e * (w / N + 1))) if N > 0 else 0.0
    eS = sigma * (1 - math.log(sigma)) if sigma > 0 else 0.0
    eps = S.eps_level(D, b, n0f)
    best, bt = math.inf, None
    for i in range(200):
        tt = 0.05 * 1.06 ** i
        if tt > 700:
            break
        v = (sigma * math.expm1(tt) * w + eS + pe + eps) / tt
        if v < best:
            best, bt = v, tt
    if wc is None:
        return best, None
    # certified: pe nondecreasing in N (N <= 1) and w
    if lt(0, Nc):
        pec = Nc * (iv.log(E_IV / Nc) + iv.log(E_IV * (wc / Nc + 1)))
    else:
        pec = iv.mpf(0)
    sg = I(sigma)
    eSc = sg * (1 - iv.log(sg))
    epsc = eps_up(D, b, n0)
    wf, pef = upf(wc), upf(pec)
    bc, btc = math.inf, None
    for i in range(200):
        tt = 0.05 * 1.06 ** i
        if tt > 700:
            break
        v = (sigma * math.expm1(tt) * wf + eS + pef + eps) / tt
        if v < bc:
            bc, btc = v, tt
    T = I(btc)
    STATS["iv_evals"] += 1
    return best, U((sg * (iv.exp(T) - 1) * wc + eSc + U(pec) + epsc) / T)


# ------------------------------------------------------------------ the cell
CS = S.CS


def escapes_cell_iv(b_lo, b_hi, s_lo, s_hi, f, L0x=0, ratio=1.6, dtop=None, do_cert=True, check_float=False):
    """returns dict: float total / e (reproducing rd_scaled.escapes_cell) and, if do_cert, certified
    upper bounds total_c / e_c (None if a needed piece could not be certified)."""
    n0f = S.n0_of_b(b_hi)
    n0 = n0_lo(b_hi)
    eps = S.eps_level(1.0, b_hi, n0f)
    if dtop is None:
        Lb = max(0.0, -math.log(b_hi))
        dtop = max(1e5, 4e3 * math.sqrt(Lb), 20 * Lb)
    L0 = math.ceil(b_hi) + L0x
    sig = s_hi
    e_S = sig * (1 - math.log(sig)) + eps
    Fbl, Fbh = Fr(b_lo), Fr(b_hi)
    levels = []
    lo = L0
    while lo - b_hi < dtop:
        off = lo - b_hi
        hi = max(lo + 1, math.ceil(b_hi + max(off + 8, off * ratio)))
        R = math.ceil(Fr(hi) - Fbl)                 # exact (float: math.ceil(hi - b_lo))
        nu = (hi - lo) * sig
        d = math.floor(Fr(lo + 1) - Fbh)            # exact
        A = S.A_star_s(b_hi, R, d, nu, e_S)
        k1 = S.kmax_sources_s(A, d, sig) if d >= 1 else math.inf
        Ac = S.A_coll_s(b_hi, hi, nu, e_S)
        k2 = S.kmax_sources_s(Ac, lo + 1, sig)
        k3 = S.k_bool_s(b_hi, d, nu, e_S) if d >= 1 else math.inf
        k = min(k1, k2, k3)
        cnts = {}
        for c in CS:
            if c <= hi - lo or c == 1:
                cnts[c] = k * c + S.mult_excess_s(hi - lo, sig, e_S + eps, c)
        cnt = min(cnts.values())
        abr = A / (4 * max(d - 1, 0.5)) + k if d >= 1 else math.inf
        cnt = min(cnt, abr)
        lev = min(sig * (hi - lo), cnt)
        levels.append(dict(lo=lo, hi=hi, R=R, d=d, nu=nu, A=A, Ac=Ac, k1=k1, k2=k2, k3=k3, k=k, cnts=cnts,
                           abr=abr, lev=lev, triv=sig * (hi - lo)))
        lo = hi
    tot_lev = sig * L0 + sum(L["lev"] for L in levels)
    Htot = int(lo - L0)
    merged = math.inf
    mc = {}
    if Htot >= 1:
        ksum = sum(min(L["k"], L["triv"]) for L in levels)
        for c in CS:
            if c <= Htot or c == 1:
                mc[c] = c * ksum + S.mult_excess_s(Htot, sig, e_S + eps, c)
        merged = sig * L0 + min(mc.values())
    total = min(tot_lev, merged)
    Dh = int(math.floor(Fr(lo) - Fbh))
    hr_f, hr_c = high_rows_cert(b_hi, sig, Dh, n0f)
    total += hr_f
    out = dict(total=total, e=total - f * s_lo, use_merged=merged < tot_lev, nlev=len(levels), hr=(hr_f, hr_c),
               ntriv=sum(L["lev"] >= L["triv"] for L in levels), tot_lev=tot_lev, merged=merged)
    if check_float:
        ft, fe = S.escapes_cell(b_lo, b_hi, s_lo, s_hi, f, L0x, ratio, dtop)
        out["float_ref"] = (ft, fe)
    def certify():
        # -------- certification
        sg = I(sig)
        eps_c = eps_up(1.0, b_hi, n0)
        eS_c = U(sg * (1 - iv.log(sg)) + eps_c)
        eSm_c = U(eS_c + eps_c)

        def k_cert(L):
            if "kc" in L:
                return L["kc"]
            nu_iv = sg * (L["hi"] - L["lo"])
            opts = sorted([(L["k1"], 1), (L["k2"], 2), (L["k3"], 3)])
            best = None
            for kv, which in opts:
                if kv == math.inf:
                    continue
                if best is not None and upf(best) <= kv:
                    break
                if which == 1:
                    v = cert_kmax(A_cert(L), L["d"], sig)
                elif which == 2:
                    v = cert_kmax(cert_A_coll(b_hi, L["hi"], nu_iv, eS_c), L["lo"] + 1, sig)
                else:
                    v = cert_k_bool(b_hi, L["d"], nu_iv, eS_c, kv)
                best = ivmin_up(best, v)
            L["kc"] = best
            return best

        def A_cert(L):
            if "Acert" not in L:
                nu_iv = sg * (L["hi"] - L["lo"])
                L["Acert"] = cert_A_star(b_hi, L["R"], L["d"], nu_iv, eS_c, L["A"])
            return L["Acert"]

        def lev_cert(L):
            triv = U(sg * (L["hi"] - L["lo"]))
            opts = sorted([(v, ("c", c)) for c, v in L["cnts"].items()] + [(L["abr"], ("a", 0))])
            best = None
            for v, (kind, c) in opts:
                if v >= L["triv"]:
                    break
                if best is not None and upf(best) <= v:
                    break
                kc = k_cert(L)
                if kc is None:
                    break
                if kind == "c":
                    m = cert_mult(L["hi"] - L["lo"], sig, eSm_c, c)
                    cand = None if m is None else kc * c + m
                else:
                    cand = A_cert(L) / (4 * I(max(Fr(L["d"] - 1), Fr(1, 2)))) + kc
                best = ivmin_up(best, cand)
            return ivmin_up(best, triv)

        if out["use_merged"]:
            ks = iv.mpf(0)
            ok = True
            for L in levels:
                kc = k_cert(L)
                ks = U(ks + ivmin_up(kc, sg * (L["hi"] - L["lo"])))
            best = None
            for v, c in sorted((v, c) for c, v in mc.items()):
                if best is not None and upf(best) <= v + sig * L0:
                    break
                m = cert_mult(Htot, sig, eSm_c, c)
                if m is not None:
                    best = ivmin_up(best, c * ks + m)
            tc = U(sg * L0 + best) if (ok and best is not None) else None
        else:
            tc = U(sg * L0)
            for L in levels:
                tc = U(tc + lev_cert(L))
        if tc is None or hr_c is None:
            out["total_c"] = out["e_c"] = None
            return out
        tc = U(tc + hr_c)
        out["total_c"] = tc
        out["e_c"] = U(tc - I(f) * I(s_lo))
        return out

    out["certify"] = certify
    if do_cert:
        certify()
    return out


if __name__ == "__main__":
    configure()
    bl, bh, sl, sh = (float(x) for x in sys.argv[1:5])
    f = max(3967.0, 8 * bl)
    r = escapes_cell_iv(bl, bh, sl, sh, f, check_float=True)
    print(r["float_ref"], r["total"], r["e"], r.get("total_c"), r.get("e_c"), STATS)
