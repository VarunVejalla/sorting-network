#!/usr/bin/env python3
"""Route (d) in the dense regime for all large n at once (ROUND1-ENERGY.md, "n -> infinity").

Every term of route_d_rigorous.escapes at density b = j/n and set fraction sigma = s2/n is n times an
n-free quantity, plus pieces of order ln n which are absorbed in a slack EPS per unit n (valid for every
n >= n0 with ln-terms/n <= EPS). Upper bounds used (each is an inequality valid at every n, not a limit):
  * lbinom(n, s) <= n H(s/n);  lbinom(u, k) <= u H(k/u);
  * n lnG(A = alpha n) = -n ln(1 - alpha g(tR) / (R^2 (e^{t lam} - 1)))           (exact);
  * mult_excess: n ln(1 + x) + ent, x n-free (Bin(H, sigma));
  * kmax_sources(alpha n, d, sigma n) = n * (sigma w + ...), F(w) <= alpha / sigma;
  * the ln n, ln(top), ln(1/ETA), ln(#grid) parts of the entropies: <= EPS n.
Escapes per unit n are compared with the allowance per unit n, b/J. Floats (as route_d_rigorous).
"""
import math
import sys

import numpy as np

EPS_DEFAULT = 1e-6


def H(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -(x * math.log(x) + (1 - x) * math.log1p(-x))


def nlnG_s(alpha, t, R, lam):
    s = t * R
    if s > 600:
        return math.inf
    q = alpha * (math.expm1(s) - s) / (R * R * math.expm1(t * lam))
    if q >= 1:
        return math.inf
    return -math.log1p(-q)


KAPPAS = [10 ** (-5 + 6.5 * i / 52) for i in range(53)]
LAMS = (1e-4, 3e-4, 1e-3, 3e-3, 0.01, 0.03, 0.1, 0.3, 0.55, 0.7, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 30.0, 100.0)


def ln_count_s(alpha, nu, d, R):
    """per n: ln #{a in ({0} u [d, R])^u : sum a^2 <= alpha n}, u = nu n: <= nu H(kap/nu) + kap ln(R - d + 1)."""
    kap = min(nu, alpha / (d * d))
    if kap <= 0:
        return 0.0
    return nu * H(kap / nu) + kap * math.log(R - d + 1)


def excluded_s(alpha, b, R, ent):
    for lam in LAMS:
        if lam * b >= alpha:
            continue
        for k in KAPPAS:
            t = k / R
            v = nlnG_s(alpha, t, R, lam)
            if v < math.inf and lam * b + (v + ent) / t < alpha:
                return True
    return False


def excluded_step_s(a0, a1, b, R, ent):
    for lam in LAMS:
        if lam * b >= a0:
            continue
        for k in KAPPAS:
            t = k / R
            v = nlnG_s(a1, t, R, lam)
            if v < math.inf and lam * b + (v + ent) / t < a0:
                return True
    return False


def A_star_s(b, R, d, nu, e_s):
    """per n: alpha* with every alpha in [alpha*, nu R^2] excluded (1.1-geometric verification)."""
    E = lambda a: ln_count_s(a, nu, d, R) + e_s
    amax = nu * R * R
    if amax <= 0:
        return 0.0
    hi = min(max(1e-12, 4 * b), amax)
    while not excluded_s(hi, b, R, E(hi)):
        hi *= 2
        if hi >= amax:
            return amax
    lo = 0.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if excluded_s(mid, b, R, E(mid)):
            hi = mid
        else:
            lo = mid
    a = hi * 1.001
    a0 = a
    while a < amax:
        a1 = min(amax, a * 1.1)
        if not excluded_step_s(a, a1, b, R, E(a1)):
            return amax if a1 >= amax else A_star_s_restart(b, R, d, nu, e_s, a1)
        a = a1
    return a0


def A_star_s_restart(b, R, d, nu, e_s, start):
    E = lambda a: ln_count_s(a, nu, d, R) + e_s
    amax = nu * R * R
    a = start
    while a < amax:
        a0 = a
        ok = True
        while a < amax:
            a1 = min(amax, a * 1.1)
            if not excluded_step_s(a, a1, b, R, E(a1)):
                ok = False
                break
            a = a1
        if ok:
            return a0
        a = a * 1.1
    return amax


TT_B = tuple(10 ** (-4.5 + 0.25 * i) for i in range(22))
LAMS_B = tuple(10 ** (-9 + 0.25 * i) for i in range(53))


def k_bool_s(b, d, nu, e_s):
    """per n: kap0 such that every kap in [kap0, nu] is excluded: kap_lo d > lam b + (-ln(1 - kap g(t)/(e^{t lam}-1))
    + nu H(kap/nu) + e_s)/t."""
    def rhs(kk):
        best = math.inf
        E = nu * H(min(1.0, kk / nu)) + e_s
        for lam in LAMS_B:
            for tt in TT_B:
                if tt * lam > 700:
                    continue
                q = kk * (math.expm1(tt) - tt) / math.expm1(tt * lam)
                if q >= 1:
                    continue
                best = min(best, lam * b + (-math.log1p(-q) + E) / tt)
        return best
    if nu <= 0:
        return 0.0
    grid = [nu]
    x = nu
    while x > nu * 1e-12:
        x /= 1.05
        grid.append(x)
    grid = sorted(grid)
    k0 = 0.0
    for i in range(len(grid) - 1, -1, -1):
        klo = grid[i - 1] if i > 0 else 0.0
        if not (klo * d > rhs(grid[i])):
            k0 = grid[i]
            break
    return k0


def mult_excess_s(Hh, sigma, e_s, c=1):
    """per n: max_S sum_u (M_u - c)_+ / n, M_u ~ Bin(Hh, sigma), union e_s per n."""
    if Hh <= c:
        return 0.0
    from math import lgamma, log
    K = min(Hh, int(Hh * sigma + 12 * math.sqrt(Hh * sigma + 1) + 80))
    ks = np.arange(K + 1)
    lp = np.array([lgamma(Hh + 1) - lgamma(k + 1) - lgamma(Hh - k + 1) + k * log(sigma) + (Hh - k) * math.log1p(-sigma)
                   for k in range(K + 1)])
    rK = (Hh - K) / (K + 1) * sigma / (1 - sigma) if K < Hh else 0.0
    if K <= c:
        return 0.0 if K == Hh else math.inf
    base = lp[c + 1:]
    kk = ks[c + 1:]
    best = math.inf
    for t in [0.02 * 1.12 ** i for i in range(80)]:
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
        best = min(best, (math.log1p(math.exp(lse)) + e_s) / t)
    return best


def kmax_sources_s(alpha, d, sigma):
    """per n: sigma * w + partial, with sigma * F(w) <= alpha, F(w) = sum_{q<w} (d+q)^2."""
    S = lambda x: x * (x + 1) * (2 * x + 1) / 6
    F = lambda w: S(d + w - 1) - S(d - 1)
    lo, hi = 0, 1
    while sigma * F(hi) <= alpha:
        hi *= 2
        if hi > 1 << 40:
            return math.inf
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if sigma * F(mid) <= alpha:
            lo = mid
        else:
            hi = mid
    rem = alpha - sigma * F(lo)
    return sigma * lo + min(sigma, rem / (d + lo) ** 2)


CS = (1, 2, 3, 5, 8, 13, 20, 30, 50, 80, 130, 200)


def escapes_s(b, sigma, f, L0x=0, ratio=1.6, eps=EPS_DEFAULT, dtop=None, verbose=False):
    """per n: escapes for sets of size sigma n at density b, all n >= n0 (ln-terms <= eps n). Levels from
    L0 = ceil(b) + L0x upward; above level offset dtop the remaining rows are bounded by the Boolean count
    at that level times the per-source row bound (tail, conservative): see the final tail term."""
    L0 = math.ceil(b) + L0x
    e_S = sigma * (1 - math.log(sigma)) + eps if sigma > 0 else eps     # lbinom(n, s)/n <= sigma ln(e/sigma)
    total = sigma * L0
    lo = L0
    if dtop is None:
        dtop = 4 * f
    while lo - b < dtop:
        off = lo - b
        hi = max(lo + 1, math.ceil(b + max(off + 8, off * ratio)))
        R = math.ceil(hi - b)
        nu = (hi - lo) * sigma
        d = math.floor(lo + 1 - b)
        A = A_star_s(b, R, d, nu, e_S)
        k = kmax_sources_s(A, d, sigma) if d >= 1 else math.inf
        if d >= 1:
            k = min(k, k_bool_s(b, d, nu, e_S))
        cnt = min(k * c + mult_excess_s(hi - lo, sigma, e_S + eps, c) for c in CS if c <= hi - lo or c == 1)
        if d >= 1:
            cnt = min(cnt, A / (4 * max(d - 1, 0.5)) + k)
        lev = min(sigma * (hi - lo), cnt)
        if verbose:
            print(f"   level [{lo}, {hi}) d={d}: A*={A:.3e} k={k:.3e} cnt={cnt:.3e} -> {lev:.3e}")
        total += lev
        lo = hi
    # tail above dtop: every remaining source has z - b >= dtop; Boolean count kap at d = dtop bounds the
    # number of such (source, row-block) incidences; each such source contributes at most its multiplicity:
    # bound by the full alpha_inf / dtop (sum of (z - b) over sources above, from the A* at the top level)
    d = int(dtop)
    R = 64 * d
    nu = sigma * R
    A = A_star_s(b, R, d, nu, e_S)
    tail = A / d
    total += tail
    if verbose:
        print(f"   tail above offset {dtop}: A*={A:.3e} -> {tail:.3e}")
    return total - f * sigma


if __name__ == "__main__":
    f, J = 3967.0, 5e5
    b, sigma = float(sys.argv[1]), float(sys.argv[2])
    e = escapes_s(b, sigma, f, verbose=True)
    print(f"b={b} sigma={sigma:.3e}: escapes/n <= {e:.4e}   allowed b/J = {b / J:.4e}   {'OK' if e < b / J else 'FAIL'}")
