#!/usr/bin/env python3
"""Property B precision by negative association + Chernoff (ROUND2.md).

Both rounds replace the earlier routes of walk_precision.py:
  round 1: B(sigma) = max_S sum_j M_j,  M_j = max_h W_j^S(h).  The M_j are negatively associated
           (NA) across columns, so E exp(t sum M_j) <= prod E exp(t M_j); each M_j has Freedman's
           tail.  Replaces mean + slice McDiarmid.
  round 2: weak duality,  sum_j X_j(delta_j) <= lam R' + sum_j Y_j(lam),  Y_j = sup_h (X_j(h) - lam|h|).
           Y_j is dominated by the max of two independent exponentials (Ville's inequality on the
           exponential supermartingale), and the Y_j are NA.  The union over the base row uses a
           grid of spacing g (any base row works because sum_j W_j(i') = 0), at the price
           R' = R + n g / 2.  Replaces peeling + Cauchy-Schwarz (no ln ln m term).

Conventions follow BULK2.md:  excess < (E1/2) m n after round 1;  excess < (d/2) m n after round 2,
for states of exact mass n i, so R = sum_j |c'_j - i| = 2 exc < E1 m n.
Failure budgets: round 1 eta1 = 1/100, round 2 eta2 = 1/1000 (BULK2's split), each spread over the
sizes s = 1..n-1 (and, in round 2, the base-row grid).

Run:  python -I na_precision.py
"""
import math
import os
import sys

import numpy as np
from scipy import integrate, optimize

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
sys.path.insert(0, HERE)
import exchange_rate as E  # noqa: E402
import walk_precision as WP  # noqa: E402

N_CERT = 16
ETA1 = 1e-2
ETA2 = 1e-3


def H(p):
    return -p * math.log(p) - (1 - p) * math.log(1 - p)


P_GRID = [k / 64 for k in range(1, 64)]


def sizes(n, uniform):
    """(p, ln binom) pairs.  uniform: binom(n, s) <= exp(n H(p)) on a fine p grid, with n = 16 in
    the 1/n terms; the per-column bound then covers every n >= 16 (ln((n-1)/eta)/n and ln(G)/n
    decrease in n) up to the sup over continuous p, which the grid only samples."""
    if uniform:
        return [(p, n * H(p)) for p in P_GRID]
    return [(s / n, lbinom(n, s)) for s in range(1, n)]


def lbinom(n, s):
    return math.lgamma(n + 1) - math.lgamma(s + 1) - math.lgamma(n - s + 1)


def chernoff(lmgf, lnN, n, tmax):
    """min_t (n lmgf(t) + lnN)/t over 0 < t < tmax: a bound on sum_j Y_j failing w.p. <= exp(-lnN)."""
    f = lambda t: (n * lmgf(t) + lnN) / t
    r = optimize.minimize_scalar(f, bounds=(tmax * 1e-6, tmax * (1 - 1e-9)), method="bounded",
                                 options=dict(xatol=tmax * 1e-10))
    return r.fun


# ---------------------------------------------------------------- round 1

def lmgf_walkmax(t, p, sm):
    """log E exp(t M), M = max_{h<=m} W(h) in units of sqrt(m v), Freedman tail
    P(M >= y) <= exp(-y^2 / (2 (1 + b y / (3 sm)))),  b = 1 - p,  sm = sqrt(m v).
    E e^{tM} <= 1 + t int_0^inf e^{t y} P(M >= y) dy  (finite for t < 3 sm / (2 b))."""
    b = 1 - p
    ex = lambda y: t * y - y * y / (2 * (1 + b * y / (3 * sm)))
    ys = np.linspace(0, 4 * t + 20, 2001)
    top = max(ex(y) for y in ys)
    val, _ = integrate.quad(lambda y: math.exp(ex(y) - top), 0, math.inf, limit=400)
    return np.logaddexp(0.0, math.log(t * val) + top)


def tmax_walkmax(p, sm):
    return min(30.0, 0.99 * 3 * sm / (2 * (1 - p)))


def e1_na(L, n=N_CERT, eta=ETA1, uniform=False):
    m = 2.0 ** L
    worst = 0.0
    for p, lb in sizes(n, uniform):
        v = p * (1 - p)
        sm = math.sqrt(m * v)
        lnN = lb + math.log((n - 1) / eta)
        x = chernoff(lambda t: lmgf_walkmax(t, p, sm), lnN, n, tmax_walkmax(p, sm)) * sm   # bound on sum_j M_j
        worst = max(worst, x)
    return 2 * worst / (m * n)


# ---------------------------------------------------------------- round 2

def theta_star(p, lam):
    """Positive root of log(1 - p + p e^th) = th (p + lam): the exponential rate for
    sup_h (W(h) - lam h), W a centered Bernoulli(p) walk.  inf if the drifted walk cannot rise."""
    if p + lam >= 1:
        return math.inf
    if p <= 0:
        return math.inf
    def f(th):
        if th > 30:                     # log(1 - p + p e^th) = th + log(p + (1-p) e^-th)
            return th * (1 - p - lam) + math.log(p + (1 - p) * math.exp(-th))
        return math.log1p(p * math.expm1(th)) - th * (p + lam)
    lo = lam / (p * (1 - p))            # f(lo) < 0  (f ~ v th^2/2 - lam th near 0)
    hi = 2 * lo
    while f(hi) < 0:
        hi *= 2
    while f(lo) >= 0:
        lo /= 2
    return optimize.brentq(f, lo, hi, xtol=1e-300, rtol=1e-14)


def lmgf_twoexp(t, a, b):
    """log of the bound a/(a-t) + b/(b-t) - (a+b)/(a+b-t) on E exp(t max(Y+, Y-)),
    P(Y+ >= x) <= e^{-a x},  P(Y- >= x) <= e^{-b x},  Y+ and Y- independent."""
    def r(c):
        return 1.0 if math.isinf(c) else c / (c - t)
    return math.log(r(a) + r(b) - r(a + b))


def round2_size(p, n, Rp, lnN):
    """min over lam of  lam R' + (Chernoff bound on sum_j Y_j(lam))."""
    def g(llam):
        lam = math.exp(llam)
        a, b = theta_star(p, lam), theta_star(1 - p, lam)
        tmax = min(a, b)
        if math.isinf(tmax):                # the drifted walks cannot rise: Y_j = 0
            return lam * Rp
        return lam * Rp + chernoff(lambda t: lmgf_twoexp(t, a, b), lnN, n, tmax)
    # scale: lam ~ sqrt(n v / R')
    l0 = math.log(math.sqrt(n * p * (1 - p) / Rp))
    r = optimize.minimize_scalar(g, bounds=(l0 - 4, l0 + 4), method="bounded", options=dict(xatol=1e-6))
    return r.fun, math.exp(r.x)


GAMMAS = [0, 0.0025, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2]
GAMMAS_U = [0.005, 0.01, 0.02]      # the range where GAMMAS optimizes for lg m >= 30


def d_na(L, E1, n=N_CERT, eta=ETA2, gamma=None, uniform=False):
    """Round-2 precision d (excess < (d/2) m n) for round-1 precision E1.  gamma: grid spacing
    g ~ gamma * E1 * m rows, rounded to an odd integer so that each grid row covers exactly g
    integer rows within (g-1)/2 <= g/2 (None: best of GAMMAS; 0: union over every base row)."""
    m = 2.0 ** L
    R = E1 * m * n
    gammas = [gamma] if gamma is not None else (GAMMAS_U if uniform else GAMMAS)
    best = None
    for gm in gammas:
        if gm == 0:
            Rp, G = R, m
        else:
            g = 2 * math.floor(max(1.0, gm * E1 * m) / 2) + 1
            Rp, G = R + n * (g - 1) / 2, math.ceil(m / g)
        worst = 0.0
        for p, lb in sizes(n, uniform):
            lnN = lb + math.log(G) + math.log((n - 1) / eta)
            phi, _ = round2_size(p, n, Rp, lnN)
            worst = max(worst, phi)
        d = 2 * worst / (m * n)
        if best is None or d < best[0]:
            best = (d, gm)
    return best


# ---------------------------------------------------------------- tables

def tables(Ls=None, uniform=True):
    Ls = np.arange(8.0, 100.01, 1.0) if Ls is None else Ls
    e1 = np.array([e1_na(L, uniform=uniform) for L in Ls])
    d = np.array([d_na(L, e, uniform=uniform)[0] for L, e in zip(Ls, e1)])
    return Ls, e1, d


def need(fn, target, lo=30.0, hi=46.0):
    for _ in range(22):
        mid = (lo + hi) / 2
        if fn(mid) <= target:
            hi = mid
        else:
            lo = mid
    return hi


def main():
    print("round 1 (NA Chernoff) and round 2 (duality + NA Chernoff), n = 16, eta1 = 1/100, eta2 = 1/1000")
    print("  lg m | E1: L6.1     walk(McD)  NA        | d: BULK2    walk sketch  NA (E1=NA)  grid")
    for L in (16, 20, 25, 30, 35, 39, 42):
        e_old, e_w, e_na = float(E.eps1(L)), WP.e1_new(L), e1_na(L)
        d_old, d_w = E.eps2_scalar(L), WP.d_new(L)
        d2, gm = d_na(L, e_na)
        print(f"  {L:4d} |    {e_old:.3e}  {e_w:.3e}  {e_na:.3e} |    {d_old:.3e}  {d_w:.3e}    {d2:.3e}   {gm}",
              flush=True)
    print("\nconstants: E1 = 2 K1 / sqrt(m),  d = 2 C2 sqrt(E1 / m)")
    for L in (20, 30, 39, 42):
        m = 2.0 ** L
        e = e1_na(L)
        d2, _ = d_na(L, e)
        print(f"  lg m = {L}:  K1_NA = {e * math.sqrt(m) / 2:.3f}  (McDiarmid route {WP._K1:.3f});  "
              f"C2_NA = {d2 / (2 * math.sqrt(e / m)):.3f}  (sketch sqrt(K2) = "
              f"{WP.d_new(L) / (2 * math.sqrt(WP.e1_new(L) / m)):.3f})")
    print("\nper-column constants vs n (lg m = 39):  K1_NA, C2_NA")
    for n in (16, 32, 64, 256):
        m = 2.0 ** 39
        e = e1_na(39, n=n)
        d2, _ = d_na(39, e, n=n)
        print(f"  n = {n:4d}:  {e * math.sqrt(m) / 2:.3f}  {d2 / (2 * math.sqrt(e / m)):.3f}", flush=True)
    t = 1 / 59e6
    print(f"\ncolumn height for the 1419 package's bulk target d = 1/59e6 (two rounds):")
    print(f"  BULK2 route              : lg m = {need(E.eps2_scalar, t):.2f}   (BULK2.md: 41.66)")
    print(f"  walk sketch (WALK-BOUND) : lg m = {need(WP.d_new, t):.2f}")
    print(f"  NA, both rounds          : lg m = {need(lambda L: d_na(L, e1_na(L))[0], t):.2f}")
    print(f"  NA round 2, McD round 1  : lg m = {need(lambda L: d_na(L, WP.e1_new(L))[0], t):.2f}")
    print(f"  NA, both rounds, n-uniform (all n >= 16, p grid 1/64): lg m = "
          f"{need(lambda L: d_na(L, e1_na(L, uniform=True), uniform=True)[0], t):.2f}")
    L = 37.5
    eu, ee = e1_na(L, uniform=True), e1_na(L)
    du, de = d_na(L, eu, uniform=True), d_na(L, ee)
    print(f"  at lg m = {L}: E1 n=16 {ee:.4e}, n-uniform {eu:.4e};  d n=16 {de[0]:.4e} (gamma {de[1]}), "
          f"n-uniform {du[0]:.4e} (gamma {du[1]})")


if __name__ == "__main__":
    main()
