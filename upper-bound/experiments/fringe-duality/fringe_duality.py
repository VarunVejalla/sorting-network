#!/usr/bin/env python3
"""Fringe by double weak duality: a float screen (model, not a certificate).

Two-round separator, Boolean threshold with j ones (the top j keys). After the first column sort the
input is a staircase h (sum h = j). Round 1 gives heights z, round 2 heights w. Escapes are
sum_v (w_v - f)_+, and the contract is: escapes < j/J for every 0 < j <= jmax = delta f n
(so zero escapes for j < J).

Round 1 (exact): for any set S of output columns and lam > 0,
    sum_{v in S} z_v = sum_c N_c^S(h_c) <= lam j + Y^S(lam),   Y^S(lam) = sum_c max_h (N_c^S(h) - lam h),
where N_c^S(h) = #{r < h : sigma1_r(c) in S}. Per column the increments are Bernoulli(p = s/n); across
columns they are negatively associated (ROUND2.md sec. 4), so E exp(t Y^S) <= M(t)^n and a Chernoff
bound plus a union over the binom(n, s) sets gives Y^S(lam) <= x_s(lam) for all S at once.
Then s_k = #{u : z_u >= k} satisfies k s_k <= min_lam (lam j + x_{s_k}(lam)), which bounds
Q(j) = sum_u z_u^2 = sum_k (2k - 1) s_k.

Round 2 (exact, convex cost): for any S' and mu > 0,
    sum_{v in S'} w_v <= mu Q(j) + Y'^{S'}(mu),   Y'(mu) = sum_u max_h (N'_u(h) - mu h^2).
Max_h (N(h) - mu h^2) is a walk with quadratic drift; its tail is computed exactly by a DP over h.
Escapes <= max_s [ min_mu (mu Q(j) + x'_s(mu)) - f s ].

Run: python -I fringe_duality.py
"""
import math
import sys
from functools import lru_cache

import numpy as np

LN = math.log


def lbinom(n, s):
    return math.lgamma(n + 1) - math.lgamma(s + 1) - math.lgamma(n - s + 1)


# ---------- walk maxima with drift: rigorous tails by level crossing ----------
#
# Y = max_{h >= 1} (N(h) - D(h)), N(h) = #hits in rows < h (Bernoulli(p) per row), D increasing with
# D(0) = 0 (linear: lam h; quadratic: mu h^2). Y > y needs some level k >= floor(y) + 1 reached by the
# k-th hit time T_k with D(T_k) < k - y, i.e. T_k <= tmax(k - y); so
#     P(Y > y) <= sum_k P(T_k <= tmax(k - y)) = sum_k P(Bin(tmax(k - y), p) >= k).
# (For a linear drift Ville's inequality also gives P(Y >= y) <= exp(-theta* y); we take the minimum.)
# E exp(tY) = 1 + int_0^inf t e^{ty} P(Y > y) dy, integrated on a grid with the left-end tail (upper bound).

def log_binom_tail(T, p, k):
    """ln P(Bin(T, p) >= k), Chernoff bound (exact enough for a screen; it is an upper bound)."""
    if T < k:
        return -math.inf
    q = k / T
    if q <= p:
        return 0.0
    if q >= 1:
        return T * math.log(p)
    return -T * (q * math.log(q / p) + (1 - q) * math.log((1 - q) / (1 - p)))


def tail_walk_grid(p, kind, c, ys, mrows=2 ** 27, ratio=1.03):
    """Vectorised union bound over a geometric time grid (valid for every p):
    for h in [h_i, h_{i+1}], N(h) - D(h) <= N(h_{i+1}) - D(h_i), so
    P(Y > y) <= sum_i P(Bin(h_{i+1}, p) > y + D(h_i))  (Chernoff), plus P(N(1) > y) for h = 1."""
    hs = np.unique(np.concatenate([np.arange(1, 64), np.geomspace(64, mrows, 600)]).astype(np.int64))
    if kind == "lin":
        D = c * hs
    elif kind == "quad":
        D = c * hs.astype(float) ** 2
    else:                                       # 'cent': c = (lam, mu, b), D = lam h + mu (h - b)_+^2
        lam, mu, b = c
        hf = hs.astype(float)
        D = lam * hf + mu * np.maximum(hf - b, 0.0) ** 2
    H1 = hs[1:].astype(float)
    D0 = D[:-1]
    ys = np.asarray(ys, dtype=float)[:, None]
    k = ys + D0[None, :]                       # need Bin(H1, p) > k
    q = np.minimum(k / H1[None, :], 1.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        kl = q * np.log(q / p) + (1 - q) * np.log((1 - q) / (1 - p))
        lt = np.where(q <= p, 0.0, -H1[None, :] * kl)
        lt = np.where(k >= H1[None, :], -np.inf, lt)   # Bin(H1, p) > k >= H1 is impossible
    tot = np.where(np.isfinite(lt), np.exp(np.clip(lt, -745, 0)), 0.0).sum(axis=1)
    return np.minimum(1.0, tot)


def tail_walk(p, kind, c, ys):
    """P(Y > y) for y in ys; kind 'lin' (D = c h), 'quad' (D = c h^2) or 'cent' (c = (lam, mu, b))."""
    if kind == "cent":
        out = np.asarray(tail_walk_grid(p, kind, c, ys))
        if p <= 1e-3:
            lam, mu, b = c

            def T_of(room):
                """largest integer h >= 0 with lam h + mu (h - b)_+^2 < room."""
                if lam > 0 and room / lam <= b:
                    return int(math.ceil(room / lam)) - 1
                r0 = room - lam * b                    # remaining room at h = b (> 0 here)
                if mu > 0:
                    u = (-lam + math.sqrt(lam * lam + 4 * mu * r0)) / (2 * mu)
                elif lam > 0:
                    u = r0 / lam
                else:
                    return 2 ** 40
                return b + int(math.ceil(u)) - 1
            lev = []
            for y in ys:
                tot = 0.0
                k0 = int(math.floor(y)) + 1
                for k in range(k0, k0 + 3000):
                    lt = log_binom_tail(T_of(k - y), p, k)
                    if lt > -700:
                        tot += math.exp(lt)
                    if k > k0 + 20 and lt < -60:
                        break
                lev.append(min(1.0, tot))
            out = np.minimum(out, np.asarray(lev))
        return list(out)
    if p > 1e-3:
        out = tail_walk_grid(p, kind, c, ys)
        if kind == "quad":
            # linearise the drift at h0: mu h^2 >= 2 mu h0 h - mu h0^2, then Ville for the linear walk
            ya = np.asarray(ys, dtype=float)
            for h0 in np.geomspace(1, 2 ** 27, 160):
                lam = 2 * c * h0
                if lam <= p or lam >= 1:
                    continue
                th = theta_star(p, lam)
                b = np.where(ya > c * h0 * h0, np.exp(-th * (ya - c * h0 * h0)), 1.0)
                out = np.minimum(out, b)
        if kind == "lin":
            th = theta_star(p, c)
            if th == math.inf:
                return [0.0] * len(ys)
            if th > 0:
                out = np.minimum(out, np.exp(-th * np.asarray(ys)))
        return list(out)
    th = theta_star(p, c) if kind == "lin" else 0.0
    out = []
    for y in ys:
        tot = 0.0
        k0 = int(math.floor(y)) + 1
        for k in range(k0, k0 + 2000):
            room = k - y
            if kind == "lin":
                T = int(math.ceil(room / c)) - 1      # T_k <= T  <=>  c T_k < room
            else:
                T = int(math.ceil(math.sqrt(room / c))) - 1
            lt = log_binom_tail(T, p, k)
            if lt > -700:
                tot += math.exp(lt)
            if k > k0 + 20 and lt < -60:
                break
        if kind == "lin" and th > 0:
            tot = min(tot, math.exp(-th * y)) if math.isfinite(th) else 0.0
        out.append(min(1.0, tot))
    return out


YGRID = np.concatenate([np.arange(0, 2, 0.05), np.arange(2, 80, 0.5), np.geomspace(80, 2.0 ** 27, 200)])


@lru_cache(maxsize=4096)
def tails_cached(p, kind, c):
    return tuple(tail_walk(p, kind, c, YGRID))


def log_mgf(p, kind, c, t):
    """ln E e^{tY} <= ln(1 + sum_i (e^{t y_{i+1}} - e^{t y_i}) P(Y > y_i)), in log-sum-exp form; the tail
    beyond the last grid point is capped by 10 e^{t y_last} P(Y > y_last)."""
    P = np.asarray(tails_cached(p, kind, c))
    y0, y1 = YGRID[:-1], YGRID[1:]
    with np.errstate(divide="ignore"):
        lP = np.log(P)
        terms = t * y1 + np.log(-np.expm1(-t * (y1 - y0))) + lP[:-1]
        last = t * YGRID[-1] + lP[-1] + math.log(10)
    allt = np.concatenate([[0.0], terms, [last]])
    mx = np.max(allt)
    return float(mx + np.log(np.sum(np.exp(allt - mx))))


def theta_star(p, lam):
    """positive root of ln(1 - p + p e^th) = th * lam (exists for p < lam < 1; inf if lam >= 1)."""
    if lam <= p:
        return 0.0
    if lam >= 1:
        return math.inf

    def f(th):
        return th + math.log(p + (1 - p) * math.exp(-th)) - th * lam
    lo, hi = 1e-12, 1.0
    while f(hi) <= 0:
        lo, hi = hi, hi * 2
        if hi > 1e6:
            return hi
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo


@lru_cache(maxsize=4096)
def x_round1(n, s, lam, logfail):
    """least x with n ln E e^{tY} - t x + ln binom(n,s) + logfail <= 0 (NA across columns), over t."""
    p = s / n
    if lam >= 1:
        return 0.0
    best = math.inf
    for t in np.geomspace(0.05, 8.0, 40):
        x = (n * log_mgf(p, "lin", lam, t) + lbinom(n, s) + logfail) / t
        best = min(best, x)
    return best


@lru_cache(maxsize=4096)
def x_round2(n, s, mu, logfail):
    p = s / n
    best = math.inf
    for t in np.geomspace(0.05, 8.0, 40):
        x = (n * log_mgf(p, "quad", mu, t) + lbinom(n, s) + logfail) / t
        best = min(best, x)
    return best


# ---------- composition ----------

def s_profile(n, j, logfail, lams):
    """upper bounds s_k on #{u : z_u >= k}, k = 1, 2, ... (round 1)."""
    out = []
    k, s_prev = 1, n
    while True:
        cap = min(s_prev, j // k)
        if cap <= 0:
            break
        def ok(s):
            return all(k * s <= lam * j + x_round1(n, s, lam, logfail) for lam in lams)
        if ok(cap):
            s_k = cap
        else:
            lo, hi = 0, cap
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if ok(mid):
                    lo = mid
                else:
                    hi = mid
            s_k = lo
        if s_k <= 0:
            break
        out.append(s_k)
        s_prev = s_k
        k += 1
    return out


def excess_energy(sk, b):
    """E_b >= sum_u (z_u - b)_+^2 = sum_{k > b} (2(k - b) - 1) s_k (b integer)."""
    return float(sum((2 * (k - b) - 1) * s for k, s in enumerate(sk, start=1) if k > b))


@lru_cache(maxsize=4096)
def x_round2c(n, s, lam, mu, b, logfail):
    p = s / n
    best = math.inf
    for t in np.geomspace(0.05, 8.0, 30):
        x = (n * log_mgf(p, "cent", (lam, mu, b), t) + lbinom(n, s) + logfail) / t
        best = min(best, x)
    return best


def Q_bound(n, j, logfail, lams):
    """upper bound on sum_u z_u^2 from round 1."""
    Q = 0.0
    k = 1
    s_prev = n
    while True:
        # largest s with k s <= min_lam (lam j + x_s(lam)); s <= min(s_prev, j // k)
        cap = min(s_prev, j // k)
        if cap <= 0:
            break
        lo, hi = 0, cap
        def ok(s):
            # s_k must satisfy the bound for EVERY lam (each lam gives a valid upper bound)
            return all(k * s <= lam * j + x_round1(n, s, lam, logfail) for lam in lams)
        if ok(hi):
            s_k = hi
        else:
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if ok(mid):
                    lo = mid
                else:
                    hi = mid
            s_k = lo
        if s_k <= 0:
            break
        Q += (2 * k - 1) * s_k
        s_prev = s_k
        k += 1
        if k > 10 ** 6:
            break
    return Q


def escapes_bound(n, j, f, logfail, lams, mus):
    Q = Q_bound(n, j, logfail, lams)
    best = -math.inf
    for s in sorted(set(int(v) for v in np.unique(np.geomspace(1, n - 1, 40).astype(int)))):
        b = min(mu * Q + x_round2(n, s, mu, logfail) for mu in mus) - f * s
        best = max(best, b)
    return best, Q


def main():
    n = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 ** 20
    logfail = math.log(n * 1e4 * 100)   # failure 1e-4, union over n thresholds/sizes and a parameter grid
    lams = [float(v) for v in np.geomspace(1e-4, 0.5, 24)]
    mus = [float(v) for v in np.geomspace(1e-9, 1e-1, 36)]
    print(f"n = {n}: round-1 Q(j) bound and round-2 escapes bound (model)")
    for j in (1000, 10000, 100000, 190000):
        Q = Q_bound(n, j, logfail, lams)
        # the smallest f with zero escapes at this j: escapes bound < 1
        lo, hi = 1, 200000
        while hi - lo > 1:
            f = (lo + hi) // 2
            b = max(min(mu * Q + x_round2(n, s, mu, logfail) for mu in mus) - f * s
                    for s in (1, 2, 4, 16, 64, 256))
            if b < 1:
                hi = f
            else:
                lo = f
        print(f"  j = {j:8d}: Q <= {Q:12.0f} (Q/j = {Q / j:6.1f});  zero escapes for f >= {hi}"
              f"  (6j)^(1/3) = {(6 * j) ** (1 / 3):6.0f}, sqrt(0.9 j) = {math.sqrt(0.9 * j):6.0f}", flush=True)


if __name__ == "__main__":
    main()
