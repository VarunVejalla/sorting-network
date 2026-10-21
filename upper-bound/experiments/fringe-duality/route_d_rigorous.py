"""Route (d), rigorous in form (floats; not interval-certified). See ROUND1-ENERGY.md, "Route (d): the
Kingman MGF lemma".

Fixed-set lemma (round 1). U fixed (depends on sigma2 only), weights a in {0..R}^U, rho = sum a / n,
drift lam > 0, walk increments X = a_{sigma1_r(c)} - rho - lam (iid over rows, mean -lam).
  * Y_c = max_h S_h <= M (infinite-horizon sup). M =_d max(0, X + M), and e^{t max(0,y)} = e^{ty} + (1-e^{ty})_+,
    so G(1 - phi) = E(1 - e^{-t (X+M)_-}) <= 1 - e^{-t E(X+M)_-} = 1 - e^{-t lam}   (concavity; E(X+M)_- = -EX).
    Hence  E e^{t Y_c} <= G <= (1 - e^{-t lam}) / (1 - phi(t)),  phi(t) = E e^{tX}.
  * phi(t) <= e^{-t lam} (1 + A g(tR) / (n R^2)),  A = sum a^2, g(s) = e^s - 1 - s
    (convexity of g(s)/s^2 and e^{-y}(1+y) <= 1). So n ln G <= -n ln(1 - A g(tR) / (n R^2 (e^{t lam} - 1))).
  * NA across columns (per-row permutation of a fixed vector), Chernoff, union over a in {0..R}^U and the
    choices of U: for all a, sum_c Y_c <= x(A) = min_t [n ln G + Ent] / t.
  * Deterministic: sum_U a (z - b) <= lam j + sum_c Y_c with b = j/n (the rho j term is b sum a);
    a_T = min(R, floor((z_T - b)_+)) gives A <= lam j + x(A).
Round 2 (sigma2, per set S of s2 columns): rows of v in S are split into levels [lo, hi).
  count_i(S) <= #{u in U_i(S) : a_u >= floor(lo + 1 - b)} + sum_u (M_u - 1)_+
             <= A_i / floor(lo + 1 - b)^2 + Mex_i,
  U_i(S) = {sigma2_r^{-1}(v) : v in S, lo <= r < hi}, |U_i| <= (hi - lo) s2, cap R = ceil(hi - b),
  M_u = #{r in [lo, hi) : sigma2_r(u) in S} ~ Bin(hi - lo, s2/n), NA across u; Mex_i by Chernoff + union over S.
  Rows r < L0 (L0 >= ceil(b)) are free. Rows >= Kmax are empty (single-column round-1 bound).
Escapes(S) = sum_{v in S} w_v - f s2 <= s2 L0 + sum_i min(s2 (hi - lo), count_i) - f s2.
"""
import math
import sys
from functools import lru_cache

ETA = 1e-4


def lbinom(n, k):
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def nlnG(A, t, R, lam, n):
    s = t * R
    if s > 600:
        return math.inf
    g = math.expm1(s) - s
    q = A * g / (n * R * R * math.expm1(t * lam))
    if q >= 1:
        return math.inf
    return -n * math.log1p(-q)


KAPPAS = [10 ** (-3 + 4.5 * i / 40) for i in range(41)]
LAMS = (0.55, 0.6, 0.7, 0.8, 1.0, 1.25, 1.5, 2.0, 3.0)


def ln_count(A, u, d, R):
    """ln #{a in ({0} u [d, R])^u : sum a^2 <= A} <= ln(k+1) + ln binom(u, k) + k ln(R - d + 1), k = min(u, A/d^2)
    (terms increase in k up to k ~ u)."""
    k = min(u, int(A / (d * d)))
    if k <= 0:
        return 0.0
    return math.log(k + 1) + lbinom(u, k) + k * math.log(R - d + 1)


def excluded(A, j, R, n, Ent):
    """True if some (lam, t) shows A > lam j + x(A) (so no profile with sum a^2 = A survives)."""
    for lam in LAMS:
        if lam * j >= A:
            continue
        for k in KAPPAS:
            t = k / R
            v = nlnG(A, t, R, lam, n)
            if v < math.inf and lam * j + (v + Ent) / t < A:
                return True
    return False


@lru_cache(maxsize=100000)
def A_star(j, R, d, u, n, ent_extra):
    """Level weights a in {0} u [d, R] on |U| = u. Union per A-interval [A_k, A_{k+1}] over vectors with
    sum a^2 <= A_{k+1} (ln_count) plus ln(#intervals). Bisect for the threshold, then verify every interval
    from A* up to 1e3 A* (1.1-geometric) with lam j + x_t(A_{k+1}) < A_k; beyond, t -> 0 gives x ~ A/(2 lam)
    plus Ent(A)/t with Ent(A) <= (A/d^2) ln(e u R) sublinear... (checked numerically to 1e3 A*)."""
    E = lambda A: ln_count(A, u, d, R) + ent_extra + math.log(200)
    hi = max(1.0, 4 * j + 10)
    while not excluded(hi, j, R, n, E(hi)):
        hi *= 2
        if hi > 1e30:
            return math.inf
    lo = 0.0
    for _ in range(30):
        mid = (lo + hi) / 2
        if excluded(mid, j, R, n, E(mid)):
            hi = mid
        else:
            lo = mid
    A = hi * 1.001
    while True:
        A0, ok = A, True
        while A < 1e3 * A0:
            if not excluded_step(A, A * 1.1, j, R, n, E(A * 1.1)):
                ok = False
                break
            A *= 1.1
        if ok:
            return A0
        A = A * 1.1
        if A > 1e30:
            return math.inf


_LAST = [(1.0, 20)]


def excluded_step(A0, A1, j, R, n, Ent):
    """All A in [A0, A1] excluded: some (lam, t) with lam j + x_t(A1) < A0 (x_t increasing in A).
    Tries the last successful (lam, t) first."""
    cands = _LAST + [(lam, i) for lam in LAMS for i in range(len(KAPPAS))]
    for lam, i in cands:
        if lam * j >= A0:
            continue
        t = KAPPAS[i] / R
        v = nlnG(A1, t, R, lam, n)
        if v < math.inf and lam * j + (v + Ent) / t < A0:
            _LAST[0] = (lam, i)
            return True
    return False


@lru_cache(maxsize=100000)
def mult_excess(H, s2, n, ent, c=1):
    """max over S (|S| = s2) of sum_u (M_u - c)_+, M_u ~ Bin(H, s2/n), NA across u; Chernoff + union (ent).
    E e^{t (M-c)_+} - 1 = sum_{k > c} P(M = k)(e^{t(k-c)} - 1) <= sum_{k > c} P(M = k) e^{t(k-c)}: summed in
    log space; terms are log-concave in k, so past the peak the tail is bounded by a geometric series."""
    p = s2 / n
    if H <= c or p >= 1:
        return 0.0 if H <= c else math.inf
    lr = math.log(p) - math.log1p(-p)
    best = math.inf
    for t in [0.02 * 1.12 ** i for i in range(80)]:
        k = c + 1
        lpk = lbinom(H, k) + k * math.log(p) + (H - k) * math.log1p(-p)
        terms, prev = [], None
        while k <= H:
            x = lpk + t * (k - c)
            terms.append(x)
            if prev is not None and x < prev and x < max(terms) - 40:
                ratio = math.exp(x - prev)
                terms.append(x + math.log(ratio / (1 - ratio)))
                break
            prev = x
            lpk += math.log((H - k) / (k + 1)) + lr if k < H else 0.0
            k += 1
        mx = max(terms)
        lse = mx + math.log(sum(math.exp(y - mx) for y in terms))
        if lse > 600:
            continue
        val = (n * math.log1p(math.exp(lse)) + ent) / t
        best = min(best, val)
    return best


def kmax_sources(A, d, s2):
    """Largest k with sum_{q<k} (d + floor(q/s2))^2 <= A (the q-th active source, ordered by its lowest
    counted row, sits at row >= lo + floor(q/s2): at most s2 i pairs lie below lo + i)."""
    if A == math.inf:
        return math.inf
    S = lambda x: x * (x + 1) * (2 * x + 1) / 6
    F = lambda w: S(d + w - 1) - S(d - 1)          # full per-column rows
    lo, hi = 0, 1
    while s2 * F(hi) <= A:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if s2 * F(mid) <= A:
            lo = mid
        else:
            hi = mid
    rem = A - s2 * F(lo)
    return s2 * lo + min(s2, int(rem / (d + lo) ** 2))


CS = (1, 2, 3, 5, 8, 13, 20, 30, 50, 80, 130, 200, 320, 500, 800, 1300, 2000)


def Kmax(j, n):
    """Round-1 single-column bound: U = {T}, union over n targets; z - b < sqrt(A*)."""
    R = int(3 * math.sqrt(j)) + 10
    A = A_star(round(j), R, 1, 1, n, math.log(n / ETA) + 3 * math.log(R + 1))
    if A >= R * R:
        return math.inf
    return math.sqrt(A)


def escapes(j, n, f, s2, L0_extra, ratio, s2_lo=None):
    """Escape bound for every round-2 set S with s2_lo <= |S| <= s2 (s2_lo = s2 by default).
    Every count term is nondecreasing in |S| (larger U, entropy lbinom(n, s) for s <= n/2, kmax_sources,
    Bin(H, s/n)), and -(f - L0)|S| is decreasing, so evaluating counts at s2 and the linear term at s2_lo
    bounds the whole interval."""
    if s2_lo is None:
        s2_lo = s2
    b = j / n
    K = Kmax(j, n)
    top = b + K + 1
    L0 = math.ceil(b) + L0_extra
    ent_S = lbinom(n, s2) + math.log(n) + 2 * math.log(top + 2) + math.log(1 / ETA) + 4
    total = 0.0
    lo = L0
    while lo < top:
        hi = min(math.ceil(top), max(lo + 1, int(lo * ratio)))
        R = math.ceil(hi - b)
        u = min(n, (hi - lo) * s2)
        d = math.floor(lo + 1 - b)
        A = A_star(round(j), R, d, u, n, ent_S)
        k = kmax_sources(A, d, s2)
        cnt = min(k * c + mult_excess(hi - lo, s2, n, ent_S + math.log(len(CS)), c) for c in CS if c <= hi - lo or c == 1)
        total += min(s2 * (hi - lo), cnt)
        lo = hi
    return total - (f - L0) * s2_lo


def main():
    n = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 ** 20
    J = float(sys.argv[2]) if len(sys.argv) > 2 else 1.66e6
    f = float(sys.argv[3]) if len(sys.argv) > 3 else 4000
    mults = [float(x) for x in sys.argv[4].split(",")] if len(sys.argv) > 4 else [1, 10, 100, 300]
    jmax = f * n / 8
    print(f"n = 2^{math.log2(n):.0f}, J = {J:.3g}, f = {f:.0f}, jmax = {jmax / J:.0f} J", flush=True)
    for mult in mults:
        j = mult * J
        if j > jmax:
            continue
        K = Kmax(j, n)
        worst = None
        # s2 = 1 exactly, then every interval [s, 2s] up to j / f (at most j / f columns can be overloaded)
        ivs = [(1, 1)] + [(2 ** i, 2 ** (i + 1)) for i in range(60) if 2 ** i <= max(1, j / f)]
        for sa, sb in ivs:
            e = min(escapes(j, n, f, sb, L0x, r, sa) for L0x in (0, 50, 200) for r in (1.3, 1.6, 2.0))
            if worst is None or e > worst[0]:
                worst = (e, sb)
        print(f"  j = {mult:8g} J (b = {j / n:7.1f}, Kmax = {K:7.0f}): worst escapes {worst[0]:12.1f} at s2 = {worst[1]:5d}"
              f"  vs allowed {j / J:10.1f}  {'OK' if worst[0] < j / J else 'FAIL'}", flush=True)


if __name__ == "__main__":
    main()
