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
import numpy as np
import sys
from functools import lru_cache

ETA = 1e-4
NR = 1.0      # n-interval: every bound below holds for all n' in [n, NR n] (n = n_lo). Decreasing terms use n,
              # increasing terms (entropies) use NR n; the multiplicity pmf uses p_hi = s2/n and (1 - p_lo)^(H-k).


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


KAPPAS = [10 ** (-5 + 6.5 * i / 52) for i in range(53)]
LAMS = (0.55, 0.6, 0.7, 0.8, 1.0, 1.25, 1.5, 2.0, 3.0, 5.0, 10.0, 30.0, 100.0, 1e3, 1e4)


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
    Amax = float(u) * R * R          # weights are capped at R on u sources: A <= u R^2 always
    hi = min(max(1.0, 4 * j + 10), Amax)
    while not excluded(hi, j, R, n, E(hi)):
        hi *= 2
        if hi >= Amax:
            return Amax
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
        while A < min(1e3 * A0, Amax):
            if not excluded_step(A, A * 1.1, j, R, n, E(A * 1.1)):
                ok = False
                break
            A *= 1.1
        if ok:
            return A0
        A = A * 1.1
        if A >= Amax:
            return Amax


@lru_cache(maxsize=100000)
def A_coll(j, R, u, n, ent):
    """Collision lemma (n-uniform; uncentred weights a in {0..R}^U, a_T = min(R, z_T) 1{z_T >= d}):
    Y_c <= single-hit value + R M_c, M_c = max{N(h) : N(h) >= 2, N(h) >= lam h / R} (N = hits on U, which
    depends on U only: no union over profiles). P(M_c >= k) <= q^k / (1 - q), q = e R u / (lam n).
    Bijection rows: sum of single-hit values <= A / (2 lam). So A <= (lam j + x_D) / (1 - 1/(2 lam)),
    x_D = min_s R [n ln(1 + (q e^s)^2 / ((1-q)(1 - q e^s))) + ent] / s."""
    best = math.inf
    for lam in (0.6, 0.75, 1.0, 1.5, 2.0, 3.0):
        q = math.e * R * u / (lam * n)
        if q >= 1:
            continue
        for s in [0.05 * 1.1 ** i for i in range(120)]:
            qe = q * math.exp(min(s, 700))
            if qe >= 1:
                break
            g = n * math.log1p(qe * qe / ((1 - q) * (1 - qe)))
            xD = R * (g + ent) / s
            best = min(best, (lam * j + xD) / (1 - 1 / (2 * lam)))
    return best


TT_B = tuple(10 ** (-4.5 + 0.25 * i) for i in range(22))   # t from 3e-5 to 5
LAMS_B = tuple(10 ** (-7 + 0.25 * i) for i in range(45))   # Boolean drift: optimum ~ sqrt(k / 2j)


@lru_cache(maxsize=100000)
def k_bool(j, d, u, n, ent):
    """Centred Boolean level count: k = #{T in U : z_T - b >= d}. Weights a = 1 on those k sources:
    k d <= sum_K (z - b) <= lam j + sum_c Y_c (drift rho + lam, rho = k/n), Kingman MGF with unit jumps:
    n ln G <= -n ln(1 - k g(t) / (n (e^{t lam} - 1))), g(t) = e^t - 1 - t; union over K (ln binom(u, k))
    and the choices of U (ent). Returns the least k0 such that every k in [k0, u] is excluded (checked on a
    1.05-geometric grid with the interval step: k_lo d > RHS(k_hi))."""
    def rhs(kk):
        best = math.inf
        E = lbinom(u, min(u, kk)) + ent + math.log(400)
        for lam in LAMS_B:
            for tt in TT_B:
                if tt * lam > 700:
                    continue
                q = kk * (math.expm1(tt) - tt) / (n * math.expm1(tt * lam))
                if q >= 1:
                    continue
                val = lam * j + (-n * math.log1p(-q) + E) / tt
                best = min(best, val)
        return best
    if u <= 0:
        return 0
    # scan from the top down: find the largest k (grid) not excluded
    grid = sorted(set([u] + [int(math.ceil(1.05 ** i)) for i in range(int(math.log(max(u, 2)) / math.log(1.05)) + 2)] ))
    grid = [g for g in grid if 1 <= g <= u]
    k0 = 0
    for i in range(len(grid) - 1, -1, -1):
        klo = grid[i - 1] if i > 0 else 0
        khi = grid[i]
        if not (max(klo, 1) * d > rhs(khi)):
            k0 = khi
            break
    return k0


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


@lru_cache(maxsize=4096)
def _binom_logpmf(H, p):
    """log P(Bin(H, p) = k) for k = 0..K, with K past the mode where the pmf has fallen by e^-60 and is
    decreasing; beyond K the ratio of consecutive terms is <= r_K < 1 (log-concave), returned for a
    geometric tail bound."""
    mode = int((H + 1) * p)
    K = min(H, mode + int(12 * math.sqrt(H * p + 1)) + 80)
    k = np.arange(K + 1)
    lgk = np.array([math.lgamma(x + 1) for x in range(K + 1)])
    lp = math.lgamma(H + 1) - lgk - np.array([math.lgamma(H - x + 1) for x in range(K + 1)])         + k * math.log(p) + (H - k) * math.log1p(-p)
    rK = (H - K) / (K + 1) * p / (1 - p) if K < H else 0.0
    return lp, rK


@lru_cache(maxsize=100000)
def mult_excess(H, s2, n, ent, c=1):
    """max over S (|S| = s2) of sum_u (M_u - c)_+, M_u ~ Bin(H, s2/n), NA across u; Chernoff + union (ent).
    E e^{t (M-c)_+} - 1 <= sum_{k > c} P(M = k) e^{t(k-c)}; terms beyond the table K are bounded by a
    geometric series with ratio r_K e^t (needs r_K e^t < 1)."""
    p = s2 / n
    if H <= c:
        return 0.0
    if p >= 1:
        return math.inf
    lp, rK = _binom_logpmf(H, p)
    shift = H * (math.log1p(-p / NR) - math.log1p(-p)) if NR > 1 else 0.0   # (1-p_lo)^(H-k) / (1-p_hi)^(H-k)
    K = len(lp) - 1
    if K <= c:
        return 0.0 if K == H else math.inf
    ks = np.arange(c + 1, K + 1)
    base = lp[c + 1:]
    best = math.inf
    for t in [0.02 * 1.12 ** i for i in range(80)]:
        x = base + t * (ks - c)
        mx = float(x.max())
        lse = mx + math.log(float(np.exp(x - mx).sum()))
        if K < H:
            q = rK * math.exp(t)
            if q >= 1:
                continue
            xl = lp[K] + t * (K - c) + math.log(q / (1 - q))
            lse = max(lse, xl) + math.log1p(math.exp(min(lse, xl) - max(lse, xl)))
        if lse > 600:
            continue
        val = (NR * n * math.log1p(math.exp(lse + shift)) + ent) / t
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
    A = A_star(round(j), R, 1, 1, n, math.log(NR * n / ETA) + 3 * math.log(R + 1))
    Ac = A_coll(round(j), R, 1, n, math.log(NR * n / ETA))
    A = min(A, Ac)
    if A >= R * R:
        return float(j)          # trivial: a column holds at most the whole mass
    return min(float(j), math.sqrt(A))


def escapes(j, n, f, s2, L0_extra, ratio, s2_lo=None, j_lo=None):
    """Escape bound for every round-2 set S with s2_lo <= |S| <= s2 and every mass j_lo <= j' <= j
    (defaults: s2_lo = s2, j_lo = j). Every count term is nondecreasing in |S| (larger U, entropy
    lbinom(n, s) for s <= n/2, kmax_sources, Bin(H, s/n)) and -(f - L0)|S| is decreasing; in j' the
    lemma uses lam j (<= lam j), the cap R = ceil(hi - b_lo) (>= hi - b'), the level floor
    d = floor(lo + 1 - b) (<= floor(lo + 1 - b')), free rows L0 >= ceil(b) (>= ceil(b')) and Kmax at j."""
    if s2_lo is None:
        s2_lo = s2
    if j_lo is None:
        j_lo = j
    b = j / n
    b_lo = j_lo / (NR * n)
    K = Kmax(j, n)
    top = b + K + 1
    L0 = math.ceil(b) + L0_extra
    ent_S = lbinom(NR * n, s2) + math.log(NR * n) + 2 * math.log(top + 2) + math.log(1 / ETA) + 4
    total = 0.0
    lo = L0
    while lo < top:
        # levels geometric in the offset above b (also right when b is small)
        off = lo - b
        hi = min(math.ceil(top), max(lo + 1, math.ceil(b + max(off + 8, off * ratio))))
        R = math.ceil(hi - b_lo)
        u = min(NR * n, (hi - lo) * s2)
        d = math.floor(lo + 1 - b)
        A = A_star(math.ceil(j), R, d, u, n, ent_S)
        k = kmax_sources(A, d, s2)
        # n-uniform alternative: uncentred collision lemma, cap hi, threshold lo + 1
        Ac = A_coll(math.ceil(j), hi, u, n, ent_S)
        k = min(k, kmax_sources(Ac, lo + 1, s2))
        if d >= 1:
            k = min(k, k_bool(math.ceil(j), d, u, n, ent_S))       # centred Boolean level count
        cnt = min(k * c + mult_excess(hi - lo, s2, n, ent_S + math.log(len(CS)), c) for c in CS if c <= hi - lo or c == 1)
        if d >= 1:   # count <= sum_u (min(z_u, hi) - lo)_+ <= sum a (a - d + 1)_+ <= A / (4 (d - 1)) + ... (AM-GM)
            cnt = min(cnt, A / (4 * max(d - 1, 0.5)) + k)
        total += min(s2 * (hi - lo), cnt)
        lo = hi
    return total - (f - L0) * s2_lo


def load_bound(jb, n, f, s, ja):
    """L_b(s) >= max_{|S| = s} sum_{v in S} w_v for every j in [ja, jb] (best over L0, level ratio)."""
    return min(escapes(jb, n, f, s, L0x, r, s, ja) + f * s for L0x in (0, 50, 200) for r in (1.3, 1.6, 2.0))


def worst_interval(ja, jb, n, f, smax=4096):
    """Escapes bound for all j in [ja, jb] and all set sizes. L(s) = sum of the s largest loads, so L(s)/s is
    nonincreasing: once L_b(s0)/s0 < f, every s >= s0 has escapes <= 0. Exact points s = 1, 2, ... up to
    that s0 (geometric steps with the interval bound past 64, as a fallback)."""
    worst = (-math.inf, 0)
    s = 1
    while s <= smax and s <= max(1, jb / f):
        L = load_bound(jb, n, f, s, ja)
        worst = max(worst, (L - f * s, s))
        if L / s < f:
            return worst
        s += 1
        if s > 64:
            break
    # past 64: grid s_a < s_b (ratio 1.05). For s in [s_a, s_b]: L(s)/s <= L(s_a)/s_a and L(s) <= L(s_b), so
    # escapes(s) <= min(s_b (L_b(s_a)/s_a - f), L_b(s_b) - f s_a).
    sa, La = s - 1, load_bound(jb, n, f, s - 1, ja)
    while sa <= max(1, jb / f):
        sb = max(sa + 1, int(sa * 1.05))
        Lb = load_bound(jb, n, f, sb, ja)
        worst = max(worst, (min(sb * (La / sa - f), Lb - f * sa), sb))
        if Lb / sb < f:
            return worst
        sa, La = sb, Lb
    return worst


FMAX = None   # fringe-class ladder: if set, j runs to FMAX n/8 with f_eff = max(f, 8 j_a/n) (escapes decrease in f)


def sweep(n, J, f, jfrom, jto, ratio=1.15):
    """Cover [jfrom, jto] by geometric intervals (split at J). Contract: escapes = 0 (bound < 1) for j < J,
    escapes < j/J for j >= J."""
    f0 = f
    jmax = (FMAX if FMAX else f) * NR * n / 8
    jto = min(jto, jmax)
    ja = jfrom
    while ja < jto:
        jb = min(jto, ja * ratio)
        if ja < J < jb:
            jb = J
        allowed = 1.0 if jb <= J else ja / J
        if FMAX:
            f = max(f0, 8 * ja / (NR * n))
        e, s = worst_interval(ja, jb, n, f)
        print(f"  j in [{ja / J:10.4g}, {jb / J:10.4g}] J: worst {e:12.1f} at s2 <= {s:7d}  allowed {allowed:10.1f}"
              f"  {'OK' if e < allowed else 'FAIL'}", flush=True)
        ja = jb


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
    if len(sys.argv) > 1 and sys.argv[1] == "sweep":
        n_, J_, f_ = int(float(sys.argv[2])), float(sys.argv[3]), float(sys.argv[4])
        if len(sys.argv) > 7 and float(sys.argv[7]) > 0:
            FMAX = float(sys.argv[7])
        if len(sys.argv) > 8:
            NR = float(sys.argv[8])
        print(f"sweep n = 2^{math.log2(n_):.0f}, J = {J_:.3g}, f = {f_:.0f}, j in [{sys.argv[5]}, {sys.argv[6]}]"
              f"{', f-ladder to %.3g (f_eff = max(f, 8 j_a/n))' % FMAX if FMAX else ''}"
              f"{', all n in [n, %g n]' % NR if NR > 1 else ''}", flush=True)
        sweep(n_, J_, f_, float(sys.argv[5]), float(sys.argv[6]))
    else:
        main()
