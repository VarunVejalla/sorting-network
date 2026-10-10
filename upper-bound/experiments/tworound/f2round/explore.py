"""Floating-point exploration of the two-stage (R1 / R2) two-round F proof.  NOT a certificate.

Notation (see F2ROUND.md):
  SR   : small ranks j<=J.  sigma1 event: some top t in tops(g0,n,j0) and column c with H_c >= f-g0+1.
  R1a_E: some top t in tops(g1,n,jE), some (kap+1)-set S with sum_S H >= (D+1)(kap+1), D=g2-g1.
  R1b_E: some top t, some s-set (1<=s<=kap) with sum_S H >= D*s + B.
  R2_E : some y with |supp y|<=kap, sum y <= B-1, some S (s>=1) with hits >= (f-g2)s + E.
"""
import math
LN = math.log
J = 86_000_000
DELTA = 128 / 4095

def lntops(g, n, j):
    k = int(j // (g + 1))
    if k == 0:
        return 0.0
    return LN(k + 1) + k * LN(math.e ** 2 * n * j / k ** 2)

def chern(n, s, M, T):
    """ln[C(n,s) (e M s/(n T))^T], requires T >= M s/n."""
    assert T >= M * s / n, (n, s, M, T)
    return s * LN(math.e * n / s) + T * LN(math.e * M * s / (n * T))

def lse(xs):
    mx = max(xs)
    return mx + LN(sum(math.exp(x - mx) for x in xs))

def sr(f, g0, n):
    j0 = min(J, math.floor(DELTA * f * n))
    if j0 <= f:
        return -math.inf
    T0 = f - g0 + 1
    return lntops(g0, n, j0) + chern(n, 1, j0, T0)

def r1a(f, g1, g2, n, jE, kap):
    D = g2 - g1
    return lntops(g1, n, jE) + chern(n, kap + 1, jE, (D + 1) * (kap + 1))

def r1b(f, g1, g2, n, jE, kap, B):
    D = g2 - g1
    lt = lntops(g1, n, jE)
    # terms decrease in s (checked numerically); bound sum by kap * max over a few s and s=1
    terms = [lt + chern(n, s, jE, D * s + B) for s in sorted(set([1, 2, 3, max(1, kap // 2), kap]))]
    return LN(kap) + max(terms)

def lnY(n, kap, B):
    if kap == 0:
        return 0.0
    return LN(kap + 1) + kap * LN(math.e ** 2 * n * (B - 1) / kap ** 2)

def r2(f, g2, n, E, kap, B):
    terms = [chern(n, s, B - 1, (f - g2) * s + E) for s in (1, 2, 3)]
    return lnY(n, kap, B) + lse(terms) + LN(1.01)

def best_E(f, g1, g2, n, E):
    jE = min(E * J, math.floor(DELTA * f * n))
    best = None
    # kappa: smallest with r1a <= target; B: smallest with r1b <= target; target = -(E+10)
    for tgt in (10, 20, 30):
        target = -(tgt + E * 0.0)
        lo, hi = 0, 10 ** 12
        while lo < hi:
            mid = (lo + hi) // 2
            if r1a(f, g1, g2, n, jE, mid) <= target: hi = mid
            else: lo = mid + 1
        kap = lo
        lo, hi = 2, 10 ** 15
        while lo < hi:
            mid = (lo + hi) // 2
            if kap == 0 or r1b(f, g1, g2, n, jE, kap, mid) <= target: hi = mid
            else: lo = mid + 1
        B = lo
        v2 = r2(f, g2, n, E, kap, B) if kap > 0 else -math.inf
        v = max(target, v2)
        if best is None or v < best[0]:
            best = (v, kap, B, v2)
    return best

if __name__ == "__main__":
    import sys
    f = int(sys.argv[1]) if len(sys.argv) > 1 else 131040
    for (a1, a2) in [(0.3, 0.6), (0.35, 0.7), (0.4, 0.8), (0.3, 0.7), (0.45, 0.9), (0.25, 0.5)]:
        g1, g2 = int(a1 * f), int(a2 * f)
        worst = (-1e300, None)
        for n in [int(J / (DELTA * f) * t) + 1 for t in (1.01, 1.5, 2, 3, 10, 100, 1e3, 1e4, 1e6, 1e9)]:
            Emax = math.ceil(DELTA * f * n / J)
            for E in sorted(set([2, 3, 5, 10, 30, 100, 300, 1000, 3000, 1e4, 3e4, 1e5, 3e5, 1e6, 1e7, 1e8, 1e9, Emax])):
                E = int(E)
                if E > Emax: continue
                v = best_E(f, g1, g2, n, E)
                if v[0] > worst[0]: worst = (v[0], (n, E, v))
        print(f, a1, a2, "SR(n=1e9)=%.1f" % sr(f, g1, 10 ** 9), "worst R2/R1 log=%.2f" % worst[0], worst[1])
