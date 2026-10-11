"""Sanity checks (not proofs) for the lemmas in BULK2.md, on small exact instances.

1. Variance identity  sum_k a_k (n - a_k) = sum_{j,l} (c_j - c_l)_+  and  V <= 2 D1 / n  at exact mass.
2. Per-row Bernoulli bound  1 - p + p e^lam <= exp(p lam + lam^2 (1/2 + 2 lam/9) p (1-p))  (grid).
3. Exact distribution of Y_S = sum_k |random a_k-subset ∩ S| (convolution of hypergeometrics):
   E e^{lam Y} <= prod_k (1-p_k+p_k e^lam)^s  and  P(Y - s i >= T) <= exp(-lam T + s c(lam) V).
"""
import itertools, math, random
from fractions import Fraction as Fr


def rows_of(c, m):
    return [sum(1 for x in c if x >= k) for k in range(1, m + 1)]


def check_variance(trials=2000):
    rng = random.Random(1)
    for _ in range(trials):
        n = rng.randint(2, 9); m = rng.randint(1, 12)
        c = [rng.randint(0, m) for _ in range(n)]
        a = rows_of(c, m)
        lhs = sum(x * (n - x) for x in a)
        rhs = sum(max(cj - cl, 0) for cj in c for cl in c)
        assert lhs == rhs, (c, lhs, rhs)
        tot = sum(c)
        if tot % n == 0:
            i = tot // n
            D1 = sum(max(x - i, 0) for x in c)
            assert Fr(lhs, n * n) <= Fr(2 * D1, n)
    print("variance identity and V <= 2 D1/n: OK")


def check_bernoulli():
    worst = 1.0
    for lam in [k / 200 for k in range(1, 201)]:
        cl = lam * lam * (0.5 + 2 * lam / 9)
        for p in [j / 400 for j in range(401)]:
            lhs = math.log1p(p * math.expm1(lam))
            rhs = p * lam + cl * p * (1 - p)
            assert lhs <= rhs + 1e-15, (lam, p)
    print("Bernoulli per-row bound on grid: OK")


def hyper_pmf(n, a, s):
    tot = math.comb(n, a)
    return {h: Fr(math.comb(s, h) * math.comb(n - s, a - h), tot)
            for h in range(max(0, a - (n - s)), min(a, s) + 1)}


def conv(p, q):
    r = {}
    for x, px in p.items():
        for y, qy in q.items():
            r[x + y] = r.get(x + y, 0) + px * qy
    return r


def check_tail(trials=300):
    rng = random.Random(7)
    for _ in range(trials):
        n = rng.randint(2, 8); m = rng.randint(1, 10)
        i = rng.randint(1, m)
        # random exact-mass state with total n*i
        c = [i] * n
        for _ in range(rng.randint(0, 3 * n)):
            j, l = rng.randrange(n), rng.randrange(n)
            if c[j] < m and c[l] > 0 and j != l:
                c[j] += 1; c[l] -= 1
        a = rows_of(c, m)
        s = rng.randint(1, n)
        dist = {0: Fr(1)}
        for ak in a:
            dist = conv(dist, hyper_pmf(n, ak, s))
        V = sum(Fr(ak, n) * (1 - Fr(ak, n)) for ak in a)
        mean = sum(y * p for y, p in dist.items())
        assert mean == s * i
        for lam in [0.05, 0.3, 1.0]:
            mgf = sum(float(p) * math.exp(lam * y) for y, p in dist.items())
            bound = math.prod((1 - ak / n + ak / n * math.exp(lam)) ** s for ak in a)
            assert mgf <= bound * (1 + 1e-12)
        for T in range(1, s * (m - i) + 1):
            tail = float(sum(p for y, p in dist.items() if y - s * i >= T))
            best = min(math.exp(-l * T + s * l * l * (0.5 + 2 * l / 9) * float(V))
                       for l in [k / 100 for k in range(1, 101)])
            assert tail <= best * (1 + 1e-12), (c, s, T, tail, best)
    print("hypergeometric MGF comparison and Bernstein-type tail on exact small cases: OK")


if __name__ == "__main__":
    check_variance(); check_bernoulli(); check_tail()
