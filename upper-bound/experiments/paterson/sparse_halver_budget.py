"""Exploratory budgets for adaptive sparse half-block concentration.

Entropy ceilings use floating point: candidates, not certified depth bounds.
Odd sizes assume a pure extreme dummy and a restriction adapter (unproved here).
"""
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, log, log1p


def entropy(x):
    if x == 0 or x == 1:
        return 0.0
    return -x*log(x) - (1-x)*log1p(-x)


def depth_bound(alpha, error):
    return 1 + (entropy(error*alpha) + entropy((1-error)*alpha)) / (
        -error*alpha*log((1-error)*alpha))


def evaluate(error, stop_support):
    @lru_cache(None)
    def rec(m, k):
        if k == 0:
            return 0, 0
        if k == 1:
            # A balanced comparison tournament captures the unique wrong
            # extreme key at one fixed output, if it exists.
            return 1, (m-1).bit_length()
        if m <= 2 or k > stop_support*m:
            return m, 0
        dirty = (m+1)//2
        clean = m//2
        alpha = F(k, dirty)  # halver support alpha * side size >= k
        if alpha > 1:
            return m, 0
        c = ceil(depth_bound(float(alpha), float(error)))
        leak = (error*k).numerator // (error*k).denominator
        dc, dd = rec(dirty, min(k, dirty))
        cc, cd = rec(clean, min(leak, clean))
        return dc+cc, c+max(dd, cd)

    A, mu, delta, nu = F(19,4), F(199,10000), F(1,57), F(707,1000)
    root = F(300000)/nu**2
    pool = int(root + 32 + root/(4*A*A-1))
    depth = 0
    cores = []
    for level in (2,4):
        m = ceil(root*A**level + 32)
        k = int(mu*delta**(level-1)*root*A**level)
        core, d = rec(m, k)
        cores.append(core)
        pool += 2**level*core
        depth = max(depth, d)
    h = (pool-1).bit_length()
    sorting = h*(h+1)//2
    return depth+sorting+1, depth, sorting, pool, cores


def main():
    rows = []
    for error in (F(1,8), F(1,6), F(1,5), F(1,4), F(1,3), F(2,5), F(9,20)):
        for support in (F(1,50), F(1,20), F(1,10), F(1,5), F(2,5)):
            rows.append((evaluate(error, support), error, support))
    print("Best numerical candidates: total=concentration+pool full sort+one layout layer")
    for (total, depth, sorting, pool, cores), error, support in sorted(rows)[:8]:
        print(f"e={error}, stop={support}: total={total}, concentration={depth}, "
              f"pool-sort={sorting}, pool={pool}, cores={cores}")
    print("Not uniform size bounds, not rigorous entropy ceilings, not a four-level repair theorem.")


if __name__ == "__main__":
    main()
