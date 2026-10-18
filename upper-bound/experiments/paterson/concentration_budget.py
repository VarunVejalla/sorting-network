"""Scalar accounting for recursive supported-separator concentration.

No networks are built. Uses the existing support/error/fringe contract;
rounds fringe sizes up to multiples of 32 so recursive inputs stay admissible.
"""
from functools import lru_cache
from fractions import Fraction as F


SUPPORT = F(1, 50)
ERROR = sum((F(1, d) for d in (199, 110, 109, 106, 90)), F(0))


def ceil32(x):
    return 32 * ((x.numerator + 32*x.denominator - 1) // (32*x.denominator))


@lru_cache(None)
def concentration(m, k):
    """Return (fixed core size, sequential separator rounds, separator nodes)."""
    if k == 0:
        return 0, 0, 0
    if m <= 32 or k > SUPPORT*m:
        return m, 0, 0
    fringe = 32 * ((m + 1023)//1024)
    if fringe >= m:
        return m, 0, 0
    leaked = (ERROR*k).numerator // (ERROR*k).denominator
    dirty = concentration(fringe, min(k, fringe))
    clean = concentration(m-fringe, min(leaked, m-fringe))
    return (dirty[0]+clean[0], 1+max(dirty[1], clean[1]),
            1+dirty[2]+clean[2])


def main():
    A, mu, delta, nu = F(19,4), F(199,10000), F(1,57), F(707,1000)
    root = F(300000)/nu**2
    pool = int(root + 32 + root/(4*A*A-1))
    rounds = 0
    for level in (2, 4):
        m = ceil32(root*A**level + 32)
        bound = mu*delta**(level-1)*root*A**level
        k = bound.numerator//bound.denominator
        core, depth, nodes = concentration(m, k)
        print(f"level {level}: bag-size upper budget={m}, wrong-half budget={k}, "
              f"core={core}, rounds={depth}, nodes={nodes}")
        pool += 2**level*core
        rounds = max(rounds, depth)
    h = (pool-1).bit_length()
    sort_depth = h*(h+1)//2
    print(f"Uniform size-budget example: pool={pool}, ceil(log2 pool)={h}, "
          f"bitonic pool sorting depth={sort_depth}")
    print(f"At existing separator depth 989: repair budget={989*rounds+sort_depth}")
    print("Actual bag sizes can be smaller. The example is not a uniform theorem "
          "over every allowed size; no monotonicity of this recursion is assumed.")


if __name__ == "__main__":
    main()
