"""Uniform scalar envelopes with rational logarithm interval certificates.

Bounds every integer size 1..M for a fixed wrong-key budget K. Assumes the
odd-size adapter and the monotonicity theorem already present in legacy.
This is exact Python arithmetic, not a Lean network or kernel certificate.
"""
from fractions import Fraction as F
from functools import lru_cache


@lru_cache(None)
def log_interval(x):
    assert x > 0
    shift = 0
    while x < 1:
        x *= 2
        shift -= 1
    while x >= 2:
        x /= 2
        shift += 1

    def series(z):
        t = (z-1)/(z+1)
        terms = 24
        total = 2*sum((t**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
        tail = 2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
        return total, total+tail

    lo, hi = series(x)
    l2, u2 = series(F(2))
    if shift >= 0:
        return lo+shift*l2, hi+shift*u2
    return lo+shift*u2, hi+shift*l2


def entropy_upper(x):
    lx, _ = log_interval(x)
    ly, _ = log_interval(1-x)
    return -x*lx-(1-x)*ly


@lru_cache(None)
def certified_depth(alpha, eps=F(1,4)):
    assert 0 < alpha <= 1 and 0 < eps <= F(1,2)
    _, log_upper = log_interval((1-eps)*alpha)
    denominator_lower = -eps*alpha*log_upper
    assert denominator_lower > 0
    upper = 1+(entropy_upper(eps*alpha)+entropy_upper((1-eps)*alpha))/denominator_lower
    return (upper.numerator+upper.denominator-1)//upper.denominator


@lru_cache(None)
def envelope(lo, hi, k):
    """Core/depth envelope for all integer m in [lo,hi]."""
    if lo > hi or k == 0:
        return 0, 0
    lo = max(lo, 1)
    if k == 1:
        return 1, (hi-1).bit_length()
    # Stop when K > m/10. Terminal and nonterminal sizes are separated.
    terminal_core = min(hi, 10*k-1) if lo < 10*k else 0
    active_lo = max(lo, 10*k)
    if active_lo > hi:
        return terminal_core, 0
    dirty = envelope((active_lo+1)//2, (hi+1)//2, k)
    clean = envelope(active_lo//2, hi//2, k//4)
    # alpha=K/ceil(m/2) decreases with m; use its largest value.
    c = certified_depth(F(k, (active_lo+1)//2))
    return (min(hi, max(terminal_core, dirty[0]+clean[0])),
            c+max(dirty[1], clean[1]))


def main():
    A, mu, delta, nu = F(19,4), F(199,10000), F(1,57), F(707,1000)
    root = F(300000)/nu**2
    pool = int(root+32+root/(4*A*A-1))
    depth = 0
    print("Uniform over all bag sizes up to the displayed maximum; epsilon=1/4, stop density=1/10")
    for level in (2,4):
        size = root*A**level+32
        maximum = (size.numerator+size.denominator-1)//size.denominator
        k = int(mu*delta**(level-1)*root*A**level)
        core, d = envelope(1, maximum, k)
        pool += 2**level*core
        depth = max(depth, d)
        print(f"level {level}: maximum={maximum}, K={k}, core<={core}, depth<={d}")
    h = (pool-1).bit_length()
    sort_depth = h*(h+1)//2
    print(f"pool<={pool}, full pool sort<={sort_depth}, concentration<={depth}, layout<=1")
    print(f"Conditional uniform first-split depth: {depth+sort_depth+1}")
    print(f"Remaining margin below 561: {561-depth-sort_depth-1}")
    print(f"Rational-certified uniform halver ceiling at alpha=1/5: {certified_depth(F(1,5))}")


if __name__ == "__main__":
    main()
