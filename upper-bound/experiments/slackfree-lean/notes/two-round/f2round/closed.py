"""Closed-form per-E bounds for the two-stage two-round F proof (float / mpmath exploration).

All quantities are natural logs of failure probabilities, evaluated at the worst points
proved in F2ROUND.md section 4 (R1: n = E J/(delta f), j = E J;  R2: n = (E-1) J/(delta f)).
kappa_E = ceil(c E), B_E = ceil(b E).
"""
import mpmath as mp
mp.mp.dps = 40
J = mp.mpf(86_000_000)
DELTA = mp.mpf(128) / 4095
e = mp.e

def tops_slope(f, g1):
    df = DELTA * f
    return J / (g1 + 1) * mp.log(e ** 2 * (g1 + 1) ** 2 / df)

def r1a(f, g1, g2, c, E):
    """ln P(R1a_E) <= ln(K+1) + K ln(e^2 (g1+1)^2/(df)) + (cE+1)[ln(eJ/(c df)) + (D+1) ln(e df/(D+1))]."""
    df = DELTA * f; D = g2 - g1; E = mp.mpf(E)
    K = E * J / (g1 + 1)
    return (mp.log(K + 1) + E * tops_slope(f, g1)
            + (c * E + 1) * (mp.log(e * J / (c * df)) + (D + 1) * mp.log(e * df / (D + 1))))

def psi(f, g1, g2, b, sig):
    df = DELTA * f; D = g2 - g1
    return (sig * mp.log(e * J / (sig * df)) + (D * sig + b) * mp.log(e * df * sig / (D * sig + b)))

def psi_star(f, g1, g2, b):
    """sup_{sig>0} psi (psi concave): bisection on psi'(sig) = ln(J/(sig df)) + D ln(e df sig/(D sig+b)) + b/sig."""
    df = DELTA * f; D = g2 - g1
    dpsi = lambda s: mp.log(J / (s * df)) + D * mp.log(e * df * s / (D * s + b)) + b / s
    lo, hi = mp.mpf('1e-30'), mp.mpf('1e30')
    for _ in range(400):
        mid = mp.sqrt(lo * hi)
        if dpsi(mid) > 0: lo = mid
        else: hi = mid
    # concavity: sup <= psi(lo) + psi'(lo)*(hi-lo)
    return psi(f, g1, g2, b, lo) + max(dpsi(lo), 0) * (hi - lo), lo

def r1b(f, g1, g2, c, b, E):
    E = mp.mpf(E)
    K = E * J / (g1 + 1)
    ps, _ = psi_star(f, g1, g2, b)
    return mp.log(c * E + 1) + mp.log(K + 1) + E * tops_slope(f, g1) + E * ps

def r2(f, g2, c, b, E):
    """ln P(R2_E) at n = (E-1)J/df, kappa <= cE+1, B-1 <= bE."""
    df = DELTA * f; Phi = f - g2; E = mp.mpf(E)
    n = (E - 1) * J / df
    kap = c * E + 1; Bm1 = b * E
    lnY = mp.log(kap + 1) + kap * mp.log(e ** 2 * n * Bm1 / kap ** 2)
    q = mp.log(n * Phi / (e * Bm1))
    A = 1 + mp.log(n) - Phi * q
    mx = A if A <= 1 else max(A, mp.exp(A - 1))
    return lnY + mp.log(n) + mx - E * q

def sr(f, g0):
    """ln P(SR) at worst n = J/df, j0 = J, single column, T0 = f-g0+1."""
    df = DELTA * f
    n = J / df
    K = J / (g0 + 1)
    T0 = f - g0 + 1
    return mp.log(K + 1) + K * mp.log(e ** 2 * n * J / K ** 2) + mp.log(e * n) + T0 * mp.log(e * J / (n * T0))

def choose(f, g1, g2, lam=1):
    """smallest c with r1a slope <= -lam, smallest b with psi* + tops_slope <= -lam."""
    df = DELTA * f; D = g2 - g1
    ts = tops_slope(f, g1)
    lo, hi = mp.mpf('1e-6'), mp.mpf(1e6)
    for _ in range(200):
        c = (lo + hi) / 2
        s = ts + c * (mp.log(e * J / (c * df)) + (D + 1) * mp.log(e * df / (D + 1)))
        if s <= -lam: hi = c
        else: lo = c
    c = hi
    lo, hi = mp.mpf(1), mp.mpf(1e12)
    for _ in range(200):
        b = (lo + hi) / 2
        if ts + psi_star(f, g1, g2, b)[0] <= -lam: hi = b
        else: lo = b
    return c, hi

if __name__ == "__main__":
    import sys
    f = int(sys.argv[1]) if len(sys.argv) > 1 else 131040
    for a1, a2 in [(0.4, 0.8), (0.3, 0.6), (0.45, 0.9), (0.5, 0.95), (0.4, 0.9), (0.35, 0.85)]:
        g1, g2 = int(a1 * f), int(a2 * f)
        if g2 - g1 <= DELTA * f: continue
        c, b = choose(f, g1, g2)
        Es = [2, 3, 5, 10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 8, 10 ** 12, 10 ** 20]
        worst2 = max((r2(f, g2, c, b, E), E) for E in Es)
        print(f, a1, a2, "c=%.4f b=%.1f" % (c, b), "SR=%.3g" % sr(f, g1),
              "r1a(2)=%.4g r1b(2)=%.4g" % (r1a(f, g1, g2, c, 2), r1b(f, g1, g2, c, b, 2)),
              "worst r2=%.4g at E=%s" % worst2)
