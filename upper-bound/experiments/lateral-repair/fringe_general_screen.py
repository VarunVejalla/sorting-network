#!/usr/bin/env python3
"""UB-15 screen: the F2ROUND two-round fringe proof at moderate precision, with the n >= 16 clamp.

Float screen (math.log, no outward rounding); a passing point should then be re-certified with
interval arithmetic.  Transcribes the general log-bounds of
upper-bound/best/notes/two-round/F2ROUND.md sec. 3 and evaluates them at the worst admissible point
of sec. 4, which is the *smallest* column count compatible with the rank:

  SR      at n = max(16, J/D),        j0 = J
  R1a/b_E at n = max(16, E J / D),    j  = E J
  R2_E    at n = max(16, (E-1) J / D)

The original cert.py substitutes n = E J / D everywhere.  That is only admissible when E J / D >= 16;
at moderate J = 1/eps_F it is not, so small E must be evaluated at n = 16.  Large E use the original
linear-in-E closed forms (valid there) for the tail sums.

Notation (F2ROUND sec. 1): f fringe rows, g1 < g2 < f, Delta = g2 - g1, Phi = f - g2, D = delta*f,
kappa_E = ceil(cE), B_E = ceil(bE), J = 1/eps_F.

Run:  python -I fringe_general_screen.py
"""
import math
import sys

import numpy as np

LN = math.log
EN = math.e


def L_tops(g, n, j):
    K = j / (g + 1)
    return LN(K + 1) + K * LN(EN ** 2 * n * (g + 1) ** 2 / j)


def ltail(lam, E0, deg):
    """ln of an upper bound on sum_{E >= E0} E^deg e^{-lam E}, in log space (no underflow)."""
    x = -lam + deg / E0
    if x >= 0:
        return math.inf
    return -lam * E0 + deg * LN(E0) - LN(-math.expm1(x))


def psi_star(J, D, Dl, b):
    """max over sigma > 0 of psi(sigma) = sigma ln(eJ/(sigma D)) + (Dl sigma + b) ln(e D sigma/(Dl sigma + b)); concave."""
    def psi(lsig):
        sg = math.exp(lsig)
        return sg * LN(EN * J / (sg * D)) + (Dl * sg + b) * LN(EN * D * sg / (Dl * sg + b))
    lo, hi = -40.0, 40.0
    for _ in range(200):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if psi(m1) < psi(m2):
            lo = m1
        else:
            hi = m2
    return psi((lo + hi) / 2) + 1e-6 * abs(psi((lo + hi) / 2))   # small safety margin


def logsumexp(xs):
    m = max(xs)
    if m == -math.inf:
        return m
    return m + LN(sum(math.exp(x - m) for x in xs))


def screen(f, g1, g2, c, b, J, delta, Emax=4000):
    """Return (ok, details): ln of the sigma1 and sigma2 failure sums, one orientation."""
    D = delta * f
    Dl, Phi = g2 - g1, f - g2
    pre = [0 < g1 < g2 < f, Dl + 1 >= D, f - g1 + 1 >= D, (g1 + 1) ** 2 >= D, c <= 0.5]
    if not all(pre):
        return False, "precondition"
    # SR
    n = max(16.0, J / D)
    j0 = min(J, D * n)
    T0 = f - g1 + 1
    if T0 < j0 / n:
        return False, "SR chernoff"
    SR = L_tops(g1, n, j0) + LN(EN * n) + T0 * LN(EN * j0 / (n * T0))
    # R1a, R1b per E, then linear tails
    r1 = []
    E_lin = None
    for E in range(2, Emax + 1):
        n = max(16.0, E * J / D)
        j = E * J
        if j > D * n * (1 + 1e-12):
            return False, "rank above Dn"
        kap = math.ceil(c * E)
        B = math.ceil(b * E)
        Lt = L_tops(g1, n, j)
        a = Lt + (kap + 1) * LN(EN * n / (kap + 1)) + (Dl + 1) * (kap + 1) * LN(EN * j / (n * (Dl + 1)))
        s = np.arange(1, kap + 1, dtype=float)
        T = Dl * s + B
        if np.any(T < j * s / n):
            return False, f"R1b chernoff E={E}"
        bb = Lt + LN(kap) + float(np.max(s * np.log(EN * n / s) + T * np.log(EN * j * s / (n * T))))
        r1 += [a, bb]
        if E * J / D >= 16 and E >= 50:
            E_lin = E
            break
    # tail for R1 with n = E J / D: per-E bound is linear in E with slopes from sec. 4
    if E_lin is None:
        E_lin = Emax
    alpha = J / (g1 + 1)
    ts = alpha * LN(EN ** 2 * (g1 + 1) ** 2 / D)
    beta = LN(EN * J / (c * D)) + (Dl + 1) * LN(EN * D / (Dl + 1))
    lam_a = -(ts + c * beta)
    lam_b = -(ts + psi_star(J, D, Dl, b))
    if not (beta < 0 and lam_a > 0 and lam_b > 0):
        return False, "R1 tail slopes"
    E0 = E_lin + 1
    # R1a tail: e^beta sum (alpha E + 1) e^{-lam_a E};  R1b tail: sum (cE+1)(alpha E+1) e^{-lam_b E}
    r1.append(beta + LN(alpha + 1) + ltail(lam_a, E0, 1))
    r1.append(LN((c + 1) * (alpha + 1)) + ltail(lam_b, E0, 2))
    P1 = logsumexp([SR] + r1)
    # R2 per E
    r2 = []
    for E in range(2, Emax + 1):
        n = max(16.0, (E - 1) * J / D)
        kap = math.ceil(c * E)
        B = math.ceil(b * E)
        if kap * kap > n * (B - 1):
            return False, f"Y-count validity E={E}"
        lnY = LN(kap + 1) + kap * LN(EN ** 2 * n * (B - 1) / kap ** 2)
        smax = int(min(n, 200000))
        s = np.arange(1, smax + 1, dtype=float)
        T = Phi * s + E
        if np.any(T < (B - 1) * s / n):
            return False, f"R2 chernoff E={E}"
        r2.append(lnY + LN(n) + float(np.max(s * np.log(EN * n / s) + T * np.log(EN * (B - 1) * s / (n * T)))))
        if (E - 1) * J / D >= 16 and E >= 200 and r2[-1] < r2[-2] - 1:
            break
    # tail: per-E bound decreases at least linearly with the last observed slope
    slope = r2[-2] - r2[-1]
    if slope <= 0:
        return False, "R2 tail not decreasing"
    r2.append(r2[-1] - slope - LN(-math.expm1(-slope)))
    P2 = logsumexp(r2)
    ok = (LN(2) + P1 <= LN(1e-3)) and (LN(2) + P2 <= LN(1e-3))
    return ok, f"ln(2P1)={LN(2) + P1:.1f} ln(2P2)={LN(2) + P2:.1f}"


def best_at(f, J, delta):
    for a in (0.2, 0.3, 0.4):
        for bf in (0.7, 0.8, 0.9):
            for c in (0.25, 1 / 3, 0.5):
                g1, g2 = int(a * f), int(bf * f)
                lo_b = J / (g1 + 1)
                for bm in (1.5, 3, 10, 30):
                    b = max(1.0, bm * lo_b)
                    ok, det = screen(f, g1, g2, c, b, J, delta)
                    if ok:
                        return (g1, g2, round(c, 3), round(b, 1), det)
    return None


DELTAS = (("128/4095", 128 / 4095), ("1/16", 1 / 16), ("1/8", 1 / 8), ("1/5", 1 / 5))


def first_pass(J, d, fmax=2 ** 22):
    """Scan f upward geometrically (the screen is not monotone over very large f at small J),
    then refine between the last failure and the first pass."""
    prev, f = 8, 16
    while f <= fmax:
        if best_at(f, J, d) is not None:
            lo, hi = prev, f
            while hi - lo > max(1, lo // 32):
                mid = (lo + hi) // 2
                if best_at(mid, J, d) is not None:
                    hi = mid
                else:
                    lo = mid
            return hi, best_at(hi, J, d)
        prev, f = f, int(f * 1.25) + 1
    return None


def main():
    # beta < 0 in R1a needs Delta + 1 > e * delta * f, so this route requires delta < 1/e.
    Js = [int(x) for x in sys.argv[1:]] or [2 ** 8, 2 ** 10, 2 ** 12, 2 ** 14, 2 ** 16, 86_000_000]
    for J in Js:
        for dname, d in DELTAS:
            r = first_pass(J, d)
            if r is None:
                print(f"J=2^{math.log2(J):.1f} delta={dname}: none up to f=2^22", flush=True)
            else:
                print(f"J=2^{math.log2(J):.1f} delta={dname}: smallest f ~ {r[0]}  {r[1]}", flush=True)


if __name__ == "__main__":
    main()
