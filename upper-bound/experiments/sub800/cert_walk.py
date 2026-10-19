#!/usr/bin/env python3
"""Interval certificate of the walk-bound bulk precision (ROUND2.md, n-uniform form) on a range of
column heights m, for the R1 point (README.md): d(m) <= eps_B for every integer m in [M_LO, M_HI].

Per column (n-uniform; the 1/n terms are taken at n = 16, valid for all n >= 16, ROUND2 sec. 6):
  round 1:  phi1(p, m) = sm * (lmgf1(t1) + H(p) + ln(15/eta1)/16) / t1,      sm = sqrt(m p (1-p)),
            lmgf1(t) = ln(1 + t * int_0^inf exp(t y - y^2 / (2 (1 + b y / (3 sm)))) dy),  b = 1 - p,
            valid for 0 < t < 3 sm/(2b) (Freedman tail of the walk maximum, in units of sm).
            For tiny p (cell [0, P0]):  M <= #ones,  ln E e^{tM} <= m p (e^t - 1).
            E1 m = 2 sup_p phi1   (R/n = E1 m).
  round 2:  phi2(p, m) = lam (R/n + (g-1)/2) + (lmgf2(t2) + H(p) + (ln G + ln(15/eta2))/16) / t2,
            lmgf2(t) = ln(a/(a-t) + b/(b-t) - (a+b)/(a+b-t)),  a <= theta*(p, lam), b <= theta*(1-p, lam)
            (any rate below theta* keeps Ville's supermartingale), G = ceil(m/g), g odd.
            d(m) = 2 sup_p phi2 / m.
Every parameter (t1, lam, t2, g) is a fixed rational per cell, found by the float optimizer of
../walk-bound/na_precision.py at the cell centre; only its evaluation is certified (mpmath.iv,
outward rounding), uniformly over the p-cell and the m-cell.

Run:  python -I cert_walk.py [M_LO M_HI EPS_B_NUM EPS_B_DEN]      (env NCELL_M: m-cells, default 40)
      cert_walk.out:  NCELL_M=48 python -I cert_walk.py 50859009 67108864 1 105000
      (m = row count of the rectangle, i.e. m+1 in R1-PROOF's padded notation)
"""
import math
import os
import sys
from fractions import Fraction as Fr

from mpmath import iv, mpf

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "walk-bound"))
import na_precision as NP  # noqa: E402

iv.dps = 30
ETA1, ETA2 = Fr(1, 100), Fr(1, 1000)
P0 = Fr(1, 10 ** 6)                 # cell [0, P0] handled by the crude Poisson bound


def I(x):
    x = Fr(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


def Hiv(p):
    """binary entropy over an interval p within [0, 1]: monotone on each side of 1/2."""
    def H(q):
        if q <= 0 or q >= 1:
            return iv.mpf(0)
        q = iv.mpf(q)
        return -q * iv.log(q) - (1 - q) * iv.log(1 - q)
    lo, hi = p.a, p.b
    if hi <= mpf(1) / 2:
        return iv.mpf([H(lo).a, H(hi).b])
    if lo >= mpf(1) / 2:
        return iv.mpf([H(hi).a, H(lo).b])
    return iv.mpf([min(H(lo).a, H(hi).a), iv.log(2).b])


def rat(x, den=10 ** 9):
    return Fr(x).limit_denominator(den)


# ------------------------------------------------------------------ round 1
def lmgf1_up(t, p, m, K=400):
    """rigorous upper end of lmgf1(t) uniformly for p in the interval p, m in the interval m."""
    b = 1 - p
    sm = iv.sqrt(m * p * (1 - p))
    smlo = iv.mpf(sm.a)                          # integrand decreasing in sm: use its lower end
    tt = I(t)
    assert (tt * 2 * b / (3 * smlo)).b < 1, "t1 too large for the Freedman MGF"
    Yq = 4 * Fr(t) + 20                          # exact rational cut point
    # integral over [0, Y]: upper Riemann sum with interval enclosure on each piece
    tot = iv.mpf(0)
    for q in range(K):
        y = iv.mpf([I(Yq * q / K).a, I(Yq * (q + 1) / K).b])
        ex = tt * y - y * y / (2 * (1 + b * y / (3 * smlo)))
        tot += iv.exp(iv.mpf(ex.b)) * (I(Yq * (q + 1) / K) - I(Yq * q / K))
    # tail y >= Y: y^2/(2(1 + b y/(3 sm))) >= kap y with kap = Y/(2(1 + bY/(3 sm)))
    kap = I(Yq) / (2 * (1 + b.b * I(Yq) / (3 * smlo)))
    kap = iv.mpf(kap.a)
    assert (kap - tt).a > 0
    tail = iv.exp((tt - kap) * I(Yq)) / (kap - tt)
    return iv.log(1 + tt * (tot + tail)).b


def phi1_up(pc, mc, t):
    """per-column round-1 bound, upper end, for p in pc, m in mc (wires)."""
    lm = lmgf1_up(t, pc, mc)
    c = iv.mpf(lm) + Hiv(pc) + iv.log(I(15) / I(ETA1)) / 16
    sm = iv.sqrt(mc * pc * (1 - pc))
    return (sm * c / I(t)).b


def phi1_small(mc):
    """End cells of round 1.  p in [0, P0]: M <= #ones in the column, so
    ln E e^{tM} <= m p (e^t - 1) <= m P0 (e^t - 1) and x <= (m P0 (e^t-1) + H(P0) + ln(15/eta1)/16)/t.
    p in [1-P0, 1): every increment is at most 1 - p, so M <= m (1 - p) <= m P0 deterministically."""
    best = None
    c0 = Hiv(iv.mpf([0, I(P0).b])) + iv.log(I(15) / I(ETA1)) / 16
    for t in (Fr(1, 2), Fr(1), Fr(2), Fr(3)):
        tt = I(t)
        v = (mc.b * I(P0) * (iv.exp(tt) - 1) + c0) / tt
        best = v.b if best is None else min(best, v.b)
    return max(best, (mc.b * I(P0)).b)


# ------------------------------------------------------------------ round 2
def fmax(T, p, L):
    """upper end of max_{q in p} f(T; q), f(T; q) = ln(1 - q + q e^T) - T (q + lam).  f is concave in q
    (log of an affine function minus a linear one), so the max is at an endpoint or at the stationary
    point q* = ((e^T - 1)/T - 1)/(e^T - 1), which is enclosed in interval arithmetic."""
    def f(q):
        return iv.log(1 - q + q * iv.exp(T)) - T * (q + L)
    vals = [f(iv.mpf(p.a)).b, f(iv.mpf(p.b)).b]
    E = iv.exp(T) - 1
    qs = ((E / T) - 1) / E
    if qs.b >= p.a and qs.a <= p.b:
        lo = max(qs.a, p.a)
        hi = min(qs.b, p.b)
        vals.append(f(iv.mpf([lo, hi])).b)
    return max(vals)


def theta_lo(p, lam):
    """theta <= theta*(q, lam) for every q in the interval p: f(theta; q) <= 0 for all q in p, where
    f(theta; q) = ln(1 - q + q e^theta) - theta (q + lam) is convex in theta with f(0) = 0 and
    f'(0) = -lam < 0, so {theta > 0 : f <= 0} = (0, theta*(q)]."""
    if (p.a + I(lam)).a >= 1:                     # the drifted walk cannot rise: rate infinite
        return None
    guesses = []
    for q in (float(p.a), float(p.b)):
        if 0 < q < 1 and q + float(lam) < 1:
            guesses.append(NP.theta_star(q, float(lam)))
    th = min(guesses)
    L = I(lam)
    for k in range(400):
        cand = th * 0.97 ** k
        T = iv.mpf(cand)
        if fmax(T, p, L) <= 0:
            return mpf(cand)
    raise RuntimeError("no certified theta lower bound")


def lmgf2_up(t, a, b):
    tt = I(t)

    def r(c):
        return iv.mpf(1) if c is None else iv.mpf(c) / (iv.mpf(c) - tt)
    for c in (a, b):
        assert c is None or c > float(t)
    ab = None if (a is None or b is None) else iv.mpf(a) + iv.mpf(b)   # interval sum
    val = r(a) + r(b) - (iv.mpf(1) if ab is None else r(ab))
    return iv.log(val).b


def phi2_up(pc, mc, lam, t, Rn, g, G):
    a = theta_lo(pc, lam)
    b = theta_lo(1 - pc, lam)
    if a is None and b is None:
        return (I(lam) * (Rn + I(Fr(g - 1, 2)))).b
    lm = lmgf2_up(t, a, b)
    c = iv.mpf(lm) + Hiv(pc) + (iv.log(G) + iv.log(I(15) / I(ETA2))) / 16
    return (I(lam) * (Rn + I(Fr(g - 1, 2))) + c / I(t)).b


# ------------------------------------------------------------------ cells and driver
def pcells(n_mid=160):
    """cover [P0, 1 - P0]: geometric near the ends, uniform in the middle."""
    edges = [P0]
    x = P0
    while x < Fr(1, 20):
        x = min(Fr(1, 20), rat(float(x) * 1.25))
        edges.append(x)
    for j in range(1, n_mid + 1):
        edges.append(Fr(1, 20) + Fr(9, 10) * j / n_mid)
    x = Fr(1, 20)
    tail = []
    while x > P0:
        x = max(P0, rat(float(x) / 1.25))
        tail.append(1 - x)
    edges += tail
    return list(zip(edges[:-1], edges[1:]))


def opt_t1(p, m):
    v = p * (1 - p)
    sm = math.sqrt(m * v)
    tmax = NP.tmax_walkmax(p, sm)
    f = lambda t: (NP.lmgf_walkmax(t, p, sm) + 16 * NP.H(p) / 16 + math.log(15 / float(ETA1)) / 16) / t
    from scipy import optimize
    r = optimize.minimize_scalar(f, bounds=(tmax * 1e-3, tmax * 0.97), method="bounded")
    return rat(r.x, 10 ** 6)


def certify(m_lo, m_hi, epsB, ncell_m=4):
    ok = True
    edges = [m_lo + (m_hi - m_lo) * j // ncell_m for j in range(ncell_m + 1)]
    worst_d = 0.0
    for ma, mb in zip(edges[:-1], edges[1:]):
        mc = iv.mpf([ma, mb])
        # round 1
        sup1 = phi1_small(mc)
        cells = pcells()
        for pa, pb in cells:
            pc = iv.mpf([I(pa).a, I(pb).b])
            pm = float((pa + pb) / 2)
            t1 = opt_t1(pm, float(ma))
            sup1 = max(sup1, phi1_up(pc, mc, t1))
        Rn = (2 * iv.mpf(sup1)).b                   # R/n = E1 m (upper end, uniform over the m-cell)
        E1 = (Rn / ma).b
        # round 2 parameters: grid spacing g odd ~ 0.02 E1 m
        g = 2 * math.floor(max(1.0, 0.02 * float(E1) * ma) / 2) + 1
        Rp_float = float(Rn) * 16 + 16 * (g - 1) / 2
        sup2 = 0.0
        for pa, pb in [(Fr(0), P0)] + cells + [(1 - P0, Fr(1))]:
            pc = iv.mpf([I(pa).a, I(pb).b])            # exact rational ends (I(0) = 0, I(1) = 1)
            pm = min(max(float((pa + pb) / 2), 1e-7), 1 - 1e-7)
            lnN = 16 * NP.H(pm) + math.log(math.ceil(mb / g)) + math.log(15 / float(ETA2))
            _, lam = NP.round2_size(pm, 16, Rp_float, lnN)
            lam = rat(lam, 10 ** 12)
            a = theta_lo(pc, lam)
            b = theta_lo(1 - pc, lam)
            rates = [x for x in (a, b) if x is not None]
            t2 = rat(0.5 * float(min(rates)), 10 ** 9) if rates else Fr(1)
            # optimize t2 below min rate on a small grid
            best = None
            for frac in (0.2, 0.35, 0.5, 0.65, 0.8, 0.9):
                tt = rat(frac * float(min(rates)), 10 ** 9) if rates else Fr(1)
                try:
                    v = phi2_up(pc, mc, lam, tt, iv.mpf(Rn), g, -(-mb // g))
                except AssertionError:
                    continue
                best = v if best is None else min(best, v)
            sup2 = max(sup2, best)
        d = (2 * iv.mpf(sup2) / ma).b
        worst_d = max(worst_d, float(d))
        good = d <= float(epsB)
        ok &= good
        print(f"  m in [{ma}, {mb}]: E1 <= {float(E1):.5e} (R/n <= {float(Rn):.2f}), g = {g}, "
              f"d <= {float(d):.5e}  {'OK' if good else 'FAIL'} vs eps_B = {float(epsB):.5e}", flush=True)
    return ok, worst_d


def main():
    a = sys.argv[1:]
    m_lo, m_hi = (int(a[0]), int(a[1])) if a else (52703924, 66137831)
    epsB = Fr(int(a[2]), int(a[3])) if len(a) >= 4 else Fr(1, 105000)
    print(f"walk-bound bulk certificate, m in [{m_lo}, {m_hi}], n-uniform (n >= 16), eta1 = 1/100, eta2 = 1/1000")
    ok, wd = certify(m_lo, m_hi, epsB, int(os.environ.get("NCELL_M", "40")))
    print(f"\nworst certified d = {wd:.5e};", "CERTIFIED" if ok else "NOT CERTIFIED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
