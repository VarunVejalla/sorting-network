"""Certified numerics for the two-round (and three-round) bulk lemma B2.  See BULK2.md.

All pass/fail decisions are made either with exact rationals (fractions.Fraction) together with
the Mathlib-available bounds 0.6931471803 < ln 2 < 0.6931471808 (Real.log_two_gt_d9 / _lt_d9),
or with mpmath interval arithmetic (mpmath.iv, outward rounding).  Floating point is used only to
*locate* thresholds (bisection); every reported threshold is then re-certified with intervals.

Notation (BULK2.md):
  d   = target eps_B2 = 1/59e6;  bad event: final excess >= T = (d/2) m n.
  E1  = first-round guarantee (round-1 excess < (E1/2) m n), so V := sum_k p_k(1-p_k) < E1 m.
  lam = MGF parameter (fixed constant, 0 < lam <= 1);  c(lam) = lam^2 (1/2 + 2 lam/9).
  Per-row Bernoulli bound (from Real.exp_bound with n=3):
      1 - p + p e^lam <= exp(p lam + c(lam) p (1-p)).
  Variant A (one tail, s <= n):          K = lam d/2 - c(lam) E1
  Variant B (two tails, min(s,n-s)<=n/2): K = lam d/2 - c(lam) E1/2, and round 1 also two-tailed.
  Round-2 failure fraction <= (2(m+1))^n exp(-n m K) = exp(-n (m K - ln(2(m+1)))).
"""
from fractions import Fraction as Fr
import math
import mpmath
from mpmath import iv, mpf

iv.prec = 200
mpmath.mp.prec = 200

D = Fr(1, 59_000_000)
LN2_LO = Fr(6931471803, 10**10)
LN2_HI = Fr(6931471808, 10**10)
LN100_OVER16_HI = Fr(2879, 10000)   # ln(100)/16 = 0.287823...  (certified below)
LN1000_OVER16_HI = Fr(4318, 10000)  # ln(1000)/16 = 0.431734... (certified below)


def c_of(lam):
    return lam * lam * (Fr(1, 2) + Fr(2, 9) * lam)


def ln2m1_hi(k):
    """Rational upper bound for ln(2(M+1)) with M = 2^k: (k+1) ln2 + ln(1+2^-k) <= (k+1)LN2_HI + 2^-k."""
    return (k + 1) * LN2_HI + Fr(1, 2**k)


def check_constants():
    assert iv.log(100) / 16 < iv.mpf(LN100_OVER16_HI.numerator) / LN100_OVER16_HI.denominator
    assert iv.log(1000) / 16 < iv.mpf(LN1000_OVER16_HI.numerator) / LN1000_OVER16_HI.denominator
    l2 = iv.log(2)
    assert l2 > iv.mpf(LN2_LO.numerator) / LN2_LO.denominator
    assert l2 < iv.mpf(LN2_HI.numerator) / LN2_HI.denominator


# ---------------------------------------------------------------- rational certificates (M = 2^k)

def certify(k, E1, lam, variant, rounds_after=None, verbose=True):
    """Exact-rational certificate for all m >= M = 2^k, all n >= 16.

    Round 1 (existing Lean lemma for variant A): sqrt(2(1+ln m)/m) <= E1  <=>  E1^2 M >= 2(1+k ln2).
    Round 1 (variant B, new two-tailed Hoeffding):  E1^2 M - ln(2(M+1)) >= ln(100)/16, E1^2 (M+1) >= 1.
    Round 2:  M K - ln(2(M+1)) >= ln(1000)/16  and  K (M+1) >= 1 (monotonicity in m).
    rounds_after: optional list of (E_prev, E_next, lam) for extra scrambles (three-round analysis);
      by default a single second round (E1 -> D).
    """
    M = 2**k
    ok = True
    msgs = []
    if variant == "A":
        r1 = E1 * E1 * M - 2 * (1 + k * LN2_HI)
        ok &= r1 >= 0
        msgs.append(f"round1(A): E1^2 M - 2(1+k ln2_hi) = {float(r1):.6g} (need >= 0; fail <= (149/200)^16 < 1/100)")
    else:
        r1 = E1 * E1 * M - ln2m1_hi(k) - LN100_OVER16_HI
        ok &= r1 >= 0 and E1 * E1 * (M + 1) >= 1
        msgs.append(f"round1(B): E1^2 M - ln(2(M+1)) - ln(100)/16 >= {float(r1):.6g} (need >= 0)")
    stages = rounds_after if rounds_after is not None else [(E1, D, lam)]
    for (Ep, En, lm) in stages:
        assert 0 < lm <= 1
        cl = c_of(lm)
        K = lm * En / 2 - cl * Ep * (1 if variant == "A" else Fr(1, 2))
        marg = M * K - ln2m1_hi(k) - LN1000_OVER16_HI
        ok &= K > 0 and K * (M + 1) >= 1 and marg >= 0
        msgs.append(f"round({float(Ep):.4g}->{float(En):.4g}): mK - ln(2(m+1)) - ln(1000)/16 >= {float(marg):.6g}"
                    f"  [mK = {float(M*K):.6g}, ln(2(M+1)) <= {float(ln2m1_hi(k)):.6g}]")
    if verbose:
        print(f"  k={k} variant={variant}: {'CERTIFIED' if ok else 'FAILS'}")
        for s in msgs:
            print("    " + s)
    return ok


# ---------------------------------------------------------------- real-threshold search (mpmath)

def e1_A(m):
    return mpmath.sqrt(2 * (1 + mpmath.log(m)) / m)


def e1_B(m):
    return mpmath.sqrt((mpmath.log(2 * (m + 1)) + mpmath.log(100) / 16) / m)


def bestK(Ep, En, variant):
    """max over lam in (0,1] of lam En/2 - c(lam) Ep w, w = 1 (A) or 1/2 (B)."""
    w = 1 if variant == "A" else mpf(1) / 2
    f = lambda l: l * En / 2 - l * l * (mpf(1) / 2 + 2 * l / 9) * Ep * w
    l0 = En / (2 * Ep * w)
    l = mpmath.findroot(lambda l: En / 2 - (l + 2 * l * l / 3) * Ep * w, l0)
    l = min(l, mpf(1))
    return f(l), l


def margin2(m, variant):
    E1 = e1_A(m) if variant == "A" else e1_B(m)
    K, _ = bestK(E1, mpf(D.numerator) / D.denominator, variant)
    return m * K - mpmath.log(2 * (m + 1)) - mpmath.log(1000) / 16


def margin3(m, variant):
    """Three scrambles: maximise over intermediate E2 the min of the two round margins."""
    E1 = e1_A(m) if variant == "A" else e1_B(m)
    d = mpf(D.numerator) / D.denominator
    L = mpmath.log(2 * (m + 1)) + mpmath.log(1000) / 16

    def g(logE2):
        E2 = mpmath.exp(logE2)
        a = m * bestK(E1, E2, variant)[0] - L
        b = m * bestK(E2, d, variant)[0] - L
        return a, b
    lo, hi = mpmath.log(d), mpmath.log(E1)
    for _ in range(200):  # bisection on a - b (a increasing in E2, b decreasing)
        mid = (lo + hi) / 2
        a, b = g(mid)
        if a > b:
            hi = mid
        else:
            lo = mid
    a, b = g((lo + hi) / 2)
    return min(a, b), mpmath.exp((lo + hi) / 2)


def threshold(fn, lo_log2, hi_log2):
    lo, hi = mpf(lo_log2), mpf(hi_log2)
    for _ in range(80):
        mid = (lo + hi) / 2
        if fn(mpmath.power(2, mid)) >= 0:
            hi = mid
        else:
            lo = mid
    return hi


def l1_margin(m, variant):
    """Variant + l1-ball state count (not Lean-cheap): number of admissible c' <= m * 2^n * C(N+n, n),
    N = E1 m n; per-column log count <= ln 2 + ln(e (E1 m + 1)), plus ln(m)/16 amortised (n >= 16)."""
    E1 = e1_A(m) if variant == "A" else e1_B(m)
    K, _ = bestK(E1, mpf(D.numerator) / D.denominator, variant)
    perCol = mpmath.log(2) + mpmath.log(2) + 1 + mpmath.log(E1 * m + 1)  # 2^n subsets * 2^n signs * (e(N+n)/n)^n
    return m * K - perCol - mpmath.log(m) / 16 - mpmath.log(1000) / 16


def main():
    check_constants()
    print("Constants certified: ln2 in (0.6931471803, 0.6931471808), ln100/16 < 0.2879, ln1000/16 < 0.4318\n")

    print("== Lean-ready rational certificates (valid for ALL m >= 2^k, ALL n >= 16) ==")
    # Variant A at k = 42 (window 2^42 < m <= 2^43): E1 = 3.71e-6, lam = 1/437
    certify(42, Fr(371, 10**8), Fr(1, 437), "A")
    # Variant A fails at k = 41 for every choice (real threshold 2^41.658 below); show near-optimal try
    certify(41, Fr(518, 10**8), Fr(1, 611), "A")
    # Variant B at k = 41 (certified) and k = 40 (fails; real threshold 2^40.62)
    certify(41, Fr(366, 10**8), Fr(1, 216), "B")
    certify(40, Fr(512, 10**8), Fr(1, 302), "B")
    # Three scrambles, variant A at k = 37: E1 -> E2 -> D
    E1 = Fr(1971, 10**8)  # >= sqrt(2(1+37 ln2)/2^37) = 1.9696e-5
    E2 = Fr(177, 10**9)
    certify(37, E1, None, "A", rounds_after=[(E1, E2, Fr(1, 222)), (E2, D, Fr(1, 21))])
    print()

    print("== Real thresholds (200-bit bisection on the optimal-lam margin; locating only, not a certificate) ==")
    for v in "AB":
        t = threshold(lambda m: margin2(m, v), 36, 46)
        print(f"  two scrambles, variant {v}: margin >= 0 iff log2 m >= {mpmath.nstr(t, 8)}")
    for v in "AB":
        t = threshold(lambda m: margin3(m, v)[0], 30, 46)
        print(f"  three scrambles, variant {v}: log2 m >= {mpmath.nstr(t, 8)}")
    for v in "AB":
        t = threshold(lambda m: l1_margin(m, v), 30, 46)
        print(f"  two scrambles + l1-ball state count, variant {v}: log2 m >= {mpmath.nstr(t, 8)}")
    print()

    print("== Interval re-check of margins at specific m (optimal E1, lam; f2 <= 1/1000) ==")
    for k in [40, 41, 42, 43]:
        for v in "AB":
            m = 2**k + 1
            E1 = e1_A(m) if v == "A" else e1_B(m)
            K, lam = bestK(E1, mpf(D.numerator) / D.denominator, v)
            # interval recomputation at the float-chosen lam (rounded to a rational)
            lamF = Fr(mpmath.nstr(lam, 12))
            E1i = (iv.sqrt(2 * (1 + iv.log(m)) / m) if v == "A"
                   else iv.sqrt((iv.log(2 * (m + 1)) + iv.log(100) / 16) / m))
            w = 1 if v == "A" else iv.mpf(1) / 2
            li = iv.mpf(lamF.numerator) / lamF.denominator
            di = iv.mpf(1) / 59_000_000
            Ki = li * di / 2 - li * li * (iv.mpf(1) / 2 + 2 * li / 9) * E1i * w
            mg = m * Ki - iv.log(2 * (m + 1)) - iv.log(1000) / 16
            print(f"  m=2^{k}+1 variant {v}: E1={mpmath.nstr(E1,6)} lam={float(lamF):.4g} "
                  f"mK={mpmath.nstr(m*K,6)} margin in {iv.nstr(mg, 8)}")
    print()
    print("== Three scrambles: margins and optimal intermediate E2 ==")
    for k in [36, 37, 38, 39, 40]:
        for v in "AB":
            mg, E2 = margin3(mpf(2)**k + 1, v)
            print(f"  m=2^{k}+1 variant {v}: min margin {mpmath.nstr(mg,6)}, E2* = {mpmath.nstr(E2,6)}")


if __name__ == "__main__":
    main()
