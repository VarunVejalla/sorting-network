#!/usr/bin/env python3
"""Re-price the conditional tapered 945 candidate with the walk-bound bulk (UB-30).

Keeps every invariant constant of the tapered candidate (../tapered/SUB1000-CANDIDATE.md,
../tapered/sub1000_screen.py, with the recovery plan's mu' = (63/64) mu): (k, A, nu) = (64, 64, 1/16),
delta = 2^-25, eps_B = 2^-21, delta_F = 128/4095.  Only the large ordinary provider changes: its row
height M drops from 2^34 + 2^28 to M below, and its fringe f scales with M.

Checks (exact rationals unless noted):
  1. the invariant's scalar budget with mu' (unchanged by this re-price; reproduces the plan's margin);
  2. the half-port fit (f+1) n <= up/2 and cohort support mu' C <= floor(delta_F f n) at the new M,
     with the recovery plan's charges (debt, rounding, floor loss); first reproduced at the old M;
  3. the bulk: walk-bound d (ROUND2.md, n-uniform, floating point) <= eps_B at lg M;
  4. depth: node depth 3 S(q) with M + 1024 < 2^q, exact small-bag cutoff S(c) <= 3 S(q).
The fringe certificate is run separately (fringe_cert_f28200.out).

Run:  python -I tapered_walk_screen.py
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "walk-bound"))

K, A, nu = 64, 64, Fr(1, 16)
Q = A ** 2 * K ** 2                         # 2^24
mu = Fr(17, 71_565_312)
mu_p = Fr(63, 64) * mu                      # recovery plan: room for half-port fit and support
delta = Fr(1, 2 ** 25)
eps_b = Fr(1, 2 ** 21)
dF = Fr(128, 4095)
s_up = (A * nu * K - 1) / Q                 # up-flow fraction 255/2^24
q_end, q_mid = -Fr(31, 2 ** 22), Fr(1, 2 ** 22)
contraction = Fr(1, A * K)
E_abs = abs(q_end) / A / (1 - contraction)  # |e|/C bound of the signed debt
E_pos = q_mid / A / (1 - contraction)
ETA = 69                                    # integer occupancy error (SignedReserve.lean)


def S(q):
    return q * (q + 1) // 2


def show(name, v):
    print(f"  {name:58s} {float(v):.6g}")


def scalar_budget(m_, d_, eb, round_C):
    """sub1000_screen.py's balanced-flow margin, with mu -> m_ and rounding charged at capacity round_C."""
    sib = d_ * K * A ** 2 / (1 - (d_ * K * A) ** 2)
    weighted = m_ * (A * nu - 1) - eb - m_ * (K * sib + d_ * A ** 2 * K)
    reserve = max(Fr(1, Q) + E_pos / K, Fr(1, 2 * Q) + Fr(31, 64) * E_abs)
    return weighted - reserve - Fr(ETA, round_C)


def provider_margins(M, f, C, pad=True):
    """Normalized (by C) margins of the half-port fit and cohort support for a bag of reference
    capacity C at ordinary occupancy a = (1 - 1/Q) C + eta, |eta| <= 69, n = floor(a/M) columns.
    Half-port: up = s C - e rounded to an even integer (one wire), e <= E_pos C; need (f+1) n <= up/2.
    Support:   need mu' C <= floor(dF f n); use floor(x) > x - 1 and n > a/M - 1.
    Padding:   the rectangle has m n - a < n <= a/M dummy wires; charged once against each margin
    (pad=True), as n/C <= a_hi/(M C).  Aligned-cut errors are not charged (open, recovery plan sec. 2)."""
    a_hi = (1 - Fr(1, Q)) * C + ETA
    a_lo = (1 - Fr(1, Q)) * C - ETA
    half_up = ((s_up - E_pos) * C - 1) / 2
    half = (half_up - (f + 1) * a_hi / M) / C
    support = (dF * f * (a_lo / M - 1) - 1 - mu_p * C) / C
    if pad:
        half -= a_hi / M / C
        support -= a_hi / M / C
    return half, support


def main():
    ok = True
    print("1. invariant scalar budget (unchanged constants)")
    b_mu = scalar_budget(mu, delta, eps_b, 2 ** 34)
    b_mup = scalar_budget(mu_p, delta, eps_b, 2 ** 34)
    show("margin, mu, rounding at 2^34 (SUB1000: 2.54003e-8)", b_mu)
    show("margin, mu' = 63/64 mu, rounding at 2^34 (plan: ~1.6150e-8)", b_mup)
    ok &= b_mu > 0 and b_mup > 0

    print("\n2. large ordinary provider: half-port fit and cohort support (normalized by C)")
    M_old, f_old = 2 ** 34 + 2 ** 28, 131040
    h, sp = provider_margins(M_old, f_old, 2 ** 59, pad=False)
    show("old M = 2^34+2^28, f = 131040, C = 2^59: half-port (plan 8.7487e-8)", h)
    show("                                         support   (plan 9.1697e-10)", sp)
    h, sp = provider_margins(M_old, f_old, 2 ** 59)
    show("  same, with the padding charge 1/M: half-port", h)
    show("                                     support", sp)
    M = 2 ** 31 + 2 ** 30 + 2 ** 29             # lg M = 31.807
    f = 28200
    lo_f = math.ceil(mu_p * M / dF)
    hi_f = math.floor((s_up - E_pos) * M / 2 - 1)
    print(f"  new M = 2^31+2^30+2^29 = {M} (lg {math.log2(M):.4f}); f window ~ [{lo_f}, {hi_f}], f = {f}")
    pad_max = M * M // (2 ** 55 - M) + 1           # m - M <= M/n + 1 with n >= 2^55/M - 1
    assert pad_max <= 1024
    print(f"  padding: m = ceil(a/n) <= M + {pad_max} <= M + 1024 for a > 2^55;  margins below include it")
    for C in (2 ** 55, 2 ** 59, 2 ** 80):
        h, sp = provider_margins(M, f, C)
        show(f"C = 2^{int(math.log2(C))}: half-port", h)
        show(f"         support", sp)
        ok &= h > 0 and sp > 0

    print("\n3. bulk (walk bound, ROUND2.md; n-uniform for n >= 16; float)")
    import na_precision as NP
    L = math.log2(M)
    e1 = NP.e1_na(L, uniform=True)
    d, gm = NP.d_na(L, e1, uniform=True)
    print(f"  lg M = {L:.4f}: E1 = {e1:.4e}, d = {d:.4e} vs eps_B = 2^-21 = {float(eps_b):.4e} "
          f"(margin {float(eps_b) / d:.3f}x, grid gamma {gm})")
    L2 = math.log2(M + 1024)
    d2 = NP.d_na(L2, NP.e1_na(L2, uniform=True), uniform=True)[0]
    print(f"  at M + 1024: d = {d2:.4e} (evaluated at both ends; monotonicity in m observed, not proved;"
          f" p on a 1/64 grid, float constants).  BULK2 needed lg m = 34")
    ok &= d2 <= float(eps_b)
    ok &= d <= float(eps_b)

    print("\n4. depth")
    q = 32
    assert M + 1024 < 2 ** q
    node = 3 * S(q)
    cut = max(c for c in range(1, 100) if S(c) <= node)
    n_min = 2 ** cut // M
    print(f"  rows < 2^{q}: node depth 3 S({q}) = {node}; exact Batcher for bags a <= 2^{cut} "
          f"(S({cut}) = {S(cut)}); large bags have n >= {n_min} columns (>= 16)")
    print(f"  three nodes per six bits: conditional coefficient {Fr(3 * node, 6)}  (was 945 at S(35))")
    print(f"  eps_F = A nu delta - A^2 k delta^2 = {A * nu * delta - A ** 2 * K * delta ** 2} -> "
          f"J = {math.ceil(1 / (A * nu * delta - A ** 2 * K * delta ** 2))}")

    print("\n5. gate for rows < 2^31 (3 S(31) = 1488, coefficient 744): what the fringe would need")
    M31 = 2 ** 31 - 2 ** 12
    L31 = math.log2(M31)
    d31 = NP.d_na(L31, NP.e1_na(L31, uniform=True), uniform=True)[0]
    eb31 = Fr(d31).limit_denominator(10 ** 15) * Fr(1001, 1000)
    lo_d, hi_d = Fr(0), Fr(1, 2 ** 20)
    if scalar_budget(mu_p, Fr(1, 10 ** 30), eb31, 2 ** 34) <= 0:
        print(f"  lg M = {L31:.4f}: bulk d = {d31:.4e} exceeds the whole budget")
    else:
        for _ in range(60):                     # largest delta keeping the budget >= 0 with eps_B = d
            mid = (lo_d + hi_d) / 2
            if scalar_budget(mu_p, mid, eb31, 2 ** 34) >= 0:      # 69 wires at the alpha frontier >= 2^34
                lo_d = mid
            else:
                hi_d = mid
        epsF = A * nu * lo_d - A ** 2 * K * lo_d ** 2
        f31 = math.floor((s_up - E_pos) * M31 / 2 - 1)
        print(f"  lg M = {L31:.4f}: bulk d = {d31:.4e} (eps_B = d), largest delta = {float(lo_d):.4e} "
              f"(was 2^-25 = {2 ** -25:.4e})")
        print(f"  -> J = 1/eps_F = {float(1 / epsF):.4e}; the fringe would have to certify at f <= {f31}")
    print("\nALL SCREENS PASS" if ok else "\nSOME SCREEN FAILS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
