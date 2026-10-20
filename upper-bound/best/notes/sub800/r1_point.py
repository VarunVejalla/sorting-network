#!/usr/bin/env python3
"""Exact check of Chvatal's (4.1)-(4.5) at the sub-800 R1 point (README.md), in the slack-free form of
SLACKFREE.md sec. 4 (route R1: same invariant P, optimal one-sided table 'design P'):

  (4.2)  mu + (k-1) mu sib + mu delta A^2 k + res + eps_B eta  <=  mu A nu,
         res = r* = (k-1)/(2 A^2 k^2) (+ an explicit rounding reserve),  eta = max a/c bound,
  (4.3)  mu <= nu/(A k^2),   (4.4)  mu <= (1/2) delta_F (A nu k - 1)/(A^2 k^2),
  (4.5)  eps_F/(A nu) + delta^2 A k/nu <= delta,   delta k A < 1,   (4.1) eps_* <= mu/k.

Point: (k, A, nu) = (16, 32, 1/8), delta_F = 1/8, mu = (1 - 2^-10) min((4.3), (4.4)).
Also prints the bulk requirement (walk bound, float) and the fringe parameters for the certificate.

Run:  python -I r1_point.py
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "experiments", "walk-bound"))

k, A, nu = 16, 32, Fr(1, 8)
dF = Fr(1, 8)
Anu = A * nu
mu43 = nu / (A * k * k)
mu44 = dF * (Anu * k - 1) / (2 * A * A * k * k)
mu = (1 - Fr(1, 1024)) * min(mu43, mu44)
rstar = Fr(k - 1, 2 * A * A * k * k)
eta = 1 + Fr(k - 1, 2 * A * A * k * k) / nu ** 2         # SLACKFREE sec. 4 (R1); simulated a/c <= 1.00168
ROUND = Fr(1, 10) * mu                                  # reserve for integer rounding of the table (to be justified)
delta = Fr(135, 10 ** 8)
eps_B = Fr(1, 105_000)
M = 2 ** 26 - 2 ** 20                                   # rows; M + padding < 2^26


def main():
    ok = True
    sib = delta * k * A * A / (1 - delta ** 2 * k ** 2 * A ** 2)
    lhs42 = mu + (k - 1) * mu * sib + mu * delta * A * A * k + rstar + ROUND + eps_B * eta
    rhs42 = mu * Anu
    eps_F = Anu * delta - A * A * k * delta ** 2            # largest eps_F allowed by (4.5)
    J = math.ceil(1 / eps_F)
    eps_F = Fr(1, J)
    rows = [
        ("(4.2) incl. rounding reserve 0.1 mu", lhs42, rhs42),
        ("(4.3) mu <= nu/(A k^2)", mu, mu43),
        ("(4.4) mu <= dF (A nu k - 1)/(2 A^2 k^2)", mu, mu44),
        ("(4.5) eps_F/(A nu) + delta^2 A k/nu <= delta", eps_F / Anu + delta ** 2 * A * k / nu, delta),
        ("delta k A < 1", delta * k * A, Fr(1)),
    ]
    print(f"(k, A, nu) = ({k}, {A}, {nu}), delta_F = {dF}, mu = {float(mu):.6e}, r*/mu = {float(rstar / mu):.4f}, "
          f"eta = {float(eta):.6f}")
    print(f"delta = {float(delta):.4e}, eps_B = 1/105000 = {float(eps_B):.4e}, J = 1/eps_F = {J}")
    for name, l, r in rows:
        good = l <= r if name.startswith("(4.") else l < r
        ok &= good
        print(f"  {'OK  ' if good else 'FAIL'} {name:46s} lhs/rhs = {float(l / r):.6f}")
    print(f"  (4.2) budget split (units of mu): sibling {float((k - 1) * sib):.3f}, delta term "
          f"{float(delta * A * A * k):.4f}, r* {float(rstar / mu):.3f}, rounding 0.1, eps_B {float(eps_B * eta / mu):.3f}, "
          f"base 1, budget {float(Anu):.0f}")
    print(f"  (4.1) root separator needs eps_* <= mu/k = {float(mu / k):.3e} (additive constant)")

    import na_precision as NP
    for m_ in (50859009, 52703924, M, 2 ** 26):           # admitted window [2^25.6, 2^26] and the observed low end
        L = math.log2(m_)
        d = NP.d_na(L, NP.e1_na(L, uniform=True), uniform=True)[0]
        print(f"  bulk: lg m = {L:.4f}: d = {d:.4e} vs eps_B {float(eps_B):.4e} (margin {float(eps_B) / d:.3f}x)")
        ok &= d <= float(eps_B)
    pi_c = (Anu * k - 1) / Fr(A * A * k * k)
    print(f"  fringe classes f = 7934 and 406109 (padded (f+1)-row form, R1-PROOF.md sec. 4); "
          f"certificates run at J = 190000 >= {J}"
          f" {'(OK: larger J is conservative)' if 190000 >= J else '(J TOO SMALL)'}")
    ok &= 190000 >= J
    S = lambda q: q * (q + 1) // 2
    node = 3 * S(26)
    cut = max(c for c in range(1, 100) if S(c) <= node)
    print(f"  depth: rows < 2^26, node 3 S(26) = {node}, exact Batcher for a <= 2^{cut}; stages per bit "
          f"(x+y)/(x z) = 9/12; coefficient {float(Fr(node) * Fr(9, 12))}")
    print("\nALL CONDITIONS HOLD" if ok else "\nSOME CONDITION FAILS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
