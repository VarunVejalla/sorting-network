#!/usr/bin/env python3
"""Exact check of the centred (4.2'') at (k, A, nu) = (16, 32, 1/8), q = 25 (CENTRED-SHIFT.md).

One-sided centred design (no new invariant): end-only deficits, interior theta = 0, a centred design
offset at every boundary. Per-child intruders <= (mu c + G)/2 + (k-1) Delta_1 / 2 + mu delta A^2 k c
+ eps_B a + gamma, with G <= g* c the sender's deficit.

  (4.2'')  mu/2 + (k-1) mu sib/2 + mu delta A^2 k + g*/2 + ROUND + eps_B eta  <=  mu A nu
  g*:      the end child of a mid/botDesc parent gets theta = pi/2 + G - o with |o| <= (mu c + G)/2, so
           g' <= (p/2 + g + (mu + g)/2)/(A nu), fixed point g* = (p + mu)/(2 A nu - 3); topRise end
           child: 1/(2 A^2 k) (smaller).
  eta:     a/c <= max(4160 p + 2^6 g*, 1) (R1-PROOF.md (I3) with theta <= g* c(i, t-2) = 64 g* c).
  (4.3), (4.4), (4.5) as in r1_point.py; delta is scanned; J = 1/eps_F from (4.5).
Bulk: eps_B = 1/70000 (R1Cells25 / R2Cells25, rows in [27254890, 2^25]).
"""
from fractions import Fraction as Fr

k, A, nu = 16, 32, Fr(1, 8)
dF = Fr(1, 8)
Anu = A * nu
p = (Anu * k - 1) / Fr(A * A * k * k)
mu43 = nu / (A * k * k)
mu44 = dF * (Anu * k - 1) / (2 * A * A * k * k)
mu = (1 - Fr(1, 1024)) * min(mu43, mu44)
ROUND = Fr(1, 10) * mu
eps_B = Fr(1, 70000)
gstar = (p + mu) / (2 * Anu - 3)
g_top = Fr(1, 2 * A * A * k)
eta = max(4160 * p + 64 * gstar, Fr(1))


def check(delta):
    sib = delta * k * A * A / (1 - delta ** 2 * k ** 2 * A ** 2)
    lhs = mu / 2 + (k - 1) * mu * sib / 2 + mu * delta * A * A * k + max(gstar, g_top) / 2 + ROUND + eps_B * eta
    rhs = mu * Anu
    eps_F = Anu * delta - A * A * k * delta ** 2
    return lhs, rhs, eps_F, sib


def main():
    print(f"mu = {float(mu):.6e}, p = {float(p):.6e}, g* = {float(gstar):.4e} (design P g* = {float(g_top):.4e}), "
          f"eta = {float(eta):.6f}, eps_B = 1/70000")
    best = None
    for num in range(5, 400, 5):
        delta = Fr(num, 10 ** 7)
        if delta * k * A >= 1:
            break
        lhs, rhs, eps_F, sib = check(delta)
        if eps_F <= 0:
            continue
        J = 1 / eps_F
        ok = lhs <= rhs
        if ok and (best is None or J < best[1]):
            best = (delta, J, lhs / rhs, sib)
        if num % 20 == 0:
            print(f"  delta = {float(delta):.2e}: (4.2'') lhs/rhs = {float(lhs / rhs):.4f} {'OK' if ok else 'FAIL'}, "
                  f"J = 1/eps_F = {float(J):.0f}")
    if best:
        d, J, ratio, sib = best
        print(f"\nsmallest J with (4.2'') OK: delta = {float(d):.3e}, J = {float(J):.0f}, lhs/rhs = {float(ratio):.4f}; "
              f"fringe needs f(J) <= 4023 (class A, f ~ 18 sqrt J ~ {18 * float(J) ** 0.5:.0f})")
    else:
        print("\n(4.2'') fails for every delta")
    print(f"(4.3) mu/bound = {float(mu / mu43):.4f}, (4.4) mu/bound = {float(mu / mu44):.4f}")


if __name__ == "__main__":
    main()
