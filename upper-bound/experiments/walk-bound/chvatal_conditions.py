#!/usr/bin/env python3
"""Exact-rational check of Chvatal's (4.1)-(4.5) (DCS-TR-294 Lemmas 4.3-4.4) at a parameter point.

Transcribed from the paper (printed pp. 12-13) in the same scaled form as the Lean package
(upper-bound/best/AKS/Chvatal/StageKernel.lean `cond42_scaled`, `cond45_scaled`, KernelSetup.lean
`cond44_real`, RealInduction.lean `paperRootEpsB_le_epsStar`):

  (4.1)  eps_*  <=  mu / k                                                     (root separator)
  (4.2)  (mu + (k-1) mu sib + slack + eps_B) / (A nu) + mu delta A k / nu  <=  mu,
         sib = delta k A^2 / (1 - delta^2 k^2 A^2),  slack = (A nu k - 2 A nu + 1) / (2 A^2 k^2)
  (4.3)  mu  <=  nu / (A k^2)
  (4.4)  mu  <=  (1/2) delta_F (A nu k - 1) / (A^2 k^2)
  (4.5)  eps_F / (A nu) + delta^2 A k / nu  <=  delta
  side:  A nu > 1,  delta k A < 1.

`python -I chvatal_conditions.py` checks the 1419 package's point (must reproduce the Lean facts) and
the re-priced V0 point (k, A, nu) = (64, 2^11, 2^-5), eps_B = 2^-25, J = 1/eps_F = 11 500 000,
and prints the feasible delta window there.
"""
import sys
from fractions import Fraction as Fr


def conditions(k, A, nu, dF, mu, delta, epsB, epsF, epsStar=None):
    sib = delta * k * A ** 2 / (1 - delta ** 2 * k ** 2 * A ** 2)
    slack = (A * nu * k - 2 * A * nu + 1) / (2 * A ** 2 * k ** 2)
    rows = []
    if epsStar is not None:
        rows.append(("(4.1) eps_* <= mu/k", epsStar, mu / k))
    rows += [
        ("(4.2)", (mu + (k - 1) * mu * sib + slack + epsB) / (A * nu) + mu * delta * A * k / nu, mu),
        ("(4.3) mu <= nu/(A k^2)", mu, nu / (A * k ** 2)),
        ("(4.4) mu <= dF (A nu k - 1)/(2 A^2 k^2)", mu, dF * (A * nu * k - 1) / (2 * A ** 2 * k ** 2)),
        ("(4.5)", epsF / (A * nu) + delta ** 2 * A * k / nu, delta),
        ("A nu > 1", Fr(1), A * nu),
        ("delta k A < 1", delta * k * A, Fr(1)),
    ]
    return [(name, lhs, rhs, lhs <= rhs if "(4." in name else lhs < rhs) for name, lhs, rhs in rows]


def report(title, rows):
    print(title)
    ok = True
    for name, lhs, rhs, good in rows:
        ok &= good
        print(f"  {'OK  ' if good else 'FAIL'} {name:42s} lhs/rhs = {float(lhs / rhs):.6f}")
    return ok


def delta_window(k, A, nu, dF, mu, epsB, epsF, N=4000):
    """Feasible delta for (4.2) and (4.5), each candidate checked exactly, on an arithmetic grid of
    step 0.1% of eps_F/(A nu) (so "no feasible delta" is a grid result, not a proof)."""
    lo, hi = None, None
    d0 = epsF / (A * nu)
    for i in range(N):
        d = d0 * Fr(1000 + i, 1000)
        rows = conditions(k, A, nu, dF, mu, d, epsB, epsF)
        good = all(r[3] for r in rows)
        if good and lo is None:
            lo = d
        if good:
            hi = d
        if lo is not None and not good:
            break
    return lo, hi


def main():
    ok = True
    # 1419 package (StageKernel.lean): mu = (1 - 2^-10) 2^-30, delta = 1/5.3e9, eps_B = 1/59e6, eps_F = 1/86e6
    pk = dict(k=Fr(64), A=Fr(4096), nu=Fr(1, 64), dF=Fr(128, 4095), mu=Fr(1023, 2 ** 40),
              delta=Fr(1, 5_300_000_000), epsB=Fr(1, 59_000_000), epsF=Fr(1, 86_000_000), epsStar=Fr(1023, 2 ** 40) / 64)   # Lean: paperRootEpsB <= invMu/64
    ok &= report("1419 package (64, 2^12, 2^-6):", conditions(**pk))

    # re-priced V0: (64, 2^11, 2^-5), mu = (1 - 2^-10) 2^-28 (the (4.3)/(4.4) cap, as in the package)
    k, A, nu, dF = Fr(64), Fr(2 ** 11), Fr(1, 32), Fr(128, 4095)
    mu = (1 - Fr(1, 2 ** 10)) * Fr(1, 2 ** 28)
    epsB, epsF = Fr(1, 2 ** 25), Fr(1, 11_500_000)
    lo, hi = delta_window(k, A, nu, dF, mu, epsB, epsF)
    print(f"\nre-priced V0 (64, 2^11, 2^-5), eps_B = 2^-25, eps_F = 1/11500000, mu = (1-2^-10) 2^-28:")
    if lo is None:
        print("  no feasible delta")
        ok = False
    else:
        print(f"  feasible delta (grid) in [{float(lo):.6e}, {float(hi):.6e}]")
        delta = Fr(138, 10 ** 11)
        print(f"  chosen delta = 1.38e-9 = {float(delta):.6e}")
        # (4.1): the package's root separator (m = 2^79, one round, Lemma 6.1) gives
        # sqrt(2(1 + 79 ln 2)/2^79) = 1.3583e-11 <= 1.36e-11 (float; Lean: paperRootEpsB_le_epsStar)
        ok &= report("  conditions at the chosen delta:", conditions(k, A, nu, dF, mu, delta, epsB, epsF, epsStar=Fr(136, 10 ** 13)))
        print(f"  root separator needs eps_* <= mu/k = {float(mu / k):.4e}; m = 2^79 one-round gives 1.3583e-11")
    print("\nALL CONDITIONS HOLD" if ok else "\nSOME CONDITION FAILS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
