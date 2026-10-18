#!/usr/bin/env python3
"""Scale of the walk-maximum bound B(sigma) = max_S sum_j max_h W_j^S(h) at moderate (m, n).

Simulation (local search over S, so a lower estimate of B for each sigma), compared with the
theorem's constant (WALK-BOUND.md):
    E F(S) <= 1.2533 n sqrt(m p(1-p)),  concentration + union over S <= n sqrt(2 m p' H(p)),
    so  B <= ~1.46 n sqrt(m)  at p = 1/2.
Also tabulates the implied one-round precision E1_new = 2 * 1.46/sqrt(m) against Lemma 6.1's
E1_old = sqrt(2 (1 + ln m)/m).

Run:  python -I scale_walk_bound.py
"""
import math

import numpy as np


def F_of(sig, inS):
    s = inS.sum()
    n = sig.shape[1]
    inc = inS[sig].astype(float) - s / n
    W = np.vstack([np.zeros(n), np.cumsum(inc, axis=0)])
    return float(W.max(axis=0).sum())


def local_search_B(sig, rng, restarts=6, sweeps=6):
    n = sig.shape[1]
    best = 0.0
    for _ in range(restarts):
        inS = rng.random(n) < 0.5
        cur = F_of(sig, inS)
        for _ in range(sweeps):
            improved = False
            for j in rng.permutation(n):
                inS[j] = ~inS[j]
                v = F_of(sig, inS)
                if v > cur:
                    cur, improved = v, True
                else:
                    inS[j] = ~inS[j]
            if not improved:
                break
        best = max(best, cur)
    return best


def H(p):
    return -p * math.log(p) - (1 - p) * math.log(1 - p)


def theorem_const():
    best = 0.0
    for p in np.linspace(0.01, 0.99, 197):
        pp = min(p, 1 - p)
        best = max(best, 1.2533 * math.sqrt(p * (1 - p)) + math.sqrt(2 * pp * H(p)))
    return best


def main():
    rng = np.random.default_rng(2029)
    K = theorem_const()
    print(f"theorem constant: B <= {K:.3f} n sqrt(m) (+ lower order)")
    print("   m    n   B(local search)   B/(n sqrt m)")
    for m, n in ((64, 32), (256, 32), (256, 64), (1024, 64)):
        vals = []
        for _ in range(3):
            sig = np.array([rng.permutation(n) for _ in range(m)])
            vals.append(local_search_B(sig, rng))
        b = max(vals)
        print(f" {m:4d} {n:4d}   {b:10.1f}        {b / (n * math.sqrt(m)):.3f}", flush=True)
    print("\none-round precision, as Property B's E1 (excess < (E1/2) m n):")
    print("  lg m   E1_old = sqrt(2(1+ln m)/m)   E1_new = 2K/sqrt(m)   ratio")
    for L in (16, 20, 25, 30, 35, 42):
        m = 2.0 ** L
        old = math.sqrt(2 * (1 + math.log(m)) / m)
        new = 2 * K / math.sqrt(m)
        print(f"  {L:4d}   {old:.3e}                  {new:.3e}          {old / new:.2f}")


if __name__ == "__main__":
    main()
