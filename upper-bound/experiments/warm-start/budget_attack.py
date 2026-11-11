#!/usr/bin/env python3
"""Per-stage worst case inside an L1 budget (WARM-START.md section 8).

Take the stationary input L1 of chain_sim.py (about 0.45 F rows per column) as the invariant budget.
The adversary picks input deviations delta with sum |delta_j| <= n * ell, using Theorem R2's dual
climb (each column maximises X_j(h) - lam |h|, with lam tuned to spend the budget), aimed at an
aligned target S = union of next-stage groups C_j over a random set J. Measures the next-stage input
(group sums of middle deviations): its L1 per group, and the far-cell leak sum_j (|delta'_j| - X)_+
per group at X = 4F. Random-sign inputs with the same L1 are the baseline. Exact runs.

    python budget_attack.py N
"""
import sys
import numpy as np


def run(F, N, ell, rng):
    D = int(12 * ell) + 8                                   # rows considered on each side of base
    s1 = np.stack([rng.permutation(N) for _ in range(2 * D)])
    groups = rng.permutation(N).reshape(N // F, F)
    owner = np.empty(N, dtype=np.int64)
    owner[groups.ravel()] = np.repeat(np.arange(N // F), F)
    rows = np.arange(2 * D)[:, None]
    flat = s1.ravel()

    def nxt(h):                                             # h in window coords, base row D
        mid = np.bincount(flat[(rows < h[None, :]).ravel()], minlength=N).astype(float)
        mid -= mid.mean()
        g = np.bincount(owner, weights=mid, minlength=N // F)
        return g

    def stats(g):
        return float(np.abs(g).mean()), float(np.maximum(np.abs(g) - 4 * F, 0).mean())

    best = (0.0, 0.0, None)
    for q in (0.01, 0.03, 0.1, 0.3, 0.5):
        J = rng.random(N // F) < q
        S = J[owner]
        p = S.mean()
        inc = np.where(S, 1 - p, -p)[s1]                    # walk increments by row (window rows)
        up = np.cumsum(inc[D:], axis=0)                     # X(h) for h = 1..D
        dn = -np.cumsum(inc[:D][::-1], axis=0)              # X(-h) for h = 1..D
        H = np.arange(1, D + 1)[:, None]
        for lam in np.geomspace(0.002, 0.5, 40):
            a, b = up - lam * H, dn - lam * H
            ia, ib = a.argmax(0), b.argmax(0)
            va, vb = a.max(0), b.max(0)
            d = np.where((va >= vb) & (va > 0), ia + 1, np.where(vb > 0, -(ib + 1), 0))
            d = d - int(round(d.mean()))                    # exact mass (shift the base)
            if np.abs(d).mean() > ell:
                continue
            g = nxt(D + d)
            L1, leak = stats(g)
            if leak > best[1] or (leak == best[1] and L1 > best[0]):
                best = (L1, leak, (q, lam, float(np.abs(d).mean())))
            break                                           # largest-budget lam within budget
    # random baseline with the same L1: two-sided geometric-ish deviations
    d = np.rint(rng.laplace(0, ell, N)).astype(int)
    d = np.clip(d - int(round(d.mean())), -D, D - 1)
    return best, stats(nxt(D + d))


def main():
    N = int(sys.argv[1])
    print(f'N={N}; budget ell = 0.45 F (stationary input L1 of chain_sim)')
    for F in (4, 16, 64):
        rng = np.random.default_rng(F)
        (L1, leak, info), (rL1, rleak) = run(F, N, 0.45 * F, rng)
        print(f'F={F:3d}: attack next-input L1/group {L1:8.2f}, leak at 4F {leak:.3f}  (q, lam, used L1) {info}'
              f' | random: L1 {rL1:.2f}, leak {rleak:.4f}', flush=True)


if __name__ == '__main__':
    main()
