#!/usr/bin/env python3
"""Multi-stage reachability (WARM-START.md section 9): can a stage-0 input re-create alignment at stage 2?

Geometry shrinks by F per stage as in the real layout (no column reuse): n0 = F^2 n2, n1 = F n2.
Stage t: sorted columns with deviations delta^t (around a base row), row scramble sigma_t (exact on
the rows where columns differ), middle deviations, then stage t+1 input = group sums over fixed
groups of F middle columns.

  target  : delta1* = Theorem-R2 dual climb at stage 1 aimed at S2 = union of stage-2 groups over J2,
            within the stationary budget ell1 = 0.45 F per column. Its stage-2 effect is the
            per-stage worst case (reference, section 8).
  lookahead: stage-0 dual climb whose deposit prices are delta1* of the receiving stage-1 group,
            within budget ell0 = 0.45 F; run forward and measure stage 2.
  one-stage: stage-0 climb aimed at stage-1 groups (random J1); measured at stage 2.
  random  : random stage-0 input with the same L1.
Measured: stage-2 input L1 per column, and its far-cell leak sum (|delta2| - 4F)_+ per column.
Exact runs (lower bounds for the sampled scrambles).

    python lookahead_attack.py F n2
"""
import sys
import numpy as np


def middle(delta, rng):
    """Middle deviations after one row scramble of columns with heights base + delta (integers)."""
    n = len(delta)
    d = np.asarray(delta, dtype=np.int64)
    lo, hi = int(d.min()), int(d.max())
    mid = np.zeros(n)
    for r in range(lo, hi):
        ones = np.nonzero(d > r)[0]
        mid[rng.permutation(n)[ones]] += 1
    return mid - mid.mean()


def climb(price_of_dest, s_rows, D, ell):
    """Theorem-R2 dual climb: prices on destination columns, rows s_rows (2D x n), base row D.
    Returns integer deviations with mean |delta| <= ell (largest budget found), exact mass."""
    inc = price_of_dest[s_rows] - price_of_dest.mean()
    up = np.cumsum(inc[D:], axis=0)
    dn = -np.cumsum(inc[:D][::-1], axis=0)
    H = np.arange(1, D + 1)[:, None]
    scale = np.abs(inc).mean() + 1e-12
    for lam in scale * np.geomspace(0.002, 2, 60):
        a, b = up - lam * H, dn - lam * H
        va, vb = a.max(0), b.max(0)
        d = np.where((va >= vb) & (va > 0), a.argmax(0) + 1, np.where(vb > 0, -(b.argmax(0) + 1), 0))
        d = d - int(round(d.mean()))
        if np.abs(d).mean() <= ell:
            return d
    return np.zeros(s_rows.shape[1], dtype=np.int64)


def gsum(x, owner, ng):
    return np.bincount(owner, weights=x, minlength=ng)


def stage_from(d, s_rows, D):
    """Middle deviations for deviations d using fixed window rows s_rows (base row D)."""
    rows = np.arange(2 * D)[:, None]
    h = D + d
    mid = np.bincount(s_rows.ravel()[(rows < h[None, :]).ravel()], minlength=s_rows.shape[1]).astype(float)
    return mid - mid.mean()


def report(tag, d2, F):
    print(f'  {tag:11s} stage-2 input L1/col {np.abs(d2).mean():8.2f}   leak at 4F {np.maximum(np.abs(d2) - 4 * F, 0).mean():8.3f}'
          f'   max {np.abs(d2).max():7.1f}', flush=True)


def main():
    F, n2 = int(sys.argv[1]), int(sys.argv[2])
    n1, n0 = F * n2, F * F * n2
    rng = np.random.default_rng(F)
    ell = 0.45 * F
    D0 = int(12 * ell) + 8
    s0 = np.stack([rng.permutation(n0).astype(np.int32) for _ in range(2 * D0)])
    own1 = np.empty(n0, dtype=np.int64); own1[rng.permutation(n0)] = np.repeat(np.arange(n1), F)
    own2 = np.empty(n1, dtype=np.int64); own2[rng.permutation(n1)] = np.repeat(np.arange(n2), F)
    D1 = 40 * F + 50
    s1 = np.stack([rng.permutation(n1).astype(np.int32) for _ in range(2 * D1)])
    print(f'F={F}: n0={n0} n1={n1} n2={n2}, budget ell = {ell:.2f} rows/column', flush=True)

    def forward(d0):
        d1 = np.rint(gsum(stage_from(d0, s0, D0), own1, n1)).astype(np.int64)
        d1 = np.clip(d1 - int(round(d1.mean())), -D1, D1 - 1)
        d2 = gsum(stage_from(d1, s1, D1), own2, n2)
        return d1, d2

    # per-stage worst case at stage 1 (reference) and its target delta1*
    best_ref, d1star = None, None
    for q in (0.1, 0.3, 0.5):
        J2 = rng.random(n2) < q
        price1 = np.where(J2[own2], 1.0, 0.0)
        d1 = climb(price1, s1, D1, ell)
        d2 = gsum(stage_from(d1, s1, D1), own2, n2)
        v = (float(np.maximum(np.abs(d2) - 4 * F, 0).mean()), float(np.abs(d2).mean()))
        if best_ref is None or v > best_ref[0]:
            best_ref, d1star = (v, d2), d1
    report('per-stage', best_ref[1], F)

    # lookahead: stage-0 deposit prices = delta1* of the receiving stage-1 group
    best = None
    for gain in (1.0,):
        d0 = climb(d1star[own1].astype(float), s0, D0, ell)
        d1, d2 = forward(d0)
        corr = np.corrcoef(d1, d1star)[0, 1]
        best = (d2, corr, np.abs(d1).mean())
    report('lookahead', best[0], F)
    print(f'  {"":11s} (stage-1 input L1/col {best[2]:.2f}, corr with delta1* {best[1]:.3f})', flush=True)

    # one-stage attack aimed at stage 1, measured at stage 2
    J1 = rng.random(n1) < 0.5
    d0 = climb(np.where(J1[own1], 1.0, 0.0), s0, D0, ell)
    d1, d2 = forward(d0)
    report('one-stage', d2, F)
    print(f'  {"":11s} (stage-1 input L1/col {np.abs(d1).mean():.2f}, stage-1 leak at 4F {np.maximum(np.abs(d1) - 4 * F, 0).mean():.3f})', flush=True)

    # random input with the same L1
    d0 = np.rint(rng.laplace(0, ell, n0)).astype(np.int64)
    d0 = np.clip(d0 - int(round(d0.mean())), -D0, D0 - 1)
    d1, d2 = forward(d0)
    report('random', d2, F)


if __name__ == '__main__':
    main()
