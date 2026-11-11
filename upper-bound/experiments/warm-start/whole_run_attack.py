#!/usr/bin/env python3
"""Whole-run (amortized) test (WARM-START.md section 10): can ONE stage-0 input make every later
stage leak at its per-stage worst rate at once?

Geometry shrinks by F per stage as in lookahead_attack.py (no column reuse): n_t = F^(T-t) n_T.
Stage t: sorted columns with deviations d_t, row scramble sigma_t (exact on the window rows),
middle deviations, then d_{t+1} = sums over fixed groups of F middle columns. Strays are carried
(no clipping), as in chain_sim.py. Leak at stage t = mean_u (|d_t(u)| - 4F)_+ rows per column.

  per-stage L_t : fresh budget ell = 0.45F at stage t-1, dual climb aimed at a union of stage-t
                  groups (best of q in 0.01..0.5). The sum of L_t is the per-stage-proof charge.
  aim-k         : stage-0 input steered at stage k by recursive targets (target at stage k-1 is the
                  aligned climb; each earlier target prices deposits by the next target).
  mixed         : stage-0 prices = weighted sum of the normalised aim-k prices, coarse grid search
                  maximising the total leak.
Exact runs, lower bounds for the sampled scrambles and wiring.

    python whole_run_attack.py F nT T
"""
import itertools
import sys
import numpy as np
from lookahead_attack import climb, gsum, stage_from


def main():
    F, nT, T = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(1000 + F)
    ell = 0.45 * F
    X = 4 * F
    n = [F ** (T - t) * nT for t in range(T + 1)]
    D = [int(12 * ell) + 8] + [40 * F + 50] * T
    S = [np.stack([rng.permutation(n[t]).astype(np.int32) for _ in range(2 * D[t])]) for t in range(T)]
    own = [None]
    for t in range(1, T + 1):                      # own[t]: stage-(t-1) middle column -> stage-t column
        o = np.empty(n[t - 1], dtype=np.int64)
        o[rng.permutation(n[t - 1])] = np.repeat(np.arange(n[t]), F)
        own.append(o)
    print(f'F={F} T={T}: n={n}, budget ell={ell:.2f}, band X=4F={X}', flush=True)

    def step(t, d):
        """stage-t input d -> stage-(t+1) input."""
        d = np.clip(np.rint(d).astype(np.int64), -D[t], D[t] - 1)
        d = d - int(round(d.mean()))
        return gsum(stage_from(d, S[t], D[t]), own[t + 1], n[t + 1])

    def leak(d):
        return float(np.maximum(np.abs(d) - X, 0).mean())

    def run(d0):
        ds, out = d0, []
        for t in range(T):
            ds = step(t, ds)
            out.append((leak(ds), float(np.abs(ds).mean())))
        return out

    def fmt(prof):
        return '  '.join(f'{lk:8.3f} ({l1:6.1f})' for lk, l1 in prof) + f'   total {sum(p[0] for p in prof):8.3f}'

    # per-stage worst case at each stage t = 1..T (fresh budget at stage t-1), and aligned targets
    Ls, aligned = [], {}
    for t in range(1, T + 1):
        best = None
        for q in (0.01, 0.03, 0.1, 0.3, 0.5):
            J = (rng.random(n[t]) < q).astype(float)
            price = J[own[t]]
            dprev = climb(price, S[t - 1], D[t - 1], ell)
            dt = step(t - 1, dprev)
            v = (leak(dt), float(np.abs(dt).mean()))
            if best is None or v > best[0]:
                best = (v, price, dprev)
        Ls.append(best[0])
        aligned[t] = (best[1], best[2])            # price on stage-(t-1) middles, its climb d_{t-1}
    print('stage:            ' + '  '.join(f'{"t=" + str(t):>17s}' for t in range(1, T + 1)), flush=True)
    print('per-stage worst   ' + fmt(Ls) + '   <- sum of per-stage charges', flush=True)

    # recursive steering: stage-0 prices aimed at stage k
    prices0 = {}
    for k in range(1, T + 1):
        price, target = aligned[k]                 # target = d_{k-1}
        for t in range(k - 2, -1, -1):             # stage-t climb priced by target d_{t+1}
            price = target[own[t + 1]].astype(float)
            if t > 0:
                target = climb(price, S[t], D[t], ell)
        prices0[k] = (price - price.mean()) / (price.std() + 1e-12)
        d0 = climb(prices0[k], S[0], D[0], ell)
        print(f'aim at stage {k}    ' + fmt(run(d0)), flush=True)

    # mixed objectives
    best = None
    grid = [0.0, 0.5, 1.0, 2.0]
    for w in itertools.product(grid, repeat=T):
        if max(w) != 1.0:
            continue
        p = sum(wk * prices0[k + 1] for k, wk in enumerate(w))
        prof = run(climb(p, S[0], D[0], ell))
        tot = sum(x[0] for x in prof)
        if best is None or tot > best[0]:
            best = (tot, w, prof)
    print(f'mixed best w={best[1]} ' + fmt(best[2]), flush=True)

    d0 = np.rint(rng.laplace(0, ell, n[0])).astype(np.int64)
    print('random            ' + fmt(run(d0)), flush=True)


if __name__ == '__main__':
    main()
