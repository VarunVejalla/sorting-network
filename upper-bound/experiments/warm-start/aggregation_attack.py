#!/usr/bin/env python3
"""Exact attack on one re-bagging step with fringe aggregation (WARM-START.md, kill test 1).

Child bag: nc = F * nv columns, input heights confined to [H-D, H+D]; only the 2D window rows
matter (rows outside are constant), so the row scramble is simulated on those rows only.
Middle column deviation = (#window cells that are 1) - mean. Each new (parent) column stacks the
fringe fragments of F distinct child middle columns (fixed random grouping C_v), so its deviation is
the sum of theirs (fragments are assumed taller than the window, so no clamping).

Attack: pick a random set J of parent columns (fraction p), target S = union of C_v over J, price
+1 / -p/(1-p) and let every child input column climb inside its window. Each run is exact.
Reports, per parent column, E (dev_v - X)_+ (the far-cell mass a band of half-width X leaves) for
X = F*W; and the random-input baseline.

    python aggregation_attack.py D W nv
"""
import sys
import numpy as np


def run(F, D, W, nv, seeds=2):
    nc = F * nv
    rng = np.random.default_rng(F)
    s1 = np.stack([rng.permutation(nc) for _ in range(2 * D)])          # window rows only
    groups = rng.permutation(nc).reshape(nv, F)                           # C_v
    owner = np.empty(nc, dtype=np.int64)
    owner[groups.ravel()] = np.repeat(np.arange(nv), F)
    flat = s1.ravel()
    rows = np.arange(2 * D)[:, None]

    def parent_dev(h):                                                    # h: heights in window coords
        mid = np.bincount(flat[(rows < h[None, :]).ravel()], minlength=nc).astype(float)
        mid -= mid.mean()
        return np.bincount(owner, weights=mid, minlength=nv), mid

    Xs = [F * W * t for t in (0.5, 1, 2, 4)]
    best = np.zeros(len(Xs))
    best_mid = 0.0
    for p in (0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2):
        for seed in range(seeds):
            J = np.random.default_rng(100 + seed).random(nv) < p
            S = J[owner]
            q = S.mean()
            if q == 0 or q == 1:
                continue
            for neg in (1.0, 0.5):
                price = np.where(S, 1.0, -neg * q / (1 - q))
                walk = np.vstack([np.zeros(nc), np.cumsum(price[s1], axis=0)])
                h = np.argmax(walk, axis=0)
                dv, mid = parent_dev(h)
                best_mid = max(best_mid, float(np.maximum(mid - W, 0).mean()))
                for i, X in enumerate(Xs):
                    best[i] = max(best[i], float(np.maximum(dv - X, 0).mean()))
    h = np.random.default_rng(7).integers(0, 2 * D + 1, nc)
    dv, _ = parent_dev(h)
    rnd = [float(np.maximum(dv - X, 0).mean()) for X in Xs]
    return Xs, best, rnd, best_mid


def main():
    D, W, nv = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    print(f'child window D={D}, W={W}, parent columns nv={nv}; far-cell rows per parent column E(dev_v - X)_+')
    for F in (4, 16, 64, 256):
        Xs, att, rnd, bm = run(F, D, W, nv)
        print(f'F={F:4d}  X=' + '/'.join(f'{x:g}' for x in Xs) + ':  attack ' + ' '.join(f'{v:8.3f}' for v in att)
              + '   random ' + ' '.join(f'{v:7.3f}' for v in rnd) + f'   [child excess beyond W {bm:.3f}; 0.25F^2={0.25*F*F:g}]',
              flush=True)


if __name__ == '__main__':
    main()
