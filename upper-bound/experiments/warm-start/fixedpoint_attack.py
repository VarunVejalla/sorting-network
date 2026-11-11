#!/usr/bin/env python3
"""Per-stage worst-case L1 fixed point (WARM-START.md section 11, bandless stage).

Bandless stage: sort, scramble, split by rows. Exported strays per boundary per column equal the input
L1 at that threshold exactly, so the per-stage provable leak is the fixed point of
  ell' = max over inputs with L1 <= ell of the grouped next-input L1   (Lemma G: ell' <~ 2 C F sqrt(ell)).
Iterates the aligned dual climb (Theorem R2 form, the Lemma G tightness attack) from ell = 0.45 F.
Exact runs; lower bounds for the sampled scramble and wiring.

    python fixedpoint_attack.py F N iters [start ell/F^2]
"""
import sys
import numpy as np


def step(F, N, ell, rng):
    D = int(6 * ell) + 4 * F + 16
    s1 = np.stack([rng.permutation(N).astype(np.int32) for _ in range(2 * D)])
    owner = np.empty(N, dtype=np.int64)
    owner[rng.permutation(N)] = np.repeat(np.arange(N // F), F)
    rows = np.arange(2 * D)[:, None]
    flat = s1.ravel()

    def nxt(h):
        mid = np.bincount(flat[(rows < h[None, :]).ravel()], minlength=N).astype(float)
        return np.bincount(owner, weights=mid - mid.mean(), minlength=N // F)

    best = (0.0, None)
    for q in (0.3, 0.5):
        S = (rng.random(N // F) < q)[owner]
        p = S.mean()
        inc = np.where(S, 1 - p, -p).astype(np.float32)[s1]
        up = np.cumsum(inc[D:], axis=0)
        dn = -np.cumsum(inc[:D][::-1], axis=0)
        H = np.arange(1, D + 1, dtype=np.float32)[:, None]
        used = None
        for lam in np.geomspace(1e-4, 0.5, 400):
            a, b = up - lam * H, dn - lam * H
            va, vb = a.max(0), b.max(0)
            d = np.where((va >= vb) & (va > 0), a.argmax(0) + 1, np.where(vb > 0, -(b.argmax(0) + 1), 0))
            d = d - int(round(d.mean()))
            if np.abs(d).mean() <= ell:
                used = d
                break
        if used is None:
            continue
        L1 = float(np.abs(nxt(D + used)).mean())
        if L1 > best[0]:
            best = (L1, (q, float(np.abs(used).mean())))
    return best


def main():
    F, N, iters = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(7 * F)
    ell = float(sys.argv[4]) * F * F if len(sys.argv) > 4 else 0.45 * F   # optional start, multiple of F^2
    print(f'F={F} N={N} (groups {N // F})', flush=True)
    for it in range(iters):
        L1, info = step(F, N, ell, rng)
        C = L1 / (2 * F * np.sqrt(ell))
        print(f'  iter {it}: budget ell {ell:9.2f} -> next L1 {L1:9.2f}   ell/F^2 {ell / F**2:6.3f}'
              f'   C = ell\'/(2F sqrt ell) {C:5.3f}   (q, used) {info}', flush=True)
        ell = L1


if __name__ == '__main__':
    main()
