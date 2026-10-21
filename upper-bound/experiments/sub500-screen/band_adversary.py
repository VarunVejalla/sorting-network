"""UB-32 check: is the 1/W round-1 tail real? Adversary for the band repair.

Threshold t = i n (top i rows' worth of keys). First column sort: staircase h, sum h = i n. Round 1 (scramble
sigma1): z_u = #{(r, c) : r < h_c, sigma1_r(c) = u}. Without the third sort, a band repair of half-height W
cannot fix ones from sources with z_u > i + W: error >= E(W) = sum_u (z_u - i - W)_+.

Attack (walk-duality LP): pick a target set T (density p), give each column c the height h_c maximising
N_c^T(h) - lam h (its own walk max), with lam tuned so that sum h = i n. Print E(W) * W / j for a range of W:
a constant ratio means the 1/W law is achieved by an actual input, so no proof can beat it.
"""
import sys
import numpy as np

m = int(sys.argv[1]) if len(sys.argv) > 1 else 4096
n = int(sys.argv[2]) if len(sys.argv) > 2 else 2048
rng = np.random.default_rng(1)
i = m // 2
j = i * n
# sigma1_r(c) for all rows: perm[r] is a permutation of columns
perm = np.stack([rng.permutation(n) for _ in range(m)])          # (m, n): target of (r, c)


def attack(p):
    T = np.zeros(n, bool)
    T[rng.choice(n, max(1, int(p * n)), replace=False)] = True
    hit = T[perm].astype(np.int32)                                  # (m, n): 1 if (r, c) lands in T
    cum = np.cumsum(hit, axis=0)                                    # N_c^T(h) for h = 1..m
    hs = np.arange(1, m + 1)[:, None]

    def heights(lam):
        val = cum - lam * hs
        best = val.argmax(axis=0)
        h = np.where(val[best, np.arange(n)] > 0, best + 1, 0)
        return h

    lo, hi = 0.0, 1.0
    for _ in range(50):
        lam = (lo + hi) / 2
        if heights(lam).sum() > j:
            lo = lam
        else:
            hi = lam
    h = heights(hi)
    # fill the remaining mass on columns without changing T much: put it on the lowest columns (adds background)
    rest = j - h.sum()
    order = np.argsort(h)
    k = 0
    while rest > 0:
        c = order[k % n]
        add = min(rest, m - h[c])
        h[c] += add
        rest -= add
        k += 1
    act = np.arange(m)[:, None] < h[None, :]                        # (m, n) active cells
    z = np.bincount(perm[act], minlength=n)
    return z


print(f"m = {m}, n = {n}, i = m/2, j = {j}")
for W in (64, 128, 256, 512, 1024):
    best = 0.0
    for p in (i / (8 * W * W), i / (2 * W * W), 2 * i / (W * W), 8 * i / (W * W)):
        if p * n < 1 or p > 0.5:
            continue
        z = attack(p)
        E = np.clip(z - i - W, 0, None).sum()
        best = max(best, E)
    zr = np.bincount(perm[np.arange(m)[:, None] < rng.permutation(np.repeat([m, 0], n // 2))[None, :]], minlength=n)
    Er = np.clip(zr - i - W, 0, None).sum()
    print(f"  W = {W:5d}: adversary E(W) = {best:9.0f}  E*W/j = {best * W / j:.4f}   (random half/half input: E = {Er:.0f})")
