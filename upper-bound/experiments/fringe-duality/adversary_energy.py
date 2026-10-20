"""Greedy adversary for the round-1 energy E = sum_T z_T^2 at mass j (model check of the 'true' E/j).

Random scramble sigma (m rows, n columns, independent uniform row permutations). The adversary raises
input column heights one cell at a time (h_c -> h_c + 1 adds a one to output sigma_{h_c}(c)), greedily
choosing the cell with the largest marginal gain 2 z_T + 1, up to mass j. Also a structured attack
(target set A, columns sigma_r^{-1}(A) at rows r < k). Reports E/j.
"""
import heapq
import sys

import numpy as np

rng = np.random.default_rng(1)
m, n = int(sys.argv[1]) if len(sys.argv) > 1 else 400, int(sys.argv[2]) if len(sys.argv) > 2 else 4000
sig = np.array([rng.permutation(n) for _ in range(m)])      # sig[r, c] = output of input c at row r


def greedy(j):
    h = np.zeros(n, dtype=int)
    z = np.zeros(n, dtype=int)
    # lazy max-heap of (gain, c); gain of raising c is 2 z[sig[h_c, c]] + 1
    heap = [(-(2 * z[sig[0, c]] + 1), c) for c in range(n)]
    heapq.heapify(heap)
    for _ in range(j):
        while True:
            g, c = heapq.heappop(heap)
            if h[c] >= m:
                continue
            cur = 2 * z[sig[h[c], c]] + 1
            if -g == cur:
                break
            heapq.heappush(heap, (-cur, c))
        T = sig[h[c], c]
        z[T] += 1
        h[c] += 1
        if h[c] < m:
            heapq.heappush(heap, (-(2 * z[sig[h[c], c]] + 1), c))
    return int((z.astype(np.int64) ** 2).sum())


def structured(j, k):
    inv = np.argsort(sig, axis=1)                             # inv[r, T] = input column mapped to T at row r
    a = max(1, int(2 * j / (k * k)))
    A = rng.choice(n, size=min(a, n), replace=False)
    h = np.zeros(n, dtype=int)
    for r in range(k):
        cols = inv[r, A]
        h[cols] = np.maximum(h[cols], r + 1)
    while h.sum() > j and len(A) > 1:
        A = A[:-1]
        h[:] = 0
        for r in range(k):
            cols = inv[r, A]
            h[cols] = np.maximum(h[cols], r + 1)
    z = np.zeros(n, dtype=np.int64)
    for c in np.nonzero(h)[0]:
        np.add.at(z, sig[:h[c], c], 1)
    return int((z ** 2).sum()), int(h.sum())


for j in (200, 1000, 4000, 16000):
    E = greedy(j)
    best_s = max((structured(j, k) for k in (2, 4, 8, 16, 32)), key=lambda t: t[0] / max(t[1], 1))
    print(f"m={m} n={n} j={j}: greedy E/j = {E / j:6.2f};  structured best E/mass = {best_s[0] / best_s[1]:6.2f}"
          f" (mass {best_s[1]});  background j/n = {j / n:.2f}", flush=True)
