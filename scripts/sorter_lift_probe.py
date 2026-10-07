"""Exact Boolean-input probe of matching lifts; research experiment, not a proof."""
import json
from fractions import Fraction
import numpy as np


def odd_even(n):
    gates = []
    def merge(lo, size, stride):
        step = 2 * stride
        if step < size:
            merge(lo, size, step)
            merge(lo + stride, size, step)
            for i in range(lo + stride, lo + size - stride, step):
                gates.append((i, i + stride))
        else:
            gates.append((lo, lo + stride))
    def sort(lo, size):
        if size > 1:
            sort(lo, size // 2)
            sort(lo + size // 2, size // 2)
            merge(lo, size, 1)
    sort(0, n)
    return gates


def evaluate(m, b, seed):
    rng = np.random.default_rng(seed)
    n = m * b
    inputs = np.arange(1 << n, dtype=np.uint32)
    out = inputs.copy()
    gates = []
    depth = [0] * n
    for a, c in odd_even(m):
        perm = np.arange(b) if seed is None else rng.permutation(b)
        for r, s in enumerate(perm):
            i, j = a * b + r, c * b + int(s)
            gates.append((i, j))
            depth[i] = depth[j] = max(depth[i], depth[j]) + 1
            swap = ((out >> i) & 1) & (1 - ((out >> j) & 1))
            out ^= (swap << i) | (swap << j)
    count = np.array([int(x).bit_count() for x in inputs], dtype=np.int16)
    left = np.zeros(len(out), dtype=np.int16)
    right_zeros = np.zeros(len(out), dtype=np.int16)
    for i in range(n // 2):
        left += ((out >> i) & 1).astype(np.int16)
        right_zeros += (1 - ((out >> (i + n // 2)) & 1)).astype(np.int16)
    worst = Fraction(0)
    witness = None
    for side, weights, errors in [('ones', count, left), ('zeros', n-count, right_zeros)]:
        for k in range(1, n // 2 + 1):
            ids = np.flatnonzero(weights == k)
            idx = int(ids[np.argmax(errors[ids])])
            error = int(errors[idx])
            ratio = Fraction(error, k)
            if ratio > worst:
                worst = ratio
                witness = dict(side=side, k=k, misplaced=error,
                               input=int(inputs[idx]), output=int(out[idx]))
    return dict(m=m, b=b, seed=seed, depth=max(depth), epsilon=str(worst), witness=witness)


if __name__ == '__main__':
    results = []
    for m, b in [(4, 1), (8, 1), (4, 2), (4, 4), (8, 2)]:
        rows = [evaluate(m, b, None)]
        if b > 1:
            rows += [evaluate(m, b, seed) for seed in range(64)]
        best = min(rows, key=lambda x: Fraction(x['epsilon']))
        results.append(dict(m=m, b=b, identity=rows[0], best=best,
                            worst_epsilon=str(max(Fraction(x['epsilon']) for x in rows)),
                            samples=len(rows)))
    mean_field = []
    for m in [64, 256, 1024, 2048]:
        densities = [0.5] * m
        for a, b in odd_even(m):
            x, y = densities[a], densities[b]
            densities[a], densities[b] = x*y, x+y-x*y
        mean_field.append(dict(m=m, leakage_ratio=2*sum(densities[:m//2])/m))
    print(json.dumps(dict(exact_lifts=results, mean_field=mean_field), indent=2))
