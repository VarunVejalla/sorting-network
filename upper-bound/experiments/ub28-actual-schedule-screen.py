#!/usr/bin/env python3
"""Finite randomized screen of the actual UB-28 two-offset schedule.

For widths >= 200 each local pass uses 70 independent uniform matchings.
For smaller widths it uses the exact cyclic complete-bipartite schedule of
`width` matchings. This is diagnostic evidence only, not a sorting proof.
"""
import argparse
import random


def build(n, seed):
    rng = random.Random(seed)
    schedule = []
    for k in reversed(range(n.bit_length() - 1)):
        h = 1 << k
        d = 70 if h >= 200 else h
        for offset in (0, 1):
            pairs = list(range(offset, n // h - 1, 2))
            for t in range(d):
                layer = []
                for b in pairs:
                    left = b * h
                    if h >= 200:
                        p = list(range(h))
                        rng.shuffle(p)
                    else:
                        p = [(i + t) % h for i in range(h)]
                    layer.extend((left + i, left + h + p[i]) for i in range(h))
                schedule.append(layer)
    return schedule


def fails(n, schedule, word):
    x = [(word >> i) & 1 for i in range(n)]
    for layer in schedule:
        for i, j in layer:
            if x[i] > x[j]:
                x[i], x[j] = x[j], x[i]
    return next((i for i in range(n - 1) if x[i] > x[i + 1]), None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sizes', nargs='+', type=int, default=[256, 512, 1024, 2048])
    ap.add_argument('--seeds', type=int, default=4)
    ap.add_argument('--random-inputs', type=int, default=12)
    args = ap.parse_args()
    for n in args.sizes:
        for seed in range(args.seeds):
            schedule = build(n, seed)
            rng = random.Random((n << 16) + seed)
            words = [rng.getrandbits(n) for _ in range(args.random_inputs)]
            words += [(1 << k) - 1 for k in sorted({0, 1, 2, 3, n//10, n//4, n//2, 3*n//4, 9*n//10, n})]
            witness = next(((w, fails(n, schedule, w)) for w in words if fails(n, schedule, w) is not None), None)
            print(f'n={n} seed={seed} layers={len(schedule)} tests={len(words)} ' +
                  (f'FAIL word={witness[0]:x} inversion={witness[1]}' if witness else 'all sorted'), flush=True)

if __name__ == '__main__':
    main()
