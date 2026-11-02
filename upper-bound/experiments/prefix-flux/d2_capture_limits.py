#!/usr/bin/env python3
"""Attack table and first-moment limit for two-round fringe capture.

Attack: best exact escape count over bases and seeds (d2_capture_attack.py).

First moment: take geometric input heights of mean i, the most numerous type, with
exp(n*g(i)) profiles. A given column reaches height f+1 after two rounds with
probability p from the mean-field law. If a fixed set of tau*n columns all do so
with probability about p^(tau*n), the expected number of (input, set) pairs with
that many escaping columns is exp(n*[g + h(tau) + tau*ln p]). While this exceeds 1,
a union bound over inputs is vacuous at escape tau*n. The independence is a
heuristic, so this is an estimate, not a theorem.

    python d2_capture_limits.py
"""
import argparse
import math

import numpy as np

from d2_capture_attack import Stage, attack
from d2_sender_tail_gate import round_step


def column_tail(i, f, cap=160):
    q = i / (1 + i)
    dist = (1 - q) * q ** np.arange(cap + 1)
    dist[-1] += 1 - dist.sum()
    dist = round_step(round_step(dist))
    return float(dist[f + 1:].sum())


def entropy(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)


def union_limit(i, f):
    g = (i + 1) * math.log(i + 1) - i * math.log(i)
    p = column_tail(i, f)
    if p <= 0:
        return 0.0, p
    lo, hi = 0.0, 0.5
    for _ in range(60):
        tau = (lo + hi) / 2
        if g + entropy(tau) + tau * math.log(p) > 0:
            lo = tau
        else:
            hi = tau
    return lo, p


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--columns', type=int, default=1000)
    ap.add_argument('--masses', type=float, nargs='+',
                    default=[0.5, 1, 2, 3, 4, 5, 6, 8.85])
    ap.add_argument('--fringes', type=int, nargs='+', default=[13, 15])
    ap.add_argument('--bases', type=int, nargs='+', default=[0, 1, 2, 3])
    ap.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    ap.add_argument('--no-attack', action='store_true')
    args = ap.parse_args()
    print('f i attack_E/a union_vacuous_to_E/a need')
    for f in args.fringes:
        for i in args.masses:
            best = 0
            if not args.no_attack:
                for seed in args.seeds:
                    stage = Stage(args.columns, 40, seed)
                    for base in args.bases:
                        if base <= i:
                            best = max(best, attack(stage, base, i, f)[0])
            tau, _ = union_limit(i, f)
            print(f'{f} {i} {best / (i * args.columns):.5f} {tau / i:.4f} '
                  f'{1 / 128:.4f}', flush=True)


if __name__ == '__main__':
    main()
