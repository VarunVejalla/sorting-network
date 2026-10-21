#!/usr/bin/env python3
"""Matrix-free floating-point screen for random matching products.

The returned power-iteration value estimates the largest singular value of a
product of random perfect-matching averages on the zero-sum subspace. It is
not an upper certificate and gives no unbounded family.
"""
import argparse

import numpy as np


def apply_matchings(x, matchings):
    y = x.copy()
    for pairs in matchings:
        avg = (y[pairs[:, 0]] + y[pairs[:, 1]]) * 0.5
        y[pairs[:, 0]] = avg
        y[pairs[:, 1]] = avg
    return y


def estimate(packet_count, rounds, seed, iterations):
    rng = np.random.default_rng(seed)
    matchings = [rng.permutation(packet_count).reshape(-1, 2)
                 for _ in range(rounds)]
    x = rng.standard_normal(packet_count)
    x -= x.mean()
    x /= np.linalg.norm(x)
    for _ in range(iterations):
        y = apply_matchings(x, matchings)
        x = apply_matchings(y, reversed(matchings))
        x -= x.mean()
        norm = np.linalg.norm(x)
        if norm == 0:
            return 0.0
        x /= norm
    return float(np.linalg.norm(apply_matchings(x, matchings)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+",
                        default=[1024, 4096, 16384, 65536, 262144])
    parser.add_argument("--rounds", type=int, default=23)
    parser.add_argument("--seed", type=int, default=123)
    parser.add_argument("--iterations", type=int, default=40)
    args = parser.parse_args()
    for c in args.packets:
        if c <= 0 or c % 2:
            raise ValueError("packet counts must be positive and even")
        rho = estimate(c, args.rounds, args.seed, args.iterations)
        print(f"packets={c} rounds={args.rounds} seed={args.seed} "
              f"power_estimate_rho={rho:.10g}")


if __name__ == "__main__":
    main()
