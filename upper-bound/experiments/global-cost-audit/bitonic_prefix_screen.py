"""Monte Carlo screen of truncated bitonic sorting-network compaction.

The same fixed comparator network is applied to high and hole indicators,
encoded as two bits per position. A final cross-row comparator deletes a
coincident high/hole pair, and the reported high-only fraction is the leakage.
The experiment is a local iid diagnostic.
"""

from __future__ import annotations

import argparse
import numpy as np


def bitonic_layers(n: int):
    if n < 2 or n & (n - 1):
        raise ValueError("n must be a power of two")
    layers = []
    k = 2
    while k <= n:
        j = k // 2
        while j:
            layer = []
            for i in range(n):
                partner = i ^ j
                if partner > i:
                    # Descending blocks send OR to the lower-index wire.
                    or_to_lower = (i & k) == 0
                    layer.append((i, partner, or_to_lower))
            layers.append(layer)
            j //= 2
        k *= 2
    return layers


def screen(n: int, depth: int, samples: int, seed: int) -> tuple[float, float]:
    layers = bitonic_layers(n)[:depth]
    state = np.random.default_rng(seed).choice(4, size=(samples, n), p=[0.5, 0.25, 0.25, 0.0]).astype(np.uint8)
    for layer in layers:
        for i, j, or_to_lower in layer:
            a = state[:, i].copy()
            b = state[:, j].copy()
            state[:, i] = (a | b) if or_to_lower else (a & b)
            state[:, j] = (a & b) if or_to_lower else (a | b)
    leakage = np.count_nonzero(state == 2, axis=1) / n
    return float(leakage.mean()), float(leakage.std(ddof=1) / np.sqrt(samples))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", type=int, nargs="+", default=[64, 256, 1024])
    parser.add_argument("--depth", type=int, default=16, help="comparator layers before final cross-row cancellation")
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=11)
    args = parser.parse_args()
    for n in args.sizes:
        mean, se = screen(n, args.depth, args.samples, args.seed)
        print(f"n={n}; compaction_layers={min(args.depth, len(bitonic_layers(n)))}; leakage={mean:.8f}; SE={se:.8f}")


if __name__ == "__main__":
    main()
