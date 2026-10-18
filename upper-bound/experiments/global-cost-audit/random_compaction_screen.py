"""Monte Carlo screen of unstructured random-matching compaction networks.

Each layer is an arbitrary perfect matching with OR sent to the first half
of a seeded random permutation and AND to the second half. The same fixed
network is applied to high and hole indicators (encoded as two bits). A final
cross-row comparator deletes the both-defect state; reported leakage is the
remaining high-only fraction. This is a diagnostic, not a theorem.
"""

from __future__ import annotations

import argparse
import numpy as np


def screen(
    n: int,
    depth: int,
    samples: int,
    schedule_seed: int,
    input_seed: int,
    orientation: str,
) -> tuple[float, float]:
    schedule_rng = np.random.default_rng(schedule_seed)
    layers = []
    rank = None
    if orientation == "fixed-order":
        order = schedule_rng.permutation(n)
        rank = np.empty(n, dtype=np.int64)
        rank[order] = np.arange(n)
    for _ in range(depth):
        p = schedule_rng.permutation(n)
        left, right = p[: n // 2].copy(), p[n // 2 :].copy()
        if rank is not None:
            flip = rank[left] > rank[right]
            left, right = np.where(flip, right, left), np.where(flip, left, right)
        layers.append((left, right))

    input_rng = np.random.default_rng(input_seed)
    state = input_rng.choice(4, size=(samples, n), p=[0.5, 0.25, 0.25, 0.0]).astype(np.uint8)
    for left, right in layers:
        a = state[:, left].copy()
        b = state[:, right].copy()
        state[:, left] = a | b
        state[:, right] = a & b

    per_sample = np.count_nonzero(state == 2, axis=1) / n
    mean = float(per_sample.mean())
    se = float(per_sample.std(ddof=1) / np.sqrt(samples))
    return mean, se


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=256)
    parser.add_argument("--depths", type=int, nargs="+", default=[8, 16])
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--schedules", type=int, default=5)
    parser.add_argument("--orientation", choices=["per-layer", "fixed-order"], default="per-layer")
    args = parser.parse_args()
    for depth in args.depths:
        vals = [
            screen(args.n, depth, args.samples, seed, 1000 + seed, args.orientation)
            for seed in range(args.schedules)
        ]
        report = "; ".join(f"seed{seed}: {mean:.6f} (SE {se:.6f})" for seed, (mean, se) in enumerate(vals))
        print(f"n={args.n}; compaction_layers={depth}; orientation={args.orientation}; post-cross leakage: {report}")


if __name__ == "__main__":
    main()
