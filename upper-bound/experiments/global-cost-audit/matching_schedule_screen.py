"""Small diagnostic for fixed cross-boundary matching schedules.

Requires NumPy and SciPy. This does not model all comparator networks or prove
anything about the central repair contract. It samples iid upper-high/lower-
hole indicators, then compares random fixed schedules with a schedule trained
greedily to maximize the expected number of repairs at each layer.
"""

from __future__ import annotations

import argparse

import numpy as np
from scipy.optimize import linear_sum_assignment


def apply_layer(high: np.ndarray, hole: np.ndarray, permutation: np.ndarray):
    """Repair pairs with both defects; return the updated defect indicators."""
    old_high = high
    old_hole = hole
    high = old_high & ~old_hole[:, permutation]
    hole = old_hole.copy()
    hole[:, permutation] = old_hole[:, permutation] & ~old_high
    return high, hole


def trained_schedule(rng: np.random.Generator, samples: int, wires: int, depth: int):
    high = rng.random((samples, wires)) < 0.25
    hole = rng.random((samples, wires)) < 0.25
    schedule = []
    for layer in range(depth):
        if layer == 0:
            permutation = np.arange(wires)
        else:
            joint_counts = high.astype(np.int32).T @ hole.astype(np.int32)
            rows, cols = linear_sum_assignment(-joint_counts)
            permutation = cols[np.argsort(rows)]
        high, hole = apply_layer(high, hole, permutation)
        schedule.append(permutation)
    return schedule, float(high.mean())


def evaluate(rng, schedule, samples, wires):
    high = rng.random((samples, wires)) < 0.25
    hole = rng.random((samples, wires)) < 0.25
    for permutation in schedule:
        high, hole = apply_layer(high, hole, permutation)
    return float(high.mean())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=64)
    parser.add_argument("--depth", type=int, default=17)
    parser.add_argument("--training-samples", type=int, default=12000)
    parser.add_argument("--validation-samples", type=int, default=50000)
    parser.add_argument("--seed", type=int, default=20261010)
    parser.add_argument("--random-schedules", type=int, default=5)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    schedule, training_error = trained_schedule(
        rng, args.training_samples, args.wires, args.depth
    )
    validation_error = evaluate(
        rng, schedule, args.validation_samples, args.wires
    )
    print(f"trained-schedule training residual: {training_error:.6f}")
    print(f"trained-schedule validation residual: {validation_error:.6f}")

    random_errors = []
    for trial in range(args.random_schedules):
        trial_rng = np.random.default_rng(args.seed + trial + 1)
        random_schedule = [
            trial_rng.permutation(args.wires) for _ in range(args.depth)
        ]
        random_errors.append(
            evaluate(
                np.random.default_rng(args.seed + 1000 + trial),
                random_schedule,
                args.validation_samples,
                args.wires,
            )
        )
    print("random-schedule residuals:", ", ".join(f"{x:.6f}" for x in random_errors))
    print(f"random-schedule mean: {np.mean(random_errors):.6f}")


if __name__ == "__main__":
    main()
