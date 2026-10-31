#!/usr/bin/env python3
"""Numerically screen the NA/Chernoff tail for one final random scramble.

The intermediate profiles are produced from fixed seed-0 first and second
scrambles. This is only a profile-conditioned diagnostic, not a uniform tail
or a three-round existence proof.
"""
import math

import numpy as np

from local_core_multiround_adversary import evaluate, make_scrambles


def profile_tail_bound(heights, rows, columns, threshold):
    total = sum(heights)
    mean = total / columns
    remainder = total % columns
    rho = remainder * (columns - remainder) / columns
    row_counts = [sum(height > r for height in heights)
                  for r in range(rows)]

    # Remove deterministic row choices and convolve the remaining independent
    # Bernoulli marginals for the height of one output column.
    offset = sum(count == columns for count in row_counts)
    probs = [count / columns for count in row_counts
             if 0 < count < columns]
    pmf = np.array([1.0])
    for probability in probs:
        pmf = np.convolve(pmf, [1 - probability, probability])
    support = np.arange(len(pmf)) + offset

    best = (math.inf, None)
    for lam in np.geomspace(1e-8, 0.5, 200):
        plus = np.exp(2 * lam * np.maximum(support - mean, 0) ** 2)
        minus = np.exp(2 * lam * np.maximum(mean - support, 0) ** 2)
        log_bound = (-lam * (2 * threshold + rho)
                     + columns / 2 * (math.log(float(pmf @ plus))
                                      + math.log(float(pmf @ minus))))
        if log_bound < best[0]:
            best = (log_bound, lam)
    area = (sum(h * h for h in heights)
            - ((columns - remainder) * (total // columns) ** 2
               + remainder * (total // columns + 1) ** 2)) // 2
    variance = sum(p * (1 - p) for p in probs)
    return area, len(probs), variance, best


def main():
    rows, columns, seed = 4096, 64, 0
    threshold = math.ceil(0.0085 * rows * columns)
    scrambles = make_scrambles(rows, columns, seed, rounds=2)
    inputs = {
        "half-full": [0] * (columns // 2) + [rows] * (columns // 2),
        "ramp": [round(rows * i / (columns - 1))
                 for i in range(columns)],
        "alternating": [rows if i % 2 else 0 for i in range(columns)],
    }
    print(f"rows={rows}, columns={columns}, final-area-threshold={threshold}, "
          f"log-labeled-profile-count={columns * math.log(rows + 1):.6f}")
    for name, initial in inputs.items():
        intermediate = evaluate(initial, scrambles)[0][-1]
        area, active_rows, variance, bound = profile_tail_bound(
            intermediate, rows, columns, threshold)
        print(f"{name}: A2={area}, active_rows={active_rows}, "
              f"marginal_variance={variance:.6f}, "
              f"best_grid_log_tail={bound[0]:.6f} at lambda={bound[1]:.6g}")


if __name__ == "__main__":
    main()
