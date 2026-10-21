#!/usr/bin/env python3
"""Diagnostic for product-affine Chernoff potentials on a tiny UB-28 cone.

Model: two independent uniform width-h input blocks, one random cross-matching
layer (min goes left, max right), then split both blocks into halves. Bound the
event that the lower block's left half is nonempty and the upper block's left
half is empty. The exact event probability is computed from the count
transitions; the screen searches for sequential affine majorants of the two
split log-MGFs and matching log-MGF.

This is a numerical diagnostic only, not a certificate or the full UB-28
terminal event. The reported affine value comes from a feasible parameter
choice, so it is an upper bound in exact arithmetic; floating point and the
optimizer make the printed value non-rigorous.
"""

import argparse
import math

import numpy as np
from scipy.optimize import differential_evolution
from scipy.special import gammaln, logsumexp


def log_choose(n, k):
    if k < 0 or k > n:
        return -math.inf
    return gammaln(n + 1) - gammaln(k + 1) - gammaln(n - k + 1)


def run(width, seed=1, maxiter=100):
    half = width // 2
    counts = np.arange(width + 1)
    match_x = np.arange(width + 1)
    split_x = np.arange(half + 1)

    split = np.full((width + 1, half + 1), -math.inf)
    for parent in range(width + 1):
        for left in range(half + 1):
            if 0 <= parent - left <= half:
                split[parent, left] = (
                    log_choose(parent, left)
                    + log_choose(width - parent, half - left)
                    - log_choose(width, half)
                )

    matching = np.full((width + 1, width + 1, width + 1), -math.inf)
    for a in range(width + 1):
        for b in range(width + 1):
            for overlap in range(max(0, a + b - width), min(a, b) + 1):
                matching[a, b, overlap] = (
                    log_choose(b, overlap)
                    + log_choose(width - b, a - overlap)
                    - log_choose(width, a)
                )

    # The two block counts are coupled by conservation. Sum the exact annealed
    # count transitions rather than multiplying marginal block probabilities.
    initial = np.array([
        log_choose(width, a) - width * math.log(2)
        for a in range(width + 1)
    ])
    split_nonempty = np.empty(width + 1)
    for parent in range(width + 1):
        log_empty = split[parent, 0]
        split_nonempty[parent] = (
            -math.inf if log_empty == 0
            else math.log1p(-math.exp(log_empty)) if math.isfinite(log_empty)
            else 0.0
        )
    exact_terms = []
    for a in range(width + 1):
        for b in range(width + 1):
            for overlap in range(width + 1):
                log_match = matching[a, b, overlap]
                if not math.isfinite(log_match):
                    continue
                right_count = a + b - overlap
                log_right_empty = split[right_count, 0]
                if math.isfinite(log_right_empty) and math.isfinite(split_nonempty[overlap]):
                    exact_terms.append(
                        initial[a] + initial[b] + log_match
                        + split_nonempty[overlap] + log_right_empty
                    )
    exact_log_probability = float(logsumexp(exact_terms))

    def objective(parameters):
        lam, mu, left_slope, right_slope, input_left, input_right = parameters

        left_split = logsumexp(
            split + lam * split_x[None, :], axis=1
        )
        right_split = logsumexp(
            split + mu * split_x[None, :], axis=1
        )
        left_intercept = np.max(left_split - left_slope * counts)
        right_intercept = np.max(right_split - right_slope * counts)

        matching_tilt = (
            left_slope * match_x[None, None, :]
            + right_slope
            * (counts[:, None, None] + counts[None, :, None] - match_x[None, None, :])
        )
        matching_intercept = np.max(
            logsumexp(matching + matching_tilt, axis=2)
            - input_left * counts[:, None]
            - input_right * counts[None, :]
        )

        initial_log_mgf = width * (
            np.logaddexp(0, input_left)
            + np.logaddexp(0, input_right)
            - 2 * math.log(2)
        )
        # Terminal indicator <= exp(lam*(left_count-1) + mu*right_count),
        # for lam >= 0 and mu <= 0.
        return (
            left_intercept
            + right_intercept
            + matching_intercept
            + initial_log_mgf
            - lam
        )

    result = differential_evolution(
        objective,
        [(0, 12), (-12, 0), (-12, 12), (-12, 12), (-12, 12), (-12, 12)],
        tol=1e-5,
        popsize=7,
        maxiter=maxiter,
        polish=True,
        seed=seed,
    )

    n = 2 * width
    return {
        "width": width,
        "exact_log_probability": exact_log_probability,
        "affine_log_upper": float(result.fun),
        "exact_rate_per_input": -exact_log_probability / n,
        "affine_rate_per_input": -float(result.fun) / n,
        "slack_nats": float(result.fun) - exact_log_probability,
        "parameters": result.x,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--widths", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--maxiter", type=int, default=100)
    args = parser.parse_args()
    for width in args.widths:
        if width < 2 or width & (width - 1):
            raise ValueError("widths must be powers of two >= 2")
        result = run(width, maxiter=args.maxiter)
        print(
            f"h={width} exact_rate={result['exact_rate_per_input']:.9f} "
            f"affine_rate={result['affine_rate_per_input']:.9f} "
            f"slack_nats={result['slack_nats']:.6f}"
        )
        print("  parameters:", " ".join(f"{x:.6g}" for x in result["parameters"]))


if __name__ == "__main__":
    main()
