#!/usr/bin/env python3
"""Relaxed two-round large-deviation screen for an endpoint input profile.

The fixed input has half the columns full and half empty. After the first row
scramble, a column height is Binomial(m,1/2); this tests symmetric mixtures of
two shifted binomials as atypical empirical height profiles. For each type it
adds its KL cost to a Chernoff rate for the second-round column height under an
independent-column approximation.

This intentionally drops the second-round fixed row-count constraints. A rate
below log(2) says only that this relaxed entropy-union argument cannot certify
the target; it is not a counterexample to fixed scrambles or a row-conditioned
aggregate bound.
"""
import argparse

import numpy as np
from scipy.optimize import brentq
from scipy.special import logsumexp
from scipy.stats import binom


def screen(rows=4096, epsilon=0.0085, shifts=(0, 32, 48, 64, 80, 96, 112, 128)):
    if rows % 2:
        raise ValueError("rows must be even for the balanced endpoint profile")
    heights = np.arange(rows + 1)
    base = binom.pmf(heights, rows, 0.5)
    cuts = np.arange(rows)
    output_heights = np.arange(rows + 1)
    target_second_moment = 2 * epsilon * rows
    results = []

    for shift in shifts:
        if shift == 0:
            profile = base.copy()
        else:
            if shift >= rows / 2:
                raise ValueError(f"shift {shift} must be less than rows/2")
            profile = 0.5 * binom.pmf(heights, rows, 0.5 - shift / rows)
            profile += 0.5 * binom.pmf(heights, rows, 0.5 + shift / rows)
        profile /= profile.sum()
        kl = float(np.sum(profile * (
            np.log(np.maximum(profile, 1e-300))
            - np.log(np.maximum(base, 1e-300)))))

        # Given this intermediate height type, row r has this zero probability
        # in a randomly selected output column after the second scramble.
        row_prob = np.cumsum(profile[::-1])[::-1][1:]
        output_variance = float(np.sum(row_prob * (1 - row_prob)))

        # Independent columns: D is Poisson-binomial with these row rates.
        pmf = np.zeros(rows + 1)
        pmf[0] = 1.0
        used = 0
        for p in row_prob:
            pmf[1:used + 2] = pmf[1:used + 2] * (1 - p) + pmf[:used + 1] * p
            pmf[0] *= 1 - p
            used += 1
        pmf /= pmf.sum()
        centered_square = (output_heights - rows / 2) ** 2
        nonzero = pmf > 0
        log_pmf = np.log(pmf[nonzero])
        square = centered_square[nonzero]

        def tilted(theta):
            log_mgf = logsumexp(log_pmf + theta * square)
            weights = np.exp(log_pmf + theta * square - log_mgf)
            return float(weights @ square), float(log_mgf)

        if output_variance >= target_second_moment:
            output_rate = 0.0
        else:
            hi = 0.01
            while tilted(hi)[0] < target_second_moment and hi < 10:
                hi *= 2
            if hi >= 10 and tilted(hi)[0] < target_second_moment:
                raise RuntimeError("failed to bracket Chernoff tilt")
            theta = brentq(
                lambda t: tilted(t)[0] - target_second_moment, 0.0, hi)
            _, log_mgf = tilted(theta)
            output_rate = theta * target_second_moment - log_mgf

        results.append((shift, kl, output_variance, output_rate, kl + output_rate))

    return target_second_moment, results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--epsilon", type=float, default=0.0085)
    parser.add_argument("--shifts", type=int, nargs="+",
                        default=[0, 32, 48, 64, 80, 96, 112, 128])
    args = parser.parse_args()
    target, data = screen(args.rows, args.epsilon, tuple(args.shifts))
    print(f"rows={args.rows} epsilon={args.epsilon} target E[(D-m/2)^2]={target:.6f}")
    print("shift input_KL second_output_variance second_round_rate combined_rate")
    for row in data:
        print("%5d %.8f %.6f %.8f %.8f" % row)
    print(f"endpoint profile entropy ln(2)={np.log(2):.8f}")
