#!/usr/bin/env python3
"""Row-marginal-preserving type screen for the endpoint input profile.

For an intermediate height type nu, let p_r be its row densities after the
first column sort. This constructs a feasible second-round column-type law Q:
an equal mixture of two product Bernoulli laws with marginals p +/- k p(1-p).
The mixture has exactly the prescribed row marginals p and is tuned so its
column-height second moment reaches the aggregate-area threshold.

The input-type KL is computed directly. The second-type KL is evaluated from
an exact mixture identity, but the remaining expectation of softplus of a sum
of independent two-point variables uses a Gaussian Edgeworth approximation.
This is a research screen, not a certified rate or a counterexample to a
fixed pair of scrambles.
"""
import argparse

import numpy as np
from scipy.optimize import brentq
from scipy.special import ndtr
from scipy.stats import binom


def screen(rows=4096, epsilon=0.0085,
           shifts=(0, 16, 24, 32, 40, 48, 56, 64)):
    if rows % 2:
        raise ValueError("rows must be even for the balanced endpoint profile")
    heights = np.arange(rows + 1)
    base = binom.pmf(heights, rows, 0.5)
    target = 2 * epsilon * rows
    results = []

    for shift in shifts:
        if shift == 0:
            nu = base.copy()
        else:
            if shift >= rows / 2:
                raise ValueError(f"shift {shift} must be less than rows/2")
            nu = 0.5 * binom.pmf(heights, rows, 0.5 - shift / rows)
            nu += 0.5 * binom.pmf(heights, rows, 0.5 + shift / rows)
        nu /= nu.sum()
        input_kl = float(np.sum(nu * (
            np.log(np.maximum(nu, 1e-300))
            - np.log(np.maximum(base, 1e-300)))))

        # p[r] is the fraction of columns containing a zero below row r.
        p = np.cumsum(nu[::-1])[::-1][1:]
        active = (p > 1e-12) & (p < 1 - 1e-12)
        v = p * (1 - p)
        base_variance = float(v.sum())
        pa, va = p[active], v[active]

        def mixture_second_moment(k):
            delta = k * va
            q_plus = pa + delta
            untouched_variance = base_variance - float(va.sum())
            return float(untouched_variance
                         + np.sum(q_plus * (1 - q_plus)) + delta.sum() ** 2)

        if base_variance >= target:
            k = 0.0
        else:
            k = brentq(lambda x: mixture_second_moment(x) - target, 0, 1)
        if k == 0.0:
            results.append((shift, input_kl, base_variance, k, 0.0,
                            0.0, 0.0, 0.0, 0.0, input_kl))
            continue
        delta = k * va
        q_plus, q_minus = pa + delta, pa - delta
        shift_mean = float(delta.sum())

        # D(product(q_plus) || product(p)); the minus branch has the same KL.
        product_kl = float(np.sum(
            q_plus * np.log(q_plus / pa)
            + (1 - q_plus) * np.log((1 - q_plus) / (1 - pa))))

        # Under product(q_plus), Delta=log(L_plus/L_minus) is a sum of
        # independent two-point terms. Bound E softplus(-Delta) by a
        # Lindeberg replacement with the matching Gaussian, using
        # ||h'''||_infinity = 1/(6 sqrt(3)) for h(x)=softplus(-x).
        log1 = np.log(q_plus / q_minus)
        log0 = np.log((1 - q_plus) / (1 - q_minus))
        step = log1 - log0
        mean = float(np.sum(q_plus * log1 + (1 - q_plus) * log0))
        variance_i = q_plus * (1 - q_plus) * step ** 2
        variance = float(np.sum(variance_i))
        sd = np.sqrt(variance)
        third_y = float(np.sum(q_plus * (1 - q_plus)
                               * ((1 - q_plus) ** 2 + q_plus ** 2)
                               * np.abs(step) ** 3))
        third_gaussian = float(2 * np.sqrt(2 / np.pi)
                               * np.sum(variance_i ** 1.5))
        lindeberg_error = (third_y + third_gaussian) / (36 * np.sqrt(3))

        # For X~N(mean,sd^2), split at zero and use softplus(-x)<=exp(-x)
        # for x>=0, and <= -x+exp(x) for x<0. The three truncated-normal
        # expectations below are closed form.
        density = lambda x: np.exp(-x * x / 2) / np.sqrt(2 * np.pi)
        gaussian_softplus_upper = float(
            np.exp(-mean + variance / 2) * ndtr((mean - variance) / sd)
            - mean * ndtr(-mean / sd) + sd * density(mean / sd)
            + np.exp(mean + variance / 2) * ndtr((-mean - variance) / sd))
        softplus_upper = gaussian_softplus_upper + lindeberg_error
        mixture_kl_upper = product_kl - np.log(2) + softplus_upper
        results.append((shift, input_kl, base_variance, k, shift_mean,
                        product_kl, gaussian_softplus_upper, lindeberg_error,
                        mixture_kl_upper, input_kl + mixture_kl_upper))
    return target, results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--epsilon", type=float, default=0.0085)
    parser.add_argument("--shifts", type=int, nargs="+",
                        default=[0, 16, 24, 32, 40, 48, 56, 64])
    args = parser.parse_args()
    target, results = screen(args.rows, args.epsilon, tuple(args.shifts))
    print(f"rows={args.rows} epsilon={args.epsilon} target second moment={target:.6f}")
    print("shift input_KL base_variance k component_shift product_KL gaussian_softplus_bound lindeberg_error mix_KL_upper combined_upper")
    for row in results:
        print("%5d %.8f %.6f %.8f %.5f %.8f %.8f %.8f %.8f %.8f" % row)
    print(f"endpoint profile entropy ln(2)={np.log(2):.8f}")
