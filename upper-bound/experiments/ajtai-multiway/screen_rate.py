#!/usr/bin/env python3
"""Numerically screen the dense-rank entropy rate for N=p^2 instances.

This samples a continuous rate function; it is diagnostic, not a rigorous
global optimization or an outward-rounded finite certificate. It complements
screen_multicut.py, whose exact finite sums are practical at small N.
Requires NumPy.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def composition_entropy(mu: np.ndarray) -> np.ndarray:
    return (mu + 1) * np.log(mu + 1) - mu * np.log(np.maximum(mu, 1e-300))


def binary_entropy(x: np.ndarray) -> np.ndarray:
    x = np.clip(x, 1e-300, 1 - 1e-15)
    return -x * np.log(x) - (1 - x) * np.log(1 - x)


def composition_entropy_scalar(mu: float) -> float:
    return (mu + 1) * math.log(mu + 1) - mu * math.log(mu) if mu > 0 else 0.0


def interval_rate_upper(k: int, p: int, leakage: float, width: float) -> tuple[float, tuple[int, float, float]]:
    """Conservative 1-D envelope for the dense-rank exponential rate.

    Uses H(q/N) <= log(2), increasing composition entropy, and the uniform
    lower bound Delta >= E*a on a rank interval [a,b]. If x_max is its
    largest feasible overfull-column fraction, the Hoeffding exponent is at
    least 2*(E*a)^2/(k*x_max). This loose bound avoids assuming the exponent
    is minimized at the feasibility boundary. Floating-point only.
    """
    worst = (-math.inf, (0, 0.0, 0.0))
    for h in range(k // p, k, k // p):
        for s in (h, k - h):
            t = k - s
            lo, hi = s / 11, min(k / 2, t / leakage)
            if lo >= hi:
                continue
            points = [lo]
            if lo < t < hi:
                points.append(t)
            points.append(hi)
            for left, right in zip(points, points[1:]):
                a = left
                while a < right:
                    b = min(right, a + width)
                    xmax = ((1 - leakage) * b / t if b <= t
                            else 1 - leakage * a / t)
                    if xmax <= 0:
                        a = b
                        continue
                    penalty_lower = 2 * (leakage * a) ** 2 / (k * xmax)
                    bound = composition_entropy_scalar(b) + math.log(2) - penalty_lower
                    if bound > worst[0]:
                        worst = (bound, (h, a, b))
                    a = b
    return worst


def sparse_log_bound(k: int, p: int, N: int, leakage: float) -> float:
    """Appendix Lemma 4 union bound for ranks mu <= s/11, in log space."""
    total = -math.inf
    for h in range(k // p, k, k // p):
        for s in (h, k - h):
            d_min = 10 * s / 11
            if d_min < 10 or leakage < (2 + math.log(d_min)) / d_min:
                return math.inf
            count = max(1, math.floor(s * N / 11))
            log_x = d_min * math.log(math.e / 10)
            log_delta = math.log(15 * d_min) + log_x - math.log1p(-math.exp(log_x))
            term = math.log(count) + log_delta
            hi, lo = max(total, term), min(total, term)
            total = hi + math.log1p(math.exp(lo - hi))
    return total


def screen(k: int, p: int, leakage: float, grid: int) -> tuple[float, tuple[int, int, float, float]]:
    if k % p:
        raise ValueError("p must divide k")
    N = p * p
    x = np.linspace(1 / N, 1, grid)[None, :]
    hx = binary_entropy(x)
    worst = (-math.inf, (0, 0, 0.0, 0.0))

    for h in range(k // p, k, k // p):
        for s in (h, k - h):
            t = k - s
            mu_min = s / 11
            mu = np.linspace(mu_min, k / 2, grid)[:, None]
            # The q-set threshold minus its mean, divided by N.
            excess = t * x + np.maximum(0, mu - t) + leakage * mu - mu * x
            threshold = t * x + np.maximum(0, mu - t) + leakage * mu
            feasible = threshold < mu
            exponent_rate = 2 * np.maximum(excess, 0) ** 2 / (k * x)
            rate = composition_entropy(mu) + hx - exponent_rate
            rate = np.where(feasible, rate, -np.inf)
            idx = np.unravel_index(np.argmax(rate), rate.shape)
            value = float(rate[idx])
            if value > worst[0]:
                worst = (value, (h, s, float(mu[idx[0], 0]), float(x[0, idx[1]])))

    # Sparse ranks: Appendix Lemma 4, invoked at d=s-mu for each rank.
    # Since d >= 10s/11, the lemma's epsilon condition is weakest at that end.
    log_sparse = -math.inf
    for h in range(k // p, k, k // p):
        for s in (h, k - h):
            d_min = 10 * s / 11
            if d_min < 10 or leakage < (2 + math.log(d_min)) / d_min:
                return worst[0], worst[1]
            count = max(1, math.floor(s * N / 11))
            log_x = d_min * math.log(math.e / 10)
            x0 = math.exp(log_x)
            log_delta = math.log(15 * d_min) + log_x - math.log1p(-x0)
            log_sparse = np.logaddexp(log_sparse, math.log(count) + log_delta)

    term_count = 2 * (p - 1) * (k * N // 2) * N
    log_dense = math.log(term_count) + N * worst[0]
    total_log = float(np.logaddexp(log_dense, log_sparse))
    return total_log / math.log(10), worst[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", action="append", default=[], metavar="K:P:E")
    parser.add_argument("--grid", type=int, default=1600)
    parser.add_argument("--interval-width", type=float, default=0.05)
    args = parser.parse_args()
    candidates = args.candidate or ["256:16:0.55", "1024:32:0.45"]
    for spec in candidates:
        k_text, p_text, e_text = spec.split(":")
        k, p, leakage = int(k_text), int(p_text), float(e_text)
        log10_bound, worst = screen(k, p, leakage, args.grid)
        interval_rate, interval_witness = interval_rate_upper(k, p, leakage, args.interval_width)
        N = p * p
        term_count = 2 * (p - 1) * (k * N // 2) * N
        dense_log10 = (math.log(term_count) + N * interval_rate) / math.log(10)
        sparse_log10 = sparse_log_bound(k, p, N, leakage) / math.log(10)
        hi, lo = max(dense_log10, sparse_log10), min(dense_log10, sparse_log10)
        interval_total_log10 = hi + math.log10(1 + 10 ** (lo - hi))
        h, s, mu, q_fraction = worst
        print(
            f"k={k} p={p} N={p*p} E={leakage:g} "
            f"sampled_log10_bound={log10_bound:.6f} "
            f"rate_witness=(cut={h}, orientation_prefix={s}, mu={mu:.4f}, q/N={q_fraction:.4f}) "
            f"interval_rate_upper={interval_rate:.6f} interval_witness={interval_witness} "
            f"dense_log10_upper={dense_log10:.3f} sparse_log10={sparse_log10:.3f} "
            f"interval_total_log10_upper={interval_total_log10:.3f}"
        )


if __name__ == "__main__":
    main()
