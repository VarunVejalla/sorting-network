#!/usr/bin/env python3
"""Outward-rounded interval screen for the AKS dense-rank rate.

This branches over rank mu and overfull-column fraction x. It certifies an
upper bound on the continuous entropy rate when it terminates successfully;
the continuous domain contains every discrete rank/column count. The proof
still depends on the counting and Hoeffding inequalities documented nearby.

Requires mpmath interval arithmetic. This is numerical certification of the
rate bound, not a Lean/kernel-checked theorem.
"""

from __future__ import annotations

import argparse
import heapq
import math

import mpmath as mp

I = mp.iv
I.dps = 40


def iv(x: float | int) -> mp.ctx_iv.ivmpf:
    return I.mpf(x)


def rate_upper(mu_lo: float, mu_hi: float, x_lo: float, x_hi: float,
               t: int, k: int, leakage: str) -> float:
    """Outward upper bound on g(mu)+H(x)-2 Delta^2/(k*x) in one box."""
    ml, mh, xl, xh = map(iv, (mu_lo, mu_hi, x_lo, x_hi))
    e = I.mpf(leakage)
    # g(mu) increases for mu > 0.
    g = (mh + 1) * I.ln(mh + 1) - mh * I.ln(mh)

    # H is maximized at 1/2, otherwise at the endpoint nearest 1/2.
    if x_lo <= 0.5 <= x_hi:
        h = I.ln(iv(2))
    else:
        z = xl if x_lo > 0.5 else xh
        h = -z * I.ln(z) - (1 - z) * I.ln(1 - z)

    # Delta is bilinear on either side of mu=t, so its rectangle minimum
    # occurs at a corner. Clamp only by taking the least lower endpoint.
    deltas = []
    for m in (ml, mh):
        for x in (xl, xh):
            if mu_hi <= t:
                d = (t - m) * x + e * m
            else:
                d = (m - t) * (1 - x) + e * m
            deltas.append(d)
    delta_lo = min(d.a for d in deltas)
    if delta_lo <= 0:
        penalty = iv(0)
    else:
        # x <= x_hi, hence Delta^2/x >= delta_lo^2/x_hi.
        penalty = 2 * delta_lo * delta_lo / (iv(k) * xh)
    result = g + h - penalty
    return float(result.b) + 1e-12  # guard the final conversion to binary64


def feasible_xmax(mu_lo: float, mu_hi: float, t: int, leakage: str) -> float:
    if mu_hi <= t:
        return (1 - float(leakage)) * mu_hi / t + 1e-10
    return 1 - float(leakage) * mu_lo / t + 1e-10


def sparse_probability_upper(k: int, p: int, N: int, leakage: str) -> float:
    """Outward-rounded sum of Appendix Lemma 4 bounds over sparse ranks."""
    E = I.mpf(leakage)
    total = iv(0)
    ratio = I.exp(1) / 10
    for s in range(k // p, k, k // p):
        d = iv(10 * s) / 11
        required = (2 + I.ln(d)) / d
        if required.b > E.a:
            return math.inf
        # For d >= 10, d*(e/10)^d/(1-(e/10)^d) is decreasing:
        # its logarithmic derivative is < 1/d + ln(e/10) < 0.
        x = I.exp(d * I.ln(ratio))
        delta = 15 * d * x / (1 - x)
        ranks = max(1, (s * N) // 11)
        total += ranks * delta
        # Both row orientations are included in the sparse union bound.
        total += ranks * delta
    return float(total.b) + 1e-12


def certify(k: int, p: int, leakage: str, N: int,
            max_boxes: int) -> tuple[float, int, bool]:
    E = float(leakage)
    if k % p or not 0 < E < 1:
        raise ValueError("require p | k and 0 < E < 1")
    step = k // p
    initial: list[tuple[float, float, float, float, int]] = []
    for s in range(step, k, step):
        t = k - s
        low, high = max(0.0, s / 11 - 1e-10), min(k / 2, t / E) + 1e-10
        if low >= high:
            continue
        points = [low]
        if low < t < high:
            points.append(float(t))
        points.append(high)
        for a, b in zip(points, points[1:]):
            xmax = feasible_xmax(a, b, t, leakage)
            if xmax >= 1 / N:
                initial.append((a, b, 1 / N, xmax, t))

    # Max-upper-bound first makes any hard witness visible quickly.
    heap: list[tuple[float, int, tuple[float, float, float, float, int]]] = []
    serial = 0
    max_leaf = -math.inf
    for box in initial:
        u = rate_upper(*box[:4], box[4], k, leakage)
        heapq.heappush(heap, (-u, serial, box))
        serial += 1
    term_count = 2 * (p - 1) * (k * N // 2) * N
    target = -math.log(2 * term_count) / N  # ensures the dense union sum <= 1/2
    processed = 0
    while heap and processed < max_boxes:
        neg_u, _, box = heapq.heappop(heap)
        u = -neg_u
        if u < target:
            max_leaf = max(max_leaf, u)
            processed += 1
            continue
        a, b, x, y, t = box
        # Balance rank and x resolutions; x has much larger local curvature.
        if (b - a) > 8 * (y - x):
            mid = (a + b) / 2
            children = [(a, mid, x, y, t), (mid, b, x, y, t)]
        else:
            mid = (x + y) / 2
            children = [(a, b, x, mid, t), (a, b, mid, y, t)]
        for child in children:
            ca, cb, cx, cy, ct = child
            xmax = feasible_xmax(ca, cb, ct, leakage)
            cy = min(cy, xmax)
            if cx > cy:
                continue
            child = (ca, cb, cx, cy, ct)
            child_u = rate_upper(ca, cb, cx, cy, ct, k, leakage)
            heapq.heappush(heap, (-child_u, serial, child))
            serial += 1
        processed += 1
    if heap:
        max_leaf = max(max_leaf, -heap[0][0])
    return max_leaf, processed, not heap


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", action="append", default=[], metavar="K:P:E")
    parser.add_argument("--N", type=int, default=None, help="column count; defaults to p^2")
    parser.add_argument("--max-boxes", type=int, default=2_000_000)
    args = parser.parse_args()
    candidates = args.candidate or ["256:16:0.55", "1024:32:0.45"]
    for spec in candidates:
        k_s, p_s, e_s = spec.split(":")
        k, p, e = int(k_s), int(p_s), float(e_s)
        N = args.N or p * p
        upper, boxes, done = certify(k, p, e_s, N, args.max_boxes)
        term_count = 2 * (p - 1) * (k * N // 2) * N
        dense_probability = I.exp(I.ln(iv(term_count)) + N * iv(upper))
        sparse_probability = iv(sparse_probability_upper(k, p, N, e_s))
        total_probability = dense_probability + sparse_probability
        print(f"k={k} p={p} N={N} E={e:g} rate_upper={upper:.9f} "
              f"dense_probability_upper={float(dense_probability.b):.9g} "
              f"sparse_probability_upper={float(sparse_probability.b):.9g} "
              f"total_probability_upper={float(total_probability.b):.9g} "
              f"boxes={boxes} complete={done} below_one={'yes' if done and total_probability.b < 1 else 'no'}")


if __name__ == "__main__":
    main()
