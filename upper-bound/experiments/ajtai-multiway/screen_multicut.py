#!/usr/bin/env python3
"""Screen a crude union bound for the AKS 1992 depth-two k-network.

This is numerical research tooling, not a proof assistant artifact. It uses
the hypergeometric Hoeffding tail from Appendix 4.1 of Ajtai--Komlos--Szemeredi
and an intentionally coarse count of monotone matrices by total weight. For
sparse ranks it also applies Appendix Lemma 4 separately at each target cut.
"""

from __future__ import annotations

import argparse
import math


def log_add(x: float, y: float) -> float:
    if x == -math.inf:
        return y
    if y == -math.inf:
        return x
    hi, lo = max(x, y), min(x, y)
    return hi + math.log1p(math.exp(lo - hi))


def log_binomial(n: int, r: int) -> float:
    if r < 0 or r > n:
        return -math.inf
    return math.lgamma(n + 1) - math.lgamma(r + 1) - math.lgamma(n - r + 1)


def log_composition_count(m: int, columns: int) -> float:
    """Upper-bound monotone matrices of weight m by weak compositions."""
    return log_binomial(m + columns - 1, columns - 1)


def log_failure_bound(k: int, p: int, columns: int, leakage: float) -> float:
    """Log of the union bound over cuts, orientations, ranks, and overfull sets.

    For a cut parameter t (h for misplaced zeros, k-h for misplaced ones),
    let q be the number of overfull output columns. The event that leakage
    exceeds E*m implies that a particular q-set contains more than
      t*q + max(0, m-t*columns) + E*m
    ones. Its mean is q*m/columns. Appendix 4.1 bounds its upper tail by
    exp(-2*delta^2/(k*q)); we union-bound over q-sets and input matrices.

    Inputs with m <= k*columns/2 suffice because the two orientations are
    both included at each cut. For sparse ranks we use Appendix Lemma 4 with
    d=s-m/columns, so its line is exactly the target cut s; remaining ranks
    use the coarse input count C(m+columns-1, columns-1), without the paper's
    equivalence-class refinement.
    """
    if k % p:
        raise ValueError("p must divide k so all requested cuts are row cuts")
    if not 0 <= leakage:
        raise ValueError("leakage must be nonnegative")

    cuts = [j * k // p for j in range(1, p)]
    log_total = -math.inf
    max_weight = k * columns // 2

    for h in cuts:
        # Treat ones leaking across the h-prefix and zeros leaking across its
        # complementary suffix as prefix problems of sizes h and k-h.
        for s in (h, k - h):
            t = k - s
            for m in range(1, max_weight + 1):
                log_inputs = log_composition_count(m, columns)
                mu = m / columns

                # Apply Appendix Lemma 4 at this rank with d=s-mu, so its
                # line mu+d is exactly the target cut s. Its rank condition
                # mu <= d/10 is equivalent to mu <= s/11.
                d = s - mu
                if (
                    d >= 10
                    and mu <= d / 10
                    and leakage >= (2 + math.log(d)) / d
                ):
                    log_x = d * math.log(math.e / 10)
                    x = math.exp(log_x) if log_x > -745 else 0.0
                    log_delta = math.log(15 * d) + log_x - math.log1p(-x)
                    log_total = log_add(log_total, log_delta)
                    continue

                base = max(0, m - t * columns)
                log_overfull_union = -math.inf

                for q in range(1, columns + 1):
                    threshold = t * q + base + leakage * m
                    # The selected q columns cannot contain more than m ones.
                    if threshold >= m:
                        continue
                    delta = threshold - mu * q
                    exponent = 2 * max(0.0, delta) ** 2 / (k * q)
                    log_term = log_binomial(columns, q) - exponent
                    log_overfull_union = log_add(log_overfull_union, log_term)

                if log_overfull_union != -math.inf:
                    log_total = log_add(log_total, log_inputs + log_overfull_union)
    return log_total


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--columns", type=int, default=23, help="N in the k by N matrix")
    parser.add_argument(
        "--candidate", action="append", default=[], metavar="K:P:E",
        help="candidate k:p:leakage tuple; repeatable",
    )
    args = parser.parse_args()
    candidates = args.candidate or ["256:16:0.55", "1024:32:0.45"]

    for spec in candidates:
        k_text, p_text, e_text = spec.split(":")
        k, p, leakage = int(k_text), int(p_text), float(e_text)
        log_bound = log_failure_bound(k, p, args.columns, leakage)
        log10_bound = log_bound / math.log(10)
        print(
            f"k={k} p={p} N={args.columns} E={leakage:g} "
            f"log10_failure_bound={log10_bound:.6f} "
            f"screen_below_one={'yes' if log_bound < 0 else 'no'}"
        )


if __name__ == "__main__":
    main()
