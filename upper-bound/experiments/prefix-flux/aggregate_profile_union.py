#!/usr/bin/env python3
"""Exact small-instance union bound for multi-round aggregate defects.

States are histograms of column heights. A row scramble independently chooses
a uniform subset of the prescribed size in every row; the following column
sort turns the resulting matrix into a new height histogram. We sum the exact
bad probabilities over every *labeled* initial height profile. `--rounds`
counts scramble/column-sort rounds after the initial column sort.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, exp, factorial, log


def histograms(rows, columns):
    """All histograms of `columns` heights in {0,...,rows}."""
    def rec(height, left, prefix):
        if height == rows:
            yield tuple(prefix + [left])
            return
        for count in range(left + 1):
            yield from rec(height + 1, left - count, prefix + [count])
    yield from rec(0, columns, [])


def row_counts(hist):
    return tuple(sum(hist[h] for h in range(r + 1, len(hist)))
                 for r in range(len(hist) - 1))


def labeled_multiplicity(hist):
    columns = sum(hist)
    out = factorial(columns)
    for count in hist:
        out //= factorial(count)
    return out


@lru_cache(None)
def transition(rows, columns, counts):
    """Integer outcome counts for one random row-scramble/column-sort."""
    choices = [tuple(combinations(range(columns), x)) for x in counts]
    outcomes = Counter()
    heights = [0] * columns

    def visit(row):
        if row == rows:
            hist = [0] * (rows + 1)
            for height in heights:
                hist[height] += 1
            outcomes[tuple(hist)] += 1
            return
        for subset in choices[row]:
            for col in subset:
                heights[col] += 1
            visit(row + 1)
            for col in subset:
                heights[col] -= 1

    visit(0)
    total = 1
    for x in counts:
        total *= comb(columns, x)
    assert sum(outcomes.values()) == total
    return tuple(outcomes.items()), total


def area(hist):
    columns = sum(hist)
    total = sum(height * count for height, count in enumerate(hist))
    q, remainder = divmod(total, columns)
    balanced = ((columns - remainder) * q * q
                + remainder * (q + 1) * (q + 1))
    square_sum = sum(height * height * count
                     for height, count in enumerate(hist))
    return (square_sum - balanced) // 2


def expected_one_round_area(hist):
    """Exact first moment after one independent row scramble and column sort.

    If c_r is the number of live columns in input row r and M is the total
    number of ones, then E[sum_j (H_j-M/n)^2] is
    sum_r c_r(n-c_r)/n. Subtract the unavoidable integer-mean correction
    before dividing by two to obtain the area statistic used by this screen.
    """
    columns = sum(hist)
    counts = row_counts(hist)
    total = sum(height * multiplicity
                for height, multiplicity in enumerate(hist))
    remainder = total % columns
    variance = Fraction(sum(c * (columns - c) for c in counts), columns)
    rounding = Fraction(remainder * (columns - remainder), columns)
    return (variance - rounding) / 2


def na_tail_bound(hist, threshold, lam):
    """One-round NA/Chernoff upper bound for P(area >= threshold | hist)."""
    if lam <= 0:
        raise ValueError('lam must be positive')
    columns = sum(hist)
    counts = row_counts(hist)
    total_ones = sum(height * multiplicity
                     for height, multiplicity in enumerate(hist))
    mean = total_ones / columns
    remainder = total_ones % columns
    rho = remainder * (columns - remainder) / columns

    # Marginal height is Poisson-binomial with probabilities c_r / columns.
    pmf = [1.0]
    for count in counts:
        p = count / columns
        updated = [0.0] * (len(pmf) + 1)
        for height, probability in enumerate(pmf):
            updated[height] += probability * (1 - p)
            updated[height + 1] += probability * p
        pmf = updated
    upper = sum(p * exp(2 * lam * max(height - mean, 0) ** 2)
                for height, p in enumerate(pmf))
    lower = sum(p * exp(2 * lam * max(mean - height, 0) ** 2)
                for height, p in enumerate(pmf))
    log_bound = (-lam * (2 * threshold + rho)
                 + columns / 2 * (log(upper) + log(lower)))
    return min(1.0, exp(log_bound))


def audit_na_tail_bound(rows, columns, thresholds=(1, 2), lam=0.02):
    """Compare the NA/Chernoff bound with exact one-round tails on a toy size."""
    comparisons = 0
    for initial in histograms(rows, columns):
        outcomes, denominator = transition(
            rows, columns, row_counts(initial)
        )
        for threshold in thresholds:
            exact = sum((Fraction(count, denominator)
                         for final, count in outcomes
                         if area(final) >= threshold), Fraction(0))
            bound = na_tail_bound(initial, threshold, lam)
            if float(exact) > bound + 1e-12:
                raise AssertionError((initial, threshold, float(exact), bound))
            comparisons += 1
    return comparisons


def screen(rows, columns, rounds=2):
    if rounds < 1:
        raise ValueError('rounds must be positive')
    states = tuple(histograms(rows, columns))
    trans = {state: transition(rows, columns, row_counts(state))
             for state in states}
    for state, (outcomes, denominator) in trans.items():
        exact_mean = sum((Fraction(count, denominator) * area(outcome)
                          for outcome, count in outcomes), Fraction(0))
        assert exact_mean == expected_one_round_area(state), (
            state, exact_mean, expected_one_round_area(state))
    final_area_mass = Counter()
    for initial in states:
        multiplicity = labeled_multiplicity(initial)
        profile_mass = {initial: Fraction(1)}
        for _ in range(rounds):
            next_mass = Counter()
            for profile, probability in profile_mass.items():
                outcomes, denominator = trans[profile]
                for outcome, count in outcomes:
                    next_mass[outcome] += probability * Fraction(count, denominator)
            profile_mass = next_mass
        for final, probability in profile_mass.items():
            final_area_mass[area(final)] += multiplicity * probability

    tail = Fraction()
    threshold = None
    total_profiles = (rows + 1) ** columns
    for value in sorted(final_area_mass, reverse=True):
        tail += final_area_mass[value]
        if tail >= 1:
            threshold = value + 1
            break
    if threshold is None:
        threshold = 0
    return dict(rows=rows, columns=columns, rounds=rounds,
                height_histogram_states=len(states),
                labeled_profiles=total_profiles,
                min_strict_area_threshold_with_union_lt1=threshold,
                threshold_fraction=threshold / (rows * columns),
                union_bound_at_threshold=sum(
                    probability for value, probability in final_area_mass.items()
                    if value >= threshold
                ))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=3)
    parser.add_argument("--columns", type=int, default=6)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--audit-na-tail", action="store_true",
                        help="compare the one-round NA tail bound with exact toy tails")
    parser.add_argument("--lambda", dest="lam", type=float, default=0.02)
    args = parser.parse_args()
    if args.audit_na_tail:
        print(dict(rows=args.rows, columns=args.columns,
                   exact_tail_comparisons=audit_na_tail_bound(
                       args.rows, args.columns, lam=args.lam)))
    else:
        print(screen(args.rows, args.columns, args.rounds))
