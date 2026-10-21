#!/usr/bin/env python3
"""Small exact union-bound screen for profile-conditioned row mixing.

For a fixed column-height profile, each independently scrambled row sends its
marks to a uniformly random subset of columns. This computes the exact
hypergeometric law for a fixed output-column subset, then sums the event
probabilities over all subsets and all column-height profiles in a mass class.
That sum is a union bound, not the exact probability of the union. It is a
finite screen, not a replacement for the reviewed analytic tail or an
all-size proof.
"""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, factorial

from moderate_tail import bound


def row_distribution(n, marked, subset):
    """Integer numerators for a Hypergeom(n, marked, subset) law."""
    lo, hi = max(0, marked - (n - subset)), min(marked, subset)
    out = [0] * (marked + 1)
    for x in range(lo, hi + 1):
        out[x] = comb(subset, x) * comb(n - subset, marked - x)
    return out


def sum_distribution(n, row_marks, subset):
    """Convolve integer hypergeometric numerators and return denominator."""
    dist = [1]
    denominator = 1
    for marked in row_marks:
        pmf = row_distribution(n, marked, subset)
        nxt = [0] * (len(dist) + len(pmf) - 1)
        for i, a in enumerate(dist):
            if a:
                for j, b in enumerate(pmf):
                    if b:
                        nxt[i + j] += a * b
        dist = nxt
        denominator *= comb(n, marked)
    return dist, denominator


def profile_types(rows, columns, max_mass):
    for heights in combinations_with_replacement(range(rows + 1), columns):
        mass = sum(heights)
        if mass > max_mass:
            continue
        multiplicity = factorial(columns)
        for count in Counter(heights).values():
            multiplicity //= factorial(count)
        row_marks = tuple(sum(h > r for h in heights) for r in range(rows))
        yield mass, multiplicity, row_marks


def profile_union_bound(rows, columns, mass_cap, fringe, escape):
    total = Fraction(0)
    for _, multiplicity, row_marks in profile_types(
        rows, columns, mass_cap
    ):
        for subset in range(1, columns + 1):
            dist, row_denominator = sum_distribution(
                columns, row_marks, subset
            )
            threshold = escape + fringe * subset
            tail = sum(dist[threshold + 1:])
            total += Fraction(multiplicity * comb(columns, subset) * tail,
                              row_denominator)
    return min(Fraction(1), 2 * total)  # both reflected orientations


def run(rows=6, columns=8, mass_class=2, eta=Fraction(1, 1000)):
    eta = Fraction(eta)
    max_mass = min(rows * columns, mass_class * columns)
    results = []
    for fringe in range(rows // 2 + 1):
        union_escape = max_mass
        for escape in range(max_mass + 1):
            if profile_union_bound(rows, columns, max_mass, fringe, escape) <= eta:
                union_escape = escape
                break
        # Match this screen's single mass cap and fixed baseline: no union
        # over other i values or baseline rows is included here.
        analytic, theta, p0 = bound(
            mass_class, fringe, columns, 1, baseline_factor=1
        )
        results.append((fringe, union_escape, analytic * columns, theta, p0))
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=6)
    parser.add_argument("--columns", type=int, default=8)
    parser.add_argument("--mass-class", type=int, default=2)
    parser.add_argument("--eta", type=Fraction, default=Fraction(1, 1000))
    args = parser.parse_args()
    print("EXACT PROFILE-UNION-BOUND SCREEN; not a uniform theorem")
    print("fringe  union-bound escape  fixed-cap analytic")
    for fringe, exact_escape, analytic, theta, p0 in run(
        args.rows, args.columns, args.mass_class, args.eta
    ):
        print(f"{fringe:6d}  {exact_escape:12d}  {analytic:17.4f}")
