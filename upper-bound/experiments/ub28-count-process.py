#!/usr/bin/env python3
"""Factorized block-count model for randomized UB-28 schedule screens.

The attempted recurrence uses an exact hypergeometric count transition for
each cross-matching pair, but assumes independent uniform patterns across
blocks at the later split. The width-2 example below disproves that assumption.
Consequently, this script computes a factorized model, not the network
ensemble's expected failure count.
"""
# The independence claim is not valid across a physical block
# split. Matched output blocks can have correlated patterns. For width 2, if
# each input block has one 1, conditioning on output counts (1,1) makes both
# output singletons identical. Thus ``split_blocks`` below is an approximation,
# and this script's full-profile results are not results for the actual network
# ensemble until a joint-pattern invariant is proved.
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb


@lru_cache(None)
def one_round(h, a, b):
    """Distribution of output block counts after one uniform matching."""
    denom = comb(h, a)
    total = a + b
    out = []
    for x in range(max(0, total - h), min(a, b) + 1):
        p = Fraction(comb(b, x) * comb(h - b, a - x), denom)
        if p:
            out.append((x, total - x, p))
    return tuple(out)


@lru_cache(None)
def matching_gadget(h, rounds, a, b):
    """Count transition for `rounds` independent uniform matchings."""
    dist = {(a, b): Fraction(1)}
    for _ in range(rounds):
        nxt = defaultdict(Fraction)
        for (x, y), p in dist.items():
            for u, v, q in one_round(h, x, y):
                nxt[(u, v)] += p * q
        dist = nxt
    return tuple((x, y, p) for (x, y), p in dist.items())


def exact_split(h, a, b):
    total = a + b
    return max(total - h, 0), min(total, h)


def apply_pass(dist, h, offset, rounds, exact_below):
    blocks = len(next(iter(dist)))
    pairs = [(j, j + 1) for j in range(offset, blocks - 1, 2)]
    if not pairs:
        return dist
    result = defaultdict(Fraction)
    for state, p_state in dist.items():
        partial = {state: p_state}
        for i, j in pairs:
            next_partial = defaultdict(Fraction)
            for current, p in partial.items():
                a, b = current[i], current[j]
                if h < exact_below:
                    outcomes = ((exact_split(h, a, b)[0], exact_split(h, a, b)[1], Fraction(1)),)
                else:
                    outcomes = matching_gadget(h, rounds, a, b)
                for x, y, q in outcomes:
                    updated = list(current)
                    updated[i], updated[j] = x, y
                    next_partial[tuple(updated)] += p * q
            partial = next_partial
        for current, p in partial.items():
            result[current] += p
    return result


def split_blocks(dist, old_width):
    """Apply the independent-uniform-pattern split approximation."""
    half = old_width // 2
    result = defaultdict(Fraction)
    for state, p_state in dist.items():
        partial = {(): p_state}
        for count in state:
            denom = comb(old_width, count)
            outcomes = []
            for left in range(max(0, count - half), min(half, count) + 1):
                p = Fraction(comb(half, left) * comb(half, count - left), denom)
                outcomes.append((left, count - left, p))
            next_partial = defaultdict(Fraction)
            for prefix, p in partial.items():
                for left, right, q in outcomes:
                    next_partial[prefix + (left, right)] += p * q
            partial = next_partial
        for state2, p in partial.items():
            result[state2] += p
    return result


def expected_failures(n, rounds, exact_below):
    if n < 2 or n & (n - 1):
        raise ValueError("n must be a power of two >= 2")
    h = n // 2
    dist = {
        (a, b): Fraction(comb(h, a) * comb(h, b), 2**n)
        for a in range(h + 1) for b in range(h + 1)
    }
    while True:
        dist = apply_pass(dist, h, 0, rounds, exact_below)
        dist = apply_pass(dist, h, 1, rounds, exact_below)
        if h == 1:
            break
        dist = split_blocks(dist, h)
        h //= 2
    p_bad = sum(p for state, p in dist.items()
                if any(state[i] > state[i + 1] for i in range(n - 1)))
    return p_bad, p_bad * 2**n, len(dist)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=8)
    parser.add_argument('--rounds', type=int, default=1)
    parser.add_argument('--exact-below', type=int, default=0,
                        help='use a randomized exact splitter when width < this threshold')
    args = parser.parse_args()
    p_bad, expected, states = expected_failures(args.n, args.rounds, args.exact_below)
    print(f'n={args.n} rounds={args.rounds} exact_below={args.exact_below}')
    print(f'P[uniform input fails]= {p_bad}')
    print(f'E[number of failing inputs]= {expected}')
    print(f'final_count_states={states}')


if __name__ == '__main__':
    main()
