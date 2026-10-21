#!/usr/bin/env python3
"""Exhaustively verify the triple-type count for a uniform permutation.

For a fixed word x on h labeled positions and a uniform permutation pi,
record at each t the colors at (pi^{-1}(t), t, pi(t)). The script compares
the enumerated frequency of every triple histogram with the factorial formula
in UB28-JOINT-PATTERN-STATE.md. This is a small-instance check of the exact
counting lemma, not an asymptotic rate proof.
"""

from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial, prod


def triple_histogram(word, permutation):
    inverse = [0] * len(word)
    for source, target in enumerate(permutation):
        inverse[target] = source
    return Counter(
        (word[inverse[t]], word[t], word[permutation[t]])
        for t in range(len(word))
    )


def predicted_multiplicity(word, triples):
    colors = Counter(word)
    incoming = Counter()
    for (previous, current, following), amount in triples.items():
        incoming[previous, current] += amount

    # The edge-color counts agree whether read as predecessor/current pairs
    # or current/successor pairs.
    pair_types = {(a, b) for (a, b, _c) in triples}
    pair_types |= {(b, c) for (_a, b, c) in triples}
    for previous, current in pair_types:
        left = sum(amount for (a, b, _c), amount in triples.items()
                   if (a, b) == (previous, current))
        right = sum(amount for (_p, a, b), amount in triples.items()
                    if (a, b) == (previous, current))
        if left != right:
            return 0

    numerator = prod(factorial(amount) for amount in colors.values())
    denominator = prod(factorial(amount) for amount in triples.values())
    edge_factor = prod(factorial(amount) for amount in incoming.values())
    value, remainder = divmod(numerator * edge_factor, denominator)
    if remainder:
        raise AssertionError((word, triples, "nonintegral formula"))
    return value


def verify_word(word):
    h = len(word)
    observed = Counter(
        tuple(sorted(triple_histogram(word, permutation).items()))
        for permutation in permutations(range(h))
    )
    for encoded, multiplicity in observed.items():
        triples = Counter(dict(encoded))
        predicted = predicted_multiplicity(word, triples)
        if multiplicity != predicted:
            raise AssertionError((word, triples, multiplicity, predicted))


def split_formula_probability(parent_histogram, child_histogram, half):
    parent_types = set(parent_histogram)
    first = Counter()
    second = Counter()
    for (left_type, right_type), amount in child_histogram.items():
        if left_type not in parent_types or right_type not in parent_types:
            return Fraction(0)
        first[left_type] += amount
        second[right_type] += amount
    if any(first[t] + second[t] != parent_histogram[t]
           for t in parent_types):
        return Fraction(0)

    ways = Fraction(prod(factorial(first[t]) for t in parent_types)
                     * prod(factorial(second[t]) for t in parent_types),
                     factorial(half)
                     * prod(factorial(amount)
                            for amount in child_histogram.values()))
    allocation = Fraction(
        prod(comb(parent_histogram[t], first[t]) for t in parent_types),
        comb(2 * half, half),
    )
    return ways * allocation


def verify_split(parent_word):
    h = len(parent_word)
    half = h // 2
    if h != 2 * half:
        return
    parent = Counter(parent_word)
    arrangements = set(permutations(parent_word))
    observed = Counter()
    for arrangement in arrangements:
        child = Counter((arrangement[i], arrangement[i + half])
                        for i in range(half))
        observed[tuple(sorted(child.items()))] += 1
    total = len(arrangements)
    for encoded, count in observed.items():
        child = Counter(dict(encoded))
        expected = split_formula_probability(parent, child, half)
        if Fraction(count, total) != expected:
            raise AssertionError((parent, child, count, total, expected))


def transformed_histogram(triples, left_bit=0, right_bit=1):
    result = Counter()
    for (previous, current, following), amount in triples.items():
        left = min((current >> left_bit) & 1,
                   (following >> right_bit) & 1)
        right = max((previous >> left_bit) & 1,
                    (current >> right_bit) & 1)
        output = current
        output = (output & ~(1 << left_bit)) | (left << left_bit)
        output = (output & ~(1 << right_bit)) | (right << right_bit)
        result[output] += amount
    return tuple(sorted(result.items()))


def verify_matching_output_kernel(word):
    h = len(word)
    observed = Counter()
    triples_seen = set()
    for permutation in permutations(range(h)):
        triples = triple_histogram(word, permutation)
        triples_seen.add(tuple(sorted(triples.items())))
        observed[transformed_histogram(triples)] += 1

    predicted = Counter()
    for encoded in triples_seen:
        triples = Counter(dict(encoded))
        output = transformed_histogram(triples)
        predicted[output] += predicted_multiplicity(word, triples)
    if observed != predicted:
        raise AssertionError((word, observed, predicted))


def main():
    checked_words = 0
    checked_splits = 0
    for h in range(1, 6):
        for alphabet_size in range(1, min(3, h) + 1):
            for word in product(range(alphabet_size), repeat=h):
                verify_word(word)
                checked_words += 1
                if h in (2, 4):
                    verify_split(word)
                    checked_splits += 1
    checked_output_kernels = 0
    for word in product(range(4), repeat=4):
        verify_matching_output_kernel(word)
        checked_output_kernels += 1
    print(f"triple_type_words_checked={checked_words} "
          f"split_words_checked={checked_splits} "
          f"output_kernels_checked={checked_output_kernels}")


if __name__ == "__main__":
    main()
