#!/usr/bin/env python3
"""Check the two-grid band-repair lemma for threshold-local Boolean words.

Each pass independently sorts fixed 64-wire segments in descending Boolean
order. The second grid is shifted by 32. This is a finite diagnostic for the
proposed fixed comparator-network macro, not a global D2 proof.
"""
import argparse
import random


def sort_segments(word, starts, width=64):
    out = list(word)
    for start in starts:
        end = start + width
        if end <= len(word):
            ones = sum(word[start:end])
            out[start:end] = [1] * ones + [0] * (width - ones)
    return out


def repair(word, width=64):
    n = len(word)
    if n % width != 0:
        raise ValueError('the two-grid lemma requires height divisible by segment width')
    first = sort_segments(word, range(0, n - width + 1, width), width)
    second = sort_segments(first, range(width // 2, n - width + 1, width), width)
    return second


def is_sorted_descending(word):
    return all(word[i] >= word[i + 1] for i in range(len(word) - 1))


def repair_ascending(word, width=64):
    # Complementing a descending comparator network reverses its order.
    return [1 - bit for bit in repair([1 - bit for bit in word], width)]


def is_sorted_ascending(word):
    return all(word[i] <= word[i + 1] for i in range(len(word) - 1))


def threshold_word(n, lo, hi, middle):
    return [1 if i < lo else 0 if i >= hi else middle[i - lo]
            for i in range(n)]


def exhaustive_small(n, max_width):
    checked = 0
    for lo in range(n + 1):
        for width in range(max_width + 1):
            hi = lo + width
            if hi > n:
                continue
            for mask in range(1 << width):
                middle = [(mask >> j) & 1 for j in range(width)]
                word = threshold_word(n, lo, hi, middle)
                assert is_sorted_descending(repair(word)), (n, lo, hi, middle)
                assert is_sorted_ascending(repair_ascending(
                    [1 - bit for bit in word])), (n, lo, hi, middle)
                checked += 1
    return checked


def random_wide(n, width, trials, seed):
    rng = random.Random(seed)
    for _ in range(trials):
        dirty = rng.randrange(width + 1)
        lo = rng.randrange(n - dirty + 1)
        middle = [rng.randrange(2) for _ in range(dirty)]
        word = threshold_word(n, lo, lo + dirty, middle)
        assert is_sorted_descending(repair(word)), (n, lo, dirty, middle)
        assert is_sorted_ascending(repair_ascending(
            [1 - bit for bit in word])), (n, lo, dirty, middle)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=256)
    ap.add_argument('--exhaustive-width', type=int, default=8)
    ap.add_argument('--wide-width', type=int, default=32)
    ap.add_argument('--trials', type=int, default=100000)
    ap.add_argument('--seed', type=int, default=0)
    args = ap.parse_args()
    checked = exhaustive_small(args.n, args.exhaustive_width)
    random_wide(args.n, args.wide_width, args.trials, args.seed)
    print({'segments': '64-aligned then 32-shifted',
           'exhaustive_width': args.exhaustive_width,
           'exhaustive_cases': checked,
           'random_width_bound': args.wide_width,
           'random_cases': args.trials,
           'status': 'passed'})


if __name__ == '__main__':
    main()
