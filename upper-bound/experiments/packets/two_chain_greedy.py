#!/usr/bin/env python3
"""Heuristic comparator-layer search for two interleaved sorted chains.

For a fixed A/B support word, legal Boolean inputs are just the (a+1)(b+1)
threshold pairs. Greedy layers maximize total inversion reduction over this
finite family. This is exploratory evidence only, not a universal network
construction or a proof of optimality.
"""
from itertools import combinations
from math import comb


def patterns(n):
    # Distinct support words up to swapping A and B and reversal.
    for a in range(n + 1):
        for apos in combinations(range(n), a):
            w = tuple(int(i in apos) for i in range(n))
            if w <= tuple(1-x for x in w) and w <= w[::-1]:
                yield w


def states(word):
    ranks = [0, 0]
    for c in word:
        ranks[c] += 1
    for cut_a in range(ranks[0] + 1):
        for cut_b in range(ranks[1] + 1):
            cuts = [cut_a, cut_b]
            seen = [0, 0]
            row = []
            for c in word:
                row.append(int(seen[c] >= cuts[c]))
                seen[c] += 1
            yield tuple(row)


def inv(x):
    return sum(x[i] > x[j] for i in range(len(x)) for j in range(i+1, len(x)))


def search(word, limit=100):
    rows = [list(x) for x in states(word)]
    n = len(word)
    edges = list(combinations(range(n), 2))
    history = []
    for _ in range(limit):
        if all(inv(x) == 0 for x in rows):
            return history, True
        scored = []
        for i, j in edges:
            score = sum(x[i] > x[j] for x in rows)
            if score:
                scored.append((score, i, j))
        scored.sort(reverse=True)
        used = set(); layer = []
        for score, i, j in scored:
            if i not in used and j not in used:
                layer.append((i, j)); used.update((i, j))
        if not layer:
            break
        for x in rows:
            y = list(x)
            for i, j in layer:
                if y[i] > y[j]:
                    y[i], y[j] = y[j], y[i]
            x[:] = y
        history.append(tuple(layer))
    return history, all(inv(x) == 0 for x in rows)


def wordstr(w):
    return ''.join('A' if x == 0 else 'B' for x in w)


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--n', type=int, default=12)
    p.add_argument('--show', type=int, default=8)
    args = p.parse_args()
    results = []
    for w in patterns(args.n):
        layers, ok = search(w)
        results.append((len(layers), wordstr(w), ok, len(list(states(w)))))
    results.sort(reverse=True)
    print(f'n={args.n}; support patterns={len(results)}; worst greedy depth={results[0][0]}')
    for r in results[:args.show]:
        print(*r)
