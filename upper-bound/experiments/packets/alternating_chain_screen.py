#!/usr/bin/env python3
"""Greedy screen for sorting two increasing chains on alternating wires.

For an A/B support word, legal Boolean inputs are the independent threshold
cuts of the two increasing chains. A comparator (i,j), i<j, reduces the binary
inversion count by exactly (j-i) whenever its endpoints are 1,0. The search
greedily picks a vertex-disjoint layer maximizing that total reduction over
all threshold inputs. This is a deterministic heuristic construction, not an
optimality proof. NumPy is used only to vectorize the finite state updates.
"""

import argparse
import json
from pathlib import Path

import numpy as np


def threshold_states(word):
    sizes = [word.count(0), word.count(1)]
    for cut_a in range(sizes[0] + 1):
        for cut_b in range(sizes[1] + 1):
            cuts = (cut_a, cut_b)
            seen = [0, 0]
            row = []
            for chain in word:
                row.append(int(seen[chain] >= cuts[chain]))
                seen[chain] += 1
            yield row


def greedy_sort(word):
    rows = np.asarray(list(threshold_states(word)), dtype=np.uint8)
    n = len(word)
    ii, jj = np.triu_indices(n, 1)
    layers = []

    while True:
        # Swapping a binary inversion at i<j removes exactly j-i inversions.
        counts = np.sum((rows[:, ii] == 1) & (rows[:, jj] == 0), axis=0)
        scores = counts * (jj - ii)
        order = sorted(range(len(scores)),
                       key=lambda q: (int(scores[q]), int(ii[q]), int(jj[q])),
                       reverse=True)
        used = set()
        layer = []
        for q in order:
            if scores[q] <= 0:
                break
            i, j = int(ii[q]), int(jj[q])
            if i not in used and j not in used:
                layer.append((i, j))
                used.update((i, j))
        if not layer:
            break
        for i, j in layer:
            swap = (rows[:, i] == 1) & (rows[:, j] == 0)
            rows[swap, i], rows[swap, j] = rows[swap, j].copy(), rows[swap, i].copy()
        layers.append(layer)

    sorted_all = all(not np.any((rows[:, i] == 1) & (rows[:, j] == 0))
                     for i in range(n) for j in range(i + 1, n))
    return rows.shape[0], layers, sorted_all


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pairs", type=int, default=64,
                        help="number of A/B wire pairs in the alternating support")
    parser.add_argument("--output", type=Path,
                        help="optional JSON file for the exact comparator layers")
    args = parser.parse_args()
    if args.pairs < 1:
        parser.error("--pairs must be positive")
    word = tuple(i % 2 for i in range(2 * args.pairs))
    state_count, layers, sorted_all = greedy_sort(word)
    result = {
        "support": "AB" * args.pairs,
        "width": 2 * args.pairs,
        "threshold_states": state_count,
        "depth": len(layers),
        "sorts_all_threshold_states": sorted_all,
        "layers": [[[i, j] for i, j in layer] for layer in layers],
        "status": "heuristic finite construction; not an optimality certificate",
    }
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
