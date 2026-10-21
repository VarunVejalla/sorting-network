#!/usr/bin/env python3
"""Exhaustive small-n screen for the UB-28 descending dyadic schedule.

This is only a finite diagnostic.  Each pass pairs adjacent blocks of size
2^k, with the odd pass shifted by one block.  Every round uses an independent
uniform random perfect cross-matching for each active block pair; comparators
send min to the lower-index block.  Scales run from largest to smallest.
"""

import argparse
import random


def schedule(n: int, d: int, rng: random.Random):
    """Yield comparator layers for one randomized candidate network."""
    levels = n.bit_length() - 1
    for k in reversed(range(levels)):
        width = 1 << k
        for shift in (0, 1):
            # The shifted pass pairs block indices (shift,shift+1), etc.
            pairs = [(j, j + 1) for j in range(shift, n // width - 1, 2)]
            for _ in range(d):
                layer = []
                for left_block, right_block in pairs:
                    left = left_block * width
                    right = right_block * width
                    perm = list(range(width))
                    rng.shuffle(perm)
                    layer.extend((left + i, right + perm[i]) for i in range(width))
                yield layer


def all_inputs_sorted(n: int, layers):
    cases = 1 << n
    wire = [sum(1 << x for x in range(cases) if (x >> i) & 1)
            for i in range(n)]
    for layer in layers:
        for i, j in layer:
            lo, hi = wire[i], wire[j]
            wire[i], wire[j] = lo & hi, lo | hi
    for i in range(n - 1):
        bad = wire[i] & ~wire[i + 1]
        if bad:
            x = (bad & -bad).bit_length() - 1
            return False, x, i
    return True, None, None


def forcing_leaves(n: int, layers, input_word: int, output: int, value: int):
    """Extract one valid single-output forcing certificate backwards."""
    before = []
    wire = [(input_word >> i) & 1 for i in range(n)]
    for layer in layers:
        before.append(wire[:])
        for i, j in layer:
            lo, hi = wire[i], wire[j]
            wire[i], wire[j] = lo & hi, lo | hi
    assert wire[output] == value
    demand = {output: value}
    for t in reversed(range(len(layers))):
        prev = demand.copy()
        for i, j in layers[t]:
            di, dj = demand.get(i), demand.get(j)
            if di is None and dj is None:
                continue
            prev.pop(i, None)
            prev.pop(j, None)
            a, b = before[t][i], before[t][j]
            if di is not None:  # lower output is AND
                if di:
                    additions = ((i, 1), (j, 1))
                else:
                    additions = ((i if not a else j, 0),)
                for w, bit in additions:
                    assert w not in prev or prev[w] == bit
                    prev[w] = bit
            if dj is not None:  # upper output is OR
                if dj:
                    additions = ((i if a else j, 1),)
                else:
                    additions = ((i, 0), (j, 0))
                for w, bit in additions:
                    assert w not in prev or prev[w] == bit
                    prev[w] = bit
        demand = prev
    assert all(((input_word >> w) & 1) == bit for w, bit in demand.items())
    return {w for w, bit in demand.items() if bit}, {w for w, bit in demand.items() if not bit}


def check_witness(n: int, layers, word: int, inversion: int):
    ones, _ = forcing_leaves(n, layers, word, inversion, 1)
    _, zeros = forcing_leaves(n, layers, word, inversion + 1, 0)
    assert ones.isdisjoint(zeros)
    return ones, zeros


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--seeds", type=int, default=10)
    ap.add_argument("--witness", action="store_true", help="show a paired forcing witness for each failure")
    args = ap.parse_args()
    if args.n < 2 or args.n & (args.n - 1):
        ap.error("n must be a power of two >= 2")
    for seed in range(args.seeds):
        layers = list(schedule(args.n, args.d, random.Random(seed)))
        ok, x, i = all_inputs_sorted(args.n, layers)
        extra = ""
        if not ok:
            extra = f" witness={x:0{args.n}b} inversion={i},{i+1}"
            if args.witness:
                ones, zeros = check_witness(args.n, layers, x, i)
                extra += f" forced_ones={sorted(ones)} forced_zeros={sorted(zeros)}"
        print(f"seed={seed} sorted={ok}" + (extra if not ok else ""))


if __name__ == "__main__":
    main()
