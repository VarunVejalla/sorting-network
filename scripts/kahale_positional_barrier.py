#!/usr/bin/env python3
"""Construct positional schedules for the scalar Kahale height relaxation.

A block (start, count, height) is paired across its two halves. Comparators
are (start+k, start+ceil(count/2)+k), 0 <= k < floor(count/2).
The interval description is exact even when the network is too big to expand.
This establishes height requirements, not sorting or approximate selection.
"""

import argparse
import json
import math
import random

from kahale_height_barrier import fib


def advance(blocks):
    result = []
    for height, count in blocks:
        for new_height, new_count in ((height, (count + 1) // 2),
                                      (height + 1, count // 2)):
            if not new_count:
                continue
            if result and result[-1][0] == new_height:
                result[-1] = (new_height, result[-1][1] + new_count)
            else:
                result.append((new_height, new_count))
    return result


def layers(n, d):
    blocks = [(0, n)] if n else []
    for _ in range(d):
        yield blocks
        blocks = advance(blocks)


def expand_layer(blocks):
    start = 0
    for _, count in blocks:
        half = (count + 1) // 2
        for k in range(count // 2):
            yield start + k, start + half + k
        start += count


def investigate(d):
    n = (1 << d) // ((d + 1) * fib(d + 1))
    blocks = [(0, n)] if n else []
    comparator_count = 0
    worst_excess = 0
    for t in range(d + 1):
        if sum(count for _, count in blocks) != n:
            raise ArithmeticError("wire count changed")
        if any(a[0] >= b[0] for a, b in zip(blocks, blocks[1:])):
            raise ArithmeticError("height blocks are not ordered")
        s = d - t
        low_prefix = sum(count for h, count in blocks if h <= s)
        # Sorted blocks make this the *position* of the first height > s.
        worst_excess = max(worst_excess, low_prefix - (1 << (s + 1)))
        if worst_excess:
            raise ArithmeticError("positional prefix requirement failed")
        if t < d:
            comparator_count += sum(count // 2 for _, count in blocks)
            blocks = advance(blocks)
    return {
        "depth": d, "arity_bits": n.bit_length(),
        "depth_over_log2_arity": d / math.log2(n) if n > 1 else None,
        "all_positional_prefix_requirements_pass": True,
        "comparators": comparator_count,
        "scope": "actual schedule with scalar certificate heights; no sorting claim",
    }


def find_unsorted_input(d, trials, seed):
    n = (1 << d) // ((d + 1) * fib(d + 1))
    if n > 10000:
        raise ValueError("explicit exploration is limited to 10000 wires")
    schedule = [list(expand_layer(blocks)) for blocks in layers(n, d)]
    rng = random.Random(seed)
    for trial in range(trials):
        original = [rng.randrange(2) for _ in range(n)]
        values = original[:]
        for layer in schedule:
            for i, j in layer:
                values[i], values[j] = min(values[i], values[j]), max(values[i], values[j])
        inversion = next((i for i in range(n - 1) if values[i] > values[i + 1]), None)
        if inversion is not None:
            return {"depth": d, "arity": n, "trial": trial, "seed": seed,
                    "input": "".join(map(str, original)),
                    "output": "".join(map(str, values)), "inversion_at": inversion}
    return {"depth": d, "arity": n, "trials": trials,
            "unsorted_input_found": False, "scope": "finite exploration, not a proof of sorting"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depth", nargs="*", type=int, default=[64, 128, 256, 512])
    parser.add_argument("--explore-depth", type=int)
    parser.add_argument("--trials", type=int, default=64)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if any(d < 0 for d in args.depth) or (args.explore_depth is not None and args.explore_depth < 0):
        parser.error("depth must be nonnegative")
    for d in args.depth:
        print(json.dumps(investigate(d)))
    if args.explore_depth is not None:
        print(json.dumps(find_unsorted_input(args.explore_depth, args.trials, args.seed)))


if __name__ == "__main__":
    main()
