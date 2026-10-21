#!/usr/bin/env python3
"""Search simple block-constant witnesses against UB-28's exact suffix.

This checks whether the deterministic width-128,...,1 suffix sorts every
assignment of constant bits to the six width-128 blocks in one central-edge
dependency window. Passing this restricted family does not prove the suffix
sorts arbitrary inputs; a failure is a concrete local obstruction.
"""

import argparse
import importlib.util
from itertools import product
from pathlib import Path
import random


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_backward_window_support", HERE / "ub28-backward-window-support.py"
)
support_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support_module)


def exact_suffix(bits, first_width):
    n = len(bits)
    width = first_width
    while width:
        for offset in (0, 1):
            for shift in range(width):
                for left_block in range(offset, n // width - 1, 2):
                    left_base = left_block * width
                    right_base = (left_block + 1) * width
                    for i in range(width):
                        left = left_base + i
                        right = right_base + ((i + shift) % width)
                        if bits[left] > bits[right]:
                            bits[left], bits[right] = bits[right], bits[left]
        width //= 2
    return bits


def support_before_width(n, edge, first_width):
    blocks = n // 4
    terminal_supports = support_module.terminal.output_supports(blocks)
    child = (set(terminal_supports[edge])
             | set(terminal_supports[edge + 1]))
    width = 8
    while width <= first_width:
        blocks = n // width
        after = {index // 2 for index in child}
        middle = support_module.close_under_pairs(after, blocks, 1)
        before = support_module.close_under_pairs(middle, blocks, 0)
        if width == first_width:
            return before
        child = before
        width *= 2
    raise ValueError("first_width must be a power of two at least 8")


def arranged_profile(n, first_width, blocks, counts, seed):
    rng = random.Random(seed)
    bits = [0] * n
    for block, count in zip(blocks, counts):
        base = block * first_width
        for local in rng.sample(range(first_width), count):
            bits[base + local] = 1
    return bits


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=1024)
    parser.add_argument("--edge", type=int, default=508)
    parser.add_argument("--first-width", type=int, default=128)
    parser.add_argument("--random-profiles", type=int, default=0,
                        help="also sample profiles satisfying the necessary parent-count ordering")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    blocks = sorted(support_before_width(args.n, args.edge,
                                         args.first_width))
    if len(blocks) > 8:
        raise ValueError("restricted exhaustive screen capped at 8 blocks")

    block_constant_witness = None
    for assignment in product((0, 1), repeat=len(blocks)):
        bits = [0] * args.n
        for block, value in zip(blocks, assignment):
            if value:
                bits[block * args.first_width:(block + 1) * args.first_width] = \
                    [1] * args.first_width
        output = exact_suffix(bits, args.first_width)
        if output[args.edge] > output[args.edge + 1]:
            block_constant_witness = assignment
            break
    checked_random = 0
    if args.random_profiles:
        if args.first_width != 128 or blocks != list(range(blocks[0], blocks[0] + 6)):
            raise ValueError("random profile screen expects six consecutive width-128 blocks")
        rng = random.Random(args.seed)
        for _ in range(args.random_profiles):
            counts = [rng.randrange(args.first_width + 1) for _ in blocks]
            if not (sum(counts[:2]) <= sum(counts[2:4])
                    <= sum(counts[4:6])):
                continue
            bits = [0] * args.n
            for block, count in zip(blocks, counts):
                ones = set(rng.sample(range(args.first_width), count))
                base = block * args.first_width
                for local in ones:
                    bits[base + local] = 1
            output = exact_suffix(bits, args.first_width)
            checked_random += 1
            if output[args.edge] > output[args.edge + 1]:
                print(f"FAIL random-profile counts={counts} "
                      f"edge={args.edge} output_pair=10 seed={args.seed}")
                return
    if block_constant_witness is not None:
        print(f"BLOCK_CONSTANT_FAIL assignment={block_constant_witness} "
              f"blocks={blocks} edge={args.edge} output_pair=10")
    else:
        print(f"PASS tested={1 << len(blocks)} block_constant_inputs "
              f"blocks={blocks} edge={args.edge}")

    checked_ordered_profile = 0
    if args.first_width == 128 and len(blocks) == 6:
        ordered_counts = [35, 24, 64, 37, 79, 25]
        if (sum(ordered_counts[:2]) <= sum(ordered_counts[2:4])
                <= sum(ordered_counts[4:6])):
            checked_ordered_profile = 1
            for seed in range(100):
                bits = arranged_profile(args.n, args.first_width, blocks,
                                        ordered_counts, seed)
                output = exact_suffix(bits, args.first_width)
                if output[args.edge] > output[args.edge + 1]:
                    print(f"ORDERED_PROFILE_FAIL counts={ordered_counts} "
                          f"edge={args.edge} output_pair=10 seed={seed}")
                    break
    print(f"fixed_ordered_profile_tested={checked_ordered_profile} "
          f"additional_count_ordered_profiles_checked={checked_random}")


if __name__ == "__main__":
    main()
