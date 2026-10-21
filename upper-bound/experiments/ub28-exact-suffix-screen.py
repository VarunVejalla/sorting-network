#!/usr/bin/env python3
"""Search simple block-constant witnesses against UB-28's exact suffix.

This checks whether the deterministic width-128,...,1 suffix sorts every
assignment of constant bits to the six width-128 blocks in one central-edge
dependency window. Passing this restricted family does not prove the suffix
sorts arbitrary inputs; a failure is a concrete local obstruction.
"""

import argparse
import importlib.util
from math import lgamma, log
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
    # The ordered local witness is embedded between a zero prefix and a one
    # suffix.  In particular, the width-256 block after blocks[4:6] must
    # really be all ones for check_local_prefix_path's ordered-count path.
    suffix_start = (max(blocks) + 1) * first_width
    bits[suffix_start:] = [1] * (n - suffix_start)
    return bits


def preserving_permutation(left, right):
    """Return pi such that each left 1 is paired with a right 1."""
    left_ones = [i for i, bit in enumerate(left) if bit]
    right_ones = [i for i, bit in enumerate(right) if bit]
    if len(left_ones) > len(right_ones):
        raise ValueError("left block has more ones than right block")
    permutation = [-1] * len(left)
    available_right_ones = iter(right_ones)
    for left_slot in left_ones:
        permutation[left_slot] = next(available_right_ones)
    used = set(permutation) - {-1}
    remaining_right = iter(i for i in range(len(right)) if i not in used)
    for left_slot, bit in enumerate(left):
        if not bit:
            permutation[left_slot] = next(remaining_right)
    return permutation


def apply_preserving_pair(left, right, rounds):
    if sum(left) > sum(right):
        raise ValueError("pair counts are not ordered")
    for _ in range(rounds):
        permutation = preserving_permutation(left, right)
        for left_slot, right_slot in enumerate(permutation):
            if left[left_slot] > right[right_slot]:
                left[left_slot], right[right_slot] = (
                    right[right_slot], left[left_slot]
                )


def check_local_prefix_path(seed=0, rounds=70):
    """Realize the ordered witness through the width-512/256 random prefix."""
    n = 1024
    width = 128
    support = list(range(6))
    counts = [35, 24, 64, 37, 79, 25]
    child_bits = arranged_profile(n, width, support, counts, seed)
    blocks = [child_bits[i * width:(i + 1) * width] for i in support]
    parent256 = [blocks[0] + blocks[1], blocks[2] + blocks[3],
                 blocks[4] + blocks[5], child_bits[6 * width:8 * width]]
    assert parent256[3] == [1] * (2 * width)
    parent_counts = [sum(row) for row in parent256]
    assert parent_counts == [59, 101, 104, 256]

    for _ in range(rounds):
        apply_preserving_pair(parent256[0], parent256[1], 1)
        apply_preserving_pair(parent256[2], parent256[3], 1)
    for _ in range(rounds):
        apply_preserving_pair(parent256[1], parent256[2], 1)

    parent512 = [parent256[0] + parent256[1],
                 parent256[2] + parent256[3]]
    assert [sum(row) for row in parent512] == [160, 360]
    for _ in range(rounds):
        apply_preserving_pair(parent512[0], parent512[1], 1)

    bits = parent512[0] + parent512[1]
    output = exact_suffix(bits, 128)
    if output[508] <= output[509]:
        raise AssertionError("constructed local prefix path did not fail")

    log_probability = rounds * (
        lgamma(101 + 1) - lgamma(101 - 59 + 1)
        - lgamma(256 + 1) + lgamma(256 - 59 + 1)
        + lgamma(104 + 1) - lgamma(104 - 101 + 1)
        - lgamma(256 + 1) + lgamma(256 - 101 + 1)
        + lgamma(360 + 1) - lgamma(360 - 160 + 1)
        - lgamma(512 + 1) + lgamma(512 - 160 + 1)
    )
    print(f"LOCAL_PREFIX_PATH_FAIL edge=508 parent256_counts={parent_counts} "
          f"parent512_counts={[sum(row) for row in parent512]} "
          f"log10_matching_probability={log_probability / log(10):.3f}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=1024)
    parser.add_argument("--edge", type=int, default=508)
    parser.add_argument("--first-width", type=int, default=128)
    parser.add_argument("--random-profiles", type=int, default=0,
                        help="also sample profiles satisfying the necessary parent-count ordering")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if args.n == 1024 and args.edge == 508 and args.first_width == 128:
        check_local_prefix_path(args.seed)
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
