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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=1024)
    parser.add_argument("--edge", type=int, default=508)
    parser.add_argument("--first-width", type=int, default=128)
    args = parser.parse_args()
    blocks = sorted(support_before_width(args.n, args.edge,
                                         args.first_width))
    if len(blocks) > 8:
        raise ValueError("restricted exhaustive screen capped at 8 blocks")

    for assignment in product((0, 1), repeat=len(blocks)):
        bits = [0] * args.n
        for block, value in zip(blocks, assignment):
            if value:
                bits[block * args.first_width:(block + 1) * args.first_width] = \
                    [1] * args.first_width
        output = exact_suffix(bits, args.first_width)
        if output[args.edge] > output[args.edge + 1]:
            print(f"FAIL blocks={blocks} assignment={assignment} "
                  f"edge={args.edge} output_pair="
                  f"{output[args.edge]}{output[args.edge + 1]}")
            return
    print(f"PASS tested={1 << len(blocks)} block_constant_inputs "
          f"blocks={blocks} edge={args.edge}")


if __name__ == "__main__":
    main()
