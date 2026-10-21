#!/usr/bin/env python3
"""Check the backward support width for one terminal UB-28 inversion.

The exact width-4/2/1 tail maps the incoming width-4 count profile to the
final bits. A single bad adjacent output pair depends on a bounded interval
of width-4 counts. Going backward through a split maps child index j to its
parent floor(j/2). Going backward through a matching pass closes the support
under its disjoint adjacent pairs. This script checks the resulting support
bound for all output edges at finite powers of two.

It checks dependency locality only; it does not estimate the probability of
the bad event.
"""

import argparse
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "ub28_terminal_window_language", HERE / "ub28-terminal-window-language.py"
)
terminal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(terminal)


def close_under_pairs(support, blocks, offset):
    """Preimage support for one count pass on adjacent block pairs."""
    result = set(support)
    for left in range(offset, blocks - 1, 2):
        if left in result or left + 1 in result:
            result.update((left, left + 1))
    return result


def reverse_random_prefix(n):
    """Return the maximum support size at the exact tail and each scale."""
    if n < 32 or n & (n - 1):
        raise ValueError("n must be a power of two at least 32")

    width4_blocks = n // 4
    output_supports = terminal.output_supports(width4_blocks)
    edge_supports = [
        set(output_supports[i]) | set(output_supports[i + 1])
        for i in range(n - 1)
    ]
    maxima = [(4, max(map(len, edge_supports)))]

    # Reverse the width-8-to-width-4 uniform split.
    blocks = width4_blocks // 2
    edge_supports = [{index // 2 for index in support} for support in edge_supports]
    width = 8

    while True:
        # The forward pass order is offsets 0 then 1, hence reverse order 1,0.
        edge_supports = [
            close_under_pairs(support, blocks, 1) for support in edge_supports
        ]
        edge_supports = [
            close_under_pairs(support, blocks, 0) for support in edge_supports
        ]
        maxima.append((width, max(map(len, edge_supports))))
        if blocks == 2:
            break
        blocks //= 2
        edge_supports = [
            {index // 2 for index in support} for support in edge_supports
        ]
        width *= 2

    return maxima


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-log", type=int, default=12)
    args = parser.parse_args()
    if args.max_log < 5:
        raise ValueError("--max-log must be at least 5")

    for log_n in range(5, args.max_log + 1):
        n = 1 << log_n
        maxima = reverse_random_prefix(n)
        if any(size > 6 for _, size in maxima):
            raise AssertionError((n, maxima))
        print(f"n={n} max_support_by_width={maxima}")


if __name__ == "__main__":
    main()
