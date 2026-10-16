#!/usr/bin/env python3
"""Screen a recursive odd/even merge for two unequal sorted runs.

The construction recursively merges the even-index and odd-index subsequences
in parallel, then compares each odd output with the following even output.
This is finite evidence for the proposed unequal-run lemma, not a proof.
"""

from functools import lru_cache
import argparse


@lru_cache(maxsize=None)
def merge_network(m: int, n: int) -> tuple[tuple[int, int], ...]:
    """Return a fixed comparator sequence on m+n wires."""
    if m == 0 or n == 0:
        return ()
    if m == n == 1:
        return ((0, 1),)

    even_wires = tuple(range(0, m, 2)) + tuple(range(m, m + n, 2))
    odd_wires = tuple(range(1, m, 2)) + tuple(range(m + 1, m + n, 2))

    even_net = merge_network((m + 1) // 2, (n + 1) // 2)
    odd_net = merge_network(m // 2, n // 2)

    embedded_even = tuple((even_wires[i], even_wires[j]) for i, j in even_net)
    embedded_odd = tuple((odd_wires[i], odd_wires[j]) for i, j in odd_net)
    correction = tuple((2 * i + 1, 2 * i + 2)
                       for i in range(m // 2 + n // 2)
                       if 2 * i + 2 < m + n)
    return embedded_even + embedded_odd + correction


def depth(network: tuple[tuple[int, int], ...], wires: int) -> int:
    last_layer = [0] * wires
    for i, j in network:
        layer = max(last_layer[i], last_layer[j]) + 1
        last_layer[i] = last_layer[j] = layer
    return max(last_layer, default=0)


def check_thresholds(m: int, n: int) -> bool:
    network = merge_network(m, n)
    for cut_a in range(m + 1):
        for cut_b in range(n + 1):
            values = [int(i >= cut_a) for i in range(m)]
            values.extend(int(i >= cut_b) for i in range(n))
            for i, j in network:
                if values[i] > values[j]:
                    values[i], values[j] = values[j], values[i]
            if values != sorted(values):
                return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-run", type=int, default=16,
                        help="exhaustively test all run lengths up to this size")
    args = parser.parse_args()
    if args.max_run < 1:
        parser.error("--max-run must be positive")

    for m in range(1, args.max_run + 1):
        for n in range(1, args.max_run + 1):
            if not check_thresholds(m, n):
                raise SystemExit(f"counterexample for run lengths {m}+{n}")
    print(f"all threshold cuts pass for run lengths 1..{args.max_run}")

    for q in range(1, 6):
        m = 64 * 2**q
        n = 64 * (2**q - 1)
        net = merge_network(m, n)
        actual_depth = depth(net, m + n)
        target_depth = q + 7
        print(f"{m}+{n} wires: {actual_depth} layers (target {target_depth}); "
              f"{len(net)} comparators")
        if actual_depth != target_depth:
            raise SystemExit("candidate depth missed the 57-layer schedule")


if __name__ == "__main__":
    main()
