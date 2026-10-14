#!/usr/bin/env python3
"""Exhaustive Boolean check of sort-chunks-then-merge-seams cleanup.

The check is combinatorial: it uses Python sorting for chunks and seam merges.
It does not build the corresponding comparator networks or prove the
all-width theorem.
"""

from itertools import product


def odd_even_merge_pairs(run_size):
    """Batcher's odd-even merge network on two sorted contiguous runs."""
    total = 2 * run_size

    def recurse(lo, stride):
        if 2 * stride < total:
            even_network = recurse(lo, 2 * stride)
            odd_network = recurse(lo + stride, 2 * stride)
            cleanup = [
                (i, i + stride)
                for i in range(lo + stride, lo + total - stride, 2 * stride)
            ]
            return even_network + odd_network + cleanup
        return [(lo, lo + stride)]

    return recurse(0, 1)


def apply_comparators(bits, pairs):
    bits = list(bits)
    for i, j in pairs:
        if bits[i] > bits[j]:
            bits[i], bits[j] = bits[j], bits[i]
    return bits


def greedy_depth(pairs):
    wire_time = {}
    for i, j in pairs:
        time = max(wire_time.get(i, 0), wire_time.get(j, 0)) + 1
        wire_time[i] = wire_time[j] = time
    return max(wire_time.values(), default=0)


def is_s_sorted(bits, width):
    true_positions = [i for i, bit in enumerate(bits) if bit]
    false_positions = [i for i, bit in enumerate(bits) if not bit]
    if not true_positions or not false_positions:
        return True
    return max(0, false_positions[-1] - true_positions[0] + 1) <= width


def chunks_for(n, width):
    block = 2 * width
    if n <= block:
        return [n]
    full, rem = divmod(n, block)
    if rem == 0:
        return [block] * full
    return [block] * (full - 1) + [block + rem]


def cleanup(bits, width):
    lengths = chunks_for(len(bits), width)
    chunks = []
    start = 0
    for length in lengths:
        chunks.append(sorted(bits[start : start + length]))
        start += length

    for i in range(len(chunks) - 1):
        left = chunks[i][-width:]
        right = chunks[i + 1][:width]
        seam = apply_comparators(left + right, odd_even_merge_pairs(width))
        chunks[i][-width:] = seam[:width]
        chunks[i + 1][:width] = seam[width:]
    return [bit for chunk in chunks for bit in chunk]


def check(max_n):
    checked = 0
    for q in range(5):
        width = 1 << q
        pairs = odd_even_merge_pairs(width)
        assert greedy_depth(pairs) == q + 1, (width, greedy_depth(pairs))
        for x, y in product(range(width + 1), repeat=2):
            left = [False] * x + [True] * (width - x)
            right = [False] * y + [True] * (width - y)
            merged = apply_comparators(left + right, pairs)
            assert merged == sorted(left + right), (width, x, y, merged)
    for n in range(1, max_n + 1):
        for width in (1, 2, 4, 8, 16):
            for bits in product((False, True), repeat=n):
                if is_s_sorted(bits, width):
                    result = cleanup(list(bits), width)
                    assert result == sorted(bits), (n, width, bits, result)
                    checked += 1
    return checked


if __name__ == "__main__":
    print(f"checked {check(16)} s-sorted Boolean inputs through n=16")
