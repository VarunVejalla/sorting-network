#!/usr/bin/env python3
"""Test a strong scalar-contract relaxation of UB-28.

Each paired-block operation may produce any output whose prefix-one counts do
not exceed the input's (as every ascending comparator network must satisfy),
and whose half-split satisfies the 1/9-halver contract. The simulation picks
the pointwise-largest such output profile. A counterexample refutes this
proof interface, not the actual matching-network schedule.
"""

import argparse


def worst_halver_output(bits, start, width, exact=False, eps_den=9):
    """Pointwise-largest profile allowed by monotonicity and the split bound."""
    old = bits[start : start + 2 * width]
    prefix = [0]
    for bit in old:
        prefix.append(prefix[-1] + bit)
    total = prefix[-1]
    if exact:
        cap = max(0, total - width)
    elif total <= width:
        cap = total // eps_den
    else:
        cap = total - width + (2 * width - total) // eps_den
    left_count = min(prefix[width], cap)
    new_prefix = [0]
    for t in range(1, 2 * width + 1):
        if t <= width:
            q = min(prefix[t], cap)
        else:
            q = min(prefix[t], left_count + (t - width), total)
        new_prefix.append(q)
    out = [new_prefix[t + 1] - new_prefix[t] for t in range(2 * width)]
    assert all(bit in (0, 1) for bit in out)
    assert sum(out) == total
    assert all(new_prefix[t] <= prefix[t] for t in range(2 * width + 1))
    assert sum(out[:width]) <= cap
    if total >= width:
        assert width - sum(out[width:]) <= (2 * width - total) // eps_den
    bits[start : start + 2 * width] = out


def run(n: int, ones: int, eps_den: int = 9):
    # Ones packed left maximize every initial prefix error.
    bits = [1] * ones + [0] * (n - ones)
    for k in reversed(range(n.bit_length() - 1)):
        width = 1 << k
        blocks = n // width
        for shift in (0, 1):
            for left_block in range(shift, blocks - 1, 2):
                left = left_block * width
                # Small-width complete bipartite gadgets give an exact split.
                worst_halver_output(bits, left, width, exact=(width < 200),
                                    eps_den=eps_den)
    return bits


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-log", type=int, default=10)
    parser.add_argument("--epsilon-denominator", type=int, default=9,
                        help="use the scalar 1/q halver contract")
    args = parser.parse_args()
    for logn in range(1, args.max_log + 1):
        n = 1 << logn
        bad = []
        for ones in range(n + 1):
            out = run(n, ones, args.epsilon_denominator)
            expected = [0] * (n - ones) + [1] * ones
            if out != expected:
                inversion = next(i for i in range(n - 1) if out[i] > out[i + 1])
                bad.append((ones, inversion))
        if bad:
            print(f"n={n}, q={args.epsilon_denominator}: scalar-contract counterexample(s) (one-count, inversion) {bad[:8]}")
        else:
            print(f"n={n}, q={args.epsilon_denominator}: every total sorts in this scalar-contract relaxation")


if __name__ == "__main__":
    main()
