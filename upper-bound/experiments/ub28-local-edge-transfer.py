#!/usr/bin/env python3
"""Exact backward local transfer for one annealed UB-28 terminal inversion.

This evaluates the probability that one fixed adjacent output pair is 1,0
under the uniform-input/random-matching ensemble. It propagates the event
backward through the exact tail, hypergeometric block splits, and matching
count kernels. Unlike the full-profile recurrence, its state is only the
count coordinates in that event's backward dependency window.

The transfer averages over a uniform input and the independent random
matching schedule. The resulting law is invariant under independent wire-slot
permutations within each block, so conditional on the count vector the block
patterns are independent uniform subsets. Thus the hypergeometric split and
matching count kernels are exact for the annealed network ensemble. The
remaining asymptotic rate bound is a separate unproved gate.
"""

from fractions import Fraction
from itertools import product
import argparse
import importlib.util
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, HERE / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


count_process = load_module("ub28_count_process", "ub28-count-process.py")
terminal = load_module("ub28_terminal_count_gate", "ub28-terminal-count-gate.py")
window = load_module("ub28_terminal_window_language", "ub28-terminal-window-language.py")


def values_for(width, arity):
    return product(range(width + 1), repeat=arity)


def exact_tail_event(n, edge):
    """Truth table on the exact width-4 count support for output edge."""
    supports = window.output_supports(n // 4)
    support = tuple(sorted(set(supports[edge]) | set(supports[edge + 1])))
    table = {}
    for values in values_for(4, len(support)):
        profile = [0] * (n // 4)
        for index, value in zip(support, values):
            profile[index] = value
        output = terminal.tail_output(profile)
        table[values] = Fraction(output[edge] > output[edge + 1])
    return support, table


def reverse_split(support, table, child_width):
    """Take conditional expectation over a uniform split of each parent."""
    parents = tuple(sorted({index // 2 for index in support}))
    choices = {}
    parent_width = 2 * child_width
    for parent in parents:
        outcomes = {}
        for count in range(parent_width + 1):
            denom = comb(parent_width, child_width)
            outcomes[count] = tuple(
                (
                    left,
                    Fraction(
                        comb(count, left) * comb(parent_width - count, child_width - left),
                        denom,
                    ),
                )
                for left in range(max(0, count - child_width), min(child_width, count) + 1)
            )
        choices[parent] = outcomes

    result = {}
    for parent_values in values_for(parent_width, len(parents)):
        parent_map = dict(zip(parents, parent_values))
        child_values = {}
        total = Fraction(0)

        def visit(position, probability):
            nonlocal total
            if position == len(parents):
                key = tuple(child_values[index] for index in support)
                total += probability * table[key]
                return
            parent = parents[position]
            count = parent_map[parent]
            for left, mass in choices[parent][count]:
                child_values[2 * parent] = left
                child_values[2 * parent + 1] = count - left
                visit(position + 1, probability * mass)

        visit(0, Fraction(1))
        result[parent_values] = total
    return parents, result


def reverse_pass(support, table, blocks, width, offset, rounds):
    """Take conditional expectation through one randomized count pass."""
    support = tuple(support)
    for left in range(offset, blocks - 1, 2):
        right = left + 1
        if left not in support and right not in support:
            continue

        expanded = tuple(sorted(set(support) | {left, right}))
        if expanded != support:
            expanded_table = {}
            for values in values_for(width, len(expanded)):
                value_map = dict(zip(expanded, values))
                old_key = tuple(value_map[index] for index in support)
                expanded_table[values] = table[old_key]
            support, table = expanded, expanded_table

        left_axis = support.index(left)
        right_axis = support.index(right)
        transformed = {}
        for input_values in values_for(width, len(support)):
            a, b = input_values[left_axis], input_values[right_axis]
            expectation = Fraction(0)
            for x, y, mass in count_process.matching_gadget(width, rounds, a, b):
                output_values = list(input_values)
                output_values[left_axis] = x
                output_values[right_axis] = y
                expectation += mass * table[tuple(output_values)]
            transformed[input_values] = expectation
        table = transformed
    return support, table


def edge_probability(n, edge, rounds):
    """Exact P[output[edge]=1 and output[edge+1]=0]."""
    support, table = exact_tail_event(n, edge)
    blocks = n // 4
    width = 4

    # Reverse the width-8 to width-4 split.
    support, table = reverse_split(support, table, width)
    blocks //= 2
    width *= 2

    while True:
        support, table = reverse_pass(support, table, blocks, width, 1, rounds)
        support, table = reverse_pass(support, table, blocks, width, 0, rounds)
        if blocks == 2:
            break
        support, table = reverse_split(support, table, width)
        blocks //= 2
        width *= 2

    assert support == (0, 1)
    return sum(
        table[(a, b)] * Fraction(comb(width, a) * comb(width, b), 2**n)
        for a in range(width + 1)
        for b in range(width + 1)
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--rounds", type=int, default=16)
    parser.add_argument("--edge", type=int, default=None)
    parser.add_argument("--check-full", action="store_true",
                        help="compare the union bound with the full n=32 recurrence")
    args = parser.parse_args()
    if args.n < 32 or args.n & (args.n - 1):
        raise ValueError("n must be a power of two >= 32")
    edges = range(args.n - 1) if args.edge is None else (args.edge,)
    total = Fraction(0)
    for edge in edges:
        probability = edge_probability(args.n, edge, args.rounds)
        total += probability
        print(f"edge={edge} P[bad]={float(probability):.12g}")
    if args.edge is None:
        print(f"union_bound_P[unsorted]={float(total):.12g}")
        print(f"union_bound_E[failing_inputs]={float(total * 2**args.n):.12g}")
    if args.check_full:
        if args.edge is not None or args.n != 32:
            raise ValueError("--check-full requires all edges and n=32")
        exact_failure, exact_expected, _ = count_process.expected_failures(
            args.n, args.rounds, 8
        )
        assert total >= exact_failure
        print(f"full_recurrence_P[unsorted]={float(exact_failure):.12g}")
        print(f"full_recurrence_E[failing_inputs]={float(exact_expected):.12g}")
        print(f"union_bound_slack_inputs={float((total - exact_failure) * 2**args.n):.12g}")


if __name__ == "__main__":
    main()
