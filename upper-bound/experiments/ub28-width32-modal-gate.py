#!/usr/bin/env python3
"""Find a feasible modal count path for the width-32 UB-28 variant.

This is a one-path lower screen for the expected number of failing inputs,
not a proof that no deterministic sorting network exists. The path follows
hypergeometric modes through the actual top-relative matching schedule and
ends at the width-32 boundary predicate (left_count > 0, right_count < 32).
"""

import argparse
import math


def matching_mode(width, left, right):
    x = ((left + 1) * (right + 1)) // (width + 2)
    return min(left, right, max(0, left + right - width, x))


def split_mode(parent_width, count):
    child_width = parent_width // 2
    return min(child_width, (count + 1) // 2)


def schedule_ops(log_n, terminal_edge, high, low):
    n = 1 << log_n
    blocks, width = n // 32, 32
    support = [terminal_edge, terminal_edge + 1]
    reverse = []
    while blocks > 2:
        for parent in sorted({i // 2 for i in support}):
            children = tuple(i for i in (2 * parent, 2 * parent + 1)
                             if i in support)
            before = list(support)
            after = sorted((set(support) - set(children)) | {parent})
            reverse.append(("split", after, before, parent, width * 2, None))
            support = after
        blocks //= 2
        width *= 2
        distance_from_top = blocks.bit_length() - 2
        rounds = high if distance_from_top % 2 == 0 else low
        for offset in (1, 0):
            lefts = set()
            for index in support:
                left = index if (index - offset) % 2 == 0 else index - 1
                if offset <= left and left + 1 < blocks:
                    lefts.add(left)
            for left in sorted(lefts):
                right = left + 1
                before = list(support)
                after = sorted(set(support) | {left, right})
                reverse.append(("match", after, before, left, width,
                                (right, rounds)))
                support = after
    if support != [0, 1]:
        raise AssertionError((support, n, terminal_edge))
    return list(reversed(reverse))


def modal_path(log_n, high, low, edge=None):
    n = 1 << log_n
    blocks = n // 32
    edge = blocks // 2 if edge is None else edge
    ops = schedule_ops(log_n, edge, high, low)
    support = [0, 1]
    profile = [n // 4, n // 4]
    path_logp_lower = 0.0
    matching_events = split_events = 0
    scale_trace = []

    for op_index, (kind, before, after, index, width, extra) in enumerate(ops):
        if support != before:
            raise AssertionError((support, before, kind, index))
        values = dict(zip(support, profile))
        if kind == "match":
            right, rounds = extra
            a, b = values[index], values[right]
            for _ in range(rounds):
                x = matching_mode(width, a, b)
                # A modal outcome among at most width+1 outcomes has
                # probability at least 1/(width+1).
                path_logp_lower -= math.log(width + 1)
                matching_events += 1
                a, b = x, a + b - x
            values[index], values[right] = a, b
        else:
            count = values[index]
            child_width = width // 2
            left_count = split_mode(width, count)
            path_logp_lower -= math.log(width + 1)
            split_events += 1
            values.pop(index)
            left_child, right_child = 2 * index, 2 * index + 1
            if left_child in after:
                values[left_child] = left_count
            if right_child in after:
                values[right_child] = count - left_count
        profile = [values[i] for i in after]
        support = after
        if (kind == "split" and
                (op_index + 1 == len(ops)
                 or ops[op_index + 1][0] != "split"
                 or ops[op_index + 1][4] != width)):
            scale_trace.append((width // 2, tuple(support), tuple(profile)))

    counts = dict(zip(support, profile))
    left, right = counts[edge], counts[edge + 1]
    bad = left > 0 and right < 32
    # C(N,N/2) >= 2^N/(N+1), since it is the largest of N+1
    # binomial coefficients summing to 2^N. Apply this to both half-blocks.
    penalty = -path_logp_lower
    positivity_threshold = (
        2 * math.log(n // 2 + 1) + penalty
    ) / math.log(2.0)
    log_expected_lower = (
        n * math.log(2.0) - 2 * math.log(n // 2 + 1) - penalty
        if log_n <= 1023 else None
    )
    return {
        "n": n, "edge": edge, "left": left, "right": right,
        "bad": bad, "path_logp_lower": path_logp_lower,
        "positivity_threshold": positivity_threshold,
        "log_expected_lower": log_expected_lower,
        "expected_failures_lower_exceeds_one": n > positivity_threshold,
        "matching_events": matching_events, "split_events": split_events,
        "scale_trace": scale_trace,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=20)
    parser.add_argument("--high", type=int, default=223)
    parser.add_argument("--low", type=int, default=27)
    parser.add_argument("--edge", type=int)
    parser.add_argument("--trace", action="store_true",
                        help="print supported count profiles after each split scale")
    args = parser.parse_args()
    if args.log_n < 7:
        raise ValueError("log-n must be at least 7")
    result = modal_path(args.log_n, args.high, args.low, args.edge)
    print(f"n=2^{args.log_n} edge={result['edge']} schedule={args.high}/{args.low}")
    print(f"terminal_counts=({result['left']},{result['right']}) "
          f"bad={result['bad']}")
    print(f"path_events=({result['matching_events']} matches, "
          f"{result['split_events']} splits) "
          f"log_path_probability_lower={result['path_logp_lower']:.12g}")
    print(f"log_E_failures_lower_positive="
          f"{result['expected_failures_lower_exceeds_one']} "
          f"(sufficient iff n > {result['positivity_threshold']:.12g})")
    if result["log_expected_lower"] is not None:
        print(f"log_E_failures_lower={result['log_expected_lower']:.12g}")
    if args.trace:
        for width, support, counts in reversed(result["scale_trace"]):
            print(f"width={width} support={support} counts={counts}")
    print("The path lower bound uses only that each chosen modal outcome has "
          "probability at least 1/(width+1); it is not an impossibility proof "
          "for deterministic networks.")


if __name__ == "__main__":
    main()
