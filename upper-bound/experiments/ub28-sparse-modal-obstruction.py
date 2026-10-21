#!/usr/bin/env python3
"""Search a sparse modal count path against UB-28's first-moment gate.

For balanced top-half counts, this follows a hypergeometric mode through the
multiscale count process and checks the exact finite anchor at the central
edge. It sums probabilities only in the local dependency cone. The resulting
lower bound on E[failing binary inputs] tests the first-moment route; it is
not an impossibility result for sorting networks.
"""

import argparse
import importlib.util
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_local_edge_maxpath", HERE / "ub28-local-edge-maxpath.py"
)
maxpath = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(maxpath)


def log_choose(n, k):
    if k < 0 or k > n:
        return -math.inf
    return (math.lgamma(n + 1) - math.lgamma(k + 1)
            - math.lgamma(n - k + 1))


def matching_mode(h, left_ones, right_ones):
    """A mode of Hypergeom(h, right_ones, left_ones)."""
    x = ((left_ones + 1) * (right_ones + 1)) // (h + 2)
    return min(left_ones, right_ones,
               max(0, left_ones + right_ones - h, x))


def split_mode(parent_width, count):
    child_width = parent_width // 2
    return min(child_width, (count + 1) // 2)


def local_support_schedule(n, anchor_support, high, low):
    """Return only matching pairs and split parents in the edge's cone."""
    delta = n // 32 - 256 // 32
    support = sorted(i + delta for i in anchor_support)
    blocks, width = n // 16, 16
    reverse_ops = []
    while blocks > 2:
        for parent in sorted({i // 2 for i in support}):
            children = tuple(i for i in (2 * parent, 2 * parent + 1)
                             if i in support)
            before = list(support)
            after = sorted((set(support) - set(children)) | {parent})
            reverse_ops.append(("split", after, before, parent, width * 2, None))
            support = after
        blocks //= 2
        width *= 2
        distance = (n.bit_length() - 2) - (width.bit_length() - 1)
        rounds = high if distance % 2 == 0 else low
        for offset in (1, 0):
            for left in range(offset, blocks - 1, 2):
                right = left + 1
                if left not in support and right not in support:
                    continue
                before = list(support)
                after = sorted(set(support) | {left, right})
                reverse_ops.append(
                    ("match", after, before, left, width, (right, rounds))
                )
                support = after
    if support != [0, 1]:
        raise AssertionError(f"support does not close at top: {support}")

    return list(reversed(reverse_ops))


def modal_local_path(log_n, high, low, anchor_rounds):
    n = 1 << log_n
    edge = n // 2 - 2
    anchor_support, anchor_table, _ = maxpath.edge_state_at_width(
        256, 126, anchor_rounds, 16
    )
    ops = local_support_schedule(
        n, anchor_support, high, low
    )
    support = [0, 1]
    profile = [n // 4, n // 4]
    matching_log_probability = 0.0
    split_log_probability = 0.0
    matching_events = 0
    split_events = 0
    for kind, support_pre, support_post, index, stage_width, extra in ops:
        if support != support_pre:
            raise AssertionError(f"support mismatch: {support} != {support_pre}")
        values = dict(zip(support, profile))
        if kind == "match":
            right, rounds = extra
            a, b = values[index], values[right]
            for _ in range(rounds):
                x = matching_mode(stage_width, a, b)
                matching_log_probability += (
                    log_choose(b, x)
                    + log_choose(stage_width - b, a - x)
                    - log_choose(stage_width, a)
                )
                matching_events += 1
                a, b = x, a + b - x
            values[index], values[right] = a, b
        else:
            parent = index
            count = values[parent]
            left_count = split_mode(stage_width, count)
            child_width = stage_width // 2
            split_log_probability += (
                log_choose(child_width, left_count)
                + log_choose(child_width, count - left_count)
                - log_choose(stage_width, count)
            )
            split_events += 1
            values.pop(parent)
            left_child, right_child = 2 * parent, 2 * parent + 1
            if left_child in support_post:
                values[left_child] = left_count
            if right_child in support_post:
                values[right_child] = count - left_count
        profile = [values[i] for i in support_post]
        support = support_post

    profile = tuple(profile)
    anchor_log_probability = float(anchor_table[profile])
    return {
        "n": n,
        "edge": edge,
        "profile": profile,
        "anchor_log_probability": anchor_log_probability,
        "matching_log_probability": matching_log_probability,
        "split_log_probability": split_log_probability,
        "matching_events": matching_events,
        "split_events": split_events,
        "type_log_count": 2 * log_choose(n // 2, n // 4),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-n", type=int, default=20)
    parser.add_argument("--high", type=int, default=235)
    parser.add_argument("--low", type=int, default=35)
    parser.add_argument("--anchor-rounds", type=int, default=150)
    args = parser.parse_args()
    if args.log_n < 8:
        raise ValueError("require log-n >= 8")
    result = modal_local_path(args.log_n, args.high, args.low,
                              args.anchor_rounds)
    local_logp = (result["matching_log_probability"]
                  + result["split_log_probability"])
    log_expected_failures = (result["type_log_count"] + local_logp
                             + result["anchor_log_probability"])
    print(f"n=2^{args.log_n} edge={result['edge']} schedule={args.high}/{args.low}")
    print(f"width16_modal_profile={result['profile']} "
          f"anchor_logp={result['anchor_log_probability']:.12g}")
    print(f"local_events=({result['matching_events']} matching, "
          f"{result['split_events']} split) local_logp={local_logp:.12g}")
    print(f"balanced_type_log_count={result['type_log_count']:.12g} "
          f"log_E[failing inputs]_lower={log_expected_failures:.12g}")
    print("Lower bound is a floating-point screen; the mode-count argument "
          "gives exp(n ln 2 - O(log^2 n)) asymptotically if the anchor profile "
          "continues to be viable.")


if __name__ == "__main__":
    main()
