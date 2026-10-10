#!/usr/bin/env python3
"""Exact finite probe of joint minimum certificate statistics.

Enumerates reachable Boolean wire functions of standard four-wire comparator
networks. Statistics are minima over *all* input supports, not chosen witnesses.
This is research enumeration, not an asymptotic improvement or a kernel proof.
"""

import argparse
from fractions import Fraction
import json
import math


def parallel_layers(n):
    def rec(remaining):
        if not remaining:
            yield ()
            return
        i, *rest = remaining
        yield from rec(rest)
        for j in rest:
            for tail in rec([k for k in rest if k != j]):
                yield ((i, j),) + tail
    return [layer for layer in rec(list(range(n))) if layer]


def minimum_sizes(function, n):
    zeros = min(n - x.bit_count() for x in range(1 << n) if not (function >> x & 1))
    ones = min(x.bit_count() for x in range(1 << n) if function >> x & 1)
    return zeros, ones


def enumerate_networks(n, max_layers):
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    paths = {initial: ()}
    frontier = [initial]
    actions = parallel_layers(n)
    signatures = {}
    product_ratio = Fraction(0)
    ratio_witness = None
    counterexample = None
    nonredundant_signatures = {}
    nonredundant_counterexample = None
    largest_active_union_sum = 0
    for depth in range(max_layers):
        following = []
        for state in frontier:
            for layer in actions:
                output = list(state)
                for i, j in layer:
                    a, b = state[i], state[j]
                    lo, hi = a & b, a | b
                    signature = (minimum_sizes(a, n), minimum_sizes(b, n))
                    after = (minimum_sizes(lo, n), minimum_sizes(hi, n))
                    entry = {"prefix": paths[state], "comparator": (i, j),
                             "input_functions": (a, b), "output_statistics": after}
                    previous = signatures.setdefault(signature, {})
                    if after not in previous and previous and counterexample is None:
                        counterexample = {"input_statistics": signature,
                                          "first": next(iter(previous.values())), "second": entry}
                    previous.setdefault(after, entry)
                    if (lo, hi) != (a, b):
                        largest_active_union_sum = max(largest_active_union_sum, after[0][1] + after[1][0])
                        active = nonredundant_signatures.setdefault(signature, {})
                        if after not in active and active and nonredundant_counterexample is None:
                            nonredundant_counterexample = {"input_statistics": signature,
                                "first": next(iter(active.values())), "second": entry}
                        active.setdefault(after, entry)
                    before_product = sum(z * o for z, o in signature)
                    after_product = sum(z * o for z, o in after)
                    ratio = Fraction(after_product, before_product)
                    if ratio > product_ratio:
                        product_ratio, ratio_witness = ratio, entry
                    output[i], output[j] = lo, hi
                output = tuple(output)
                if output not in paths:
                    paths[output] = paths[state] + (layer,)
                    following.append(output)
        frontier = following
        if not frontier:
            break
    monomial_samples = []
    for p, q in ((1, 1), (0.5, 0.5), (1, 2), (2, 1), (0.5, 2)):
        forced_factor = (2 ** p + 2 ** q) / 2
        monomial_samples.append({"p": p, "q": q, "forced_uniform_factor": forced_factor,
                                  "largest_possible_leading_coefficient": (p + q) / math.log2(forced_factor)})
    return {"wires": n, "reachable_states": len(paths), "exhausted_reachable_states": not frontier,
            "explored_layer_bound": max_layers, "input_statistic_signatures": len(signatures),
            "nonclosed_summary_witness": counterexample,
            "nonclosed_summary_nonredundant_witness": nonredundant_counterexample,
            "largest_nonredundant_union_cost_sum": largest_active_union_sum,
            "largest_product_ratio": str(product_ratio), "product_ratio_witness": ratio_witness,
            "monomial_samples": monomial_samples,
            "scope": "exact finite enumeration; universal inequalities need separate proofs"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=4, choices=(2, 3, 4))
    parser.add_argument("--max-layers", type=int, default=16)
    parser.add_argument("--output")
    args = parser.parse_args()
    result = json.dumps(enumerate_networks(args.wires, args.max_layers), indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as out:
            out.write(result + "\n")
    else:
        print(result)


if __name__ == "__main__":
    main()
