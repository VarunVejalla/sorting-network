#!/usr/bin/env python3
"""Inspect actual certificates in the positional Kahale barrier schedule.

Certificates use exact input-index bit sets. Greedy deletion returns an
inclusion-minimal certificate, not necessarily a minimum-cardinality one.
This is a finite research probe, not an asymptotic lower-bound argument.
"""

import argparse
import json

from kahale_positional_barrier import layers, expand_layer, find_unsorted_input, fib


def execute(schedule, values):
    values = values[:]
    for layer in schedule:
        for i, j in layer:
            values[i], values[j] = min(values[i], values[j]), max(values[i], values[j])
    return values


def indices(mask):
    return [i for i in range(mask.bit_length()) if mask >> i & 1]


def certificate_input(n, mask, value):
    return [value if mask >> i & 1 else 1 - value for i in range(n)]


def shrink(schedule, n, mask, wire, value):
    for i in indices(mask):
        candidate = mask ^ (1 << i)
        if execute(schedule, certificate_input(n, candidate, value))[wire] == value:
            mask = candidate
    # For a monotone network, testing this extremal input proves the certificate
    # property for every assignment of the remaining inputs.
    if execute(schedule, certificate_input(n, mask, value))[wire] != value:
        raise ArithmeticError("invalid certificate")
    return mask


def probe(d):
    witness = find_unsorted_input(d, 64, 0)
    if "input" not in witness:
        return witness
    n = witness["arity"]
    schedule = [list(expand_layer(block)) for block in layers(n, d)]
    original = list(map(int, witness["input"]))
    values = original[:]
    heights = [0] * n
    conditional = [1 << i for i in range(n)]
    zeros = [1 << i for i in range(n)]
    ones = zeros[:]
    overlap_events = 0
    largest_overlap = 0
    zero_unions_without_growth = 0
    one_unions_without_growth = 0
    for layer in schedule:
        for i, j in layer:
            a, b = values[i], values[j]
            si, sj = conditional[i], conditional[j]
            pick = lambda x, y: min((x, y), key=lambda m: (m.bit_count(), m))
            if a == b:
                if a == 0:
                    conditional[i], conditional[j] = pick(si, sj), si | sj
                else:
                    conditional[i], conditional[j] = si | sj, pick(si, sj)
            elif a < b:
                conditional[i], conditional[j] = si, sj
            else:
                conditional[i], conditional[j] = sj, si
            zi, zj, oi, oj = zeros[i], zeros[j], ones[i], ones[j]
            loss = (zi & zj).bit_count() + (oi & oj).bit_count()
            overlap_events += bool(loss)
            largest_overlap = max(largest_overlap, loss)
            zero_unions_without_growth += (zi | zj).bit_count() == max(zi.bit_count(), zj.bit_count())
            one_unions_without_growth += (oi | oj).bit_count() == max(oi.bit_count(), oj.bit_count())
            zeros[i], zeros[j] = pick(zi, zj), zi | zj
            ones[i], ones[j] = oi | oj, pick(oi, oj)
            hi, hj = heights[i], heights[j]
            heights[i], heights[j] = min(hi, hj), max(hi, hj) + 1
            values[i], values[j] = min(a, b), max(a, b)
    i = witness["inversion_at"]
    j = i + 1
    one_cert = shrink(schedule, n, conditional[i], i, 1)
    zero_cert = shrink(schedule, n, conditional[j], j, 0)
    if one_cert & zero_cert:
        raise ArithmeticError("inversion certificates should be disjoint")
    combined = certificate_input(n, one_cert, 1)
    if execute(schedule, combined)[i] != 1 or execute(schedule, combined)[j] != 0:
        raise ArithmeticError("joint certificate witness failed")
    violations = []
    for wire in range(n):
        for value, cert, required in ((0, zeros[wire], wire + 1),
                                      (1, ones[wire], n - wire)):
            if cert.bit_count() < required:
                violations.append({"wire": wire, "value": value,
                                   "certificate_size": cert.bit_count(),
                                   "sorting_requires": required})
    return {
        "depth": d, "arity": n, "inversion": [i, j],
        "zero_height_at_right_wire": heights[j],
        "power_of_two_height_bound": 1 << heights[j],
        "zero_certificate": indices(zero_cert),
        "zero_certificate_size": zero_cert.bit_count(),
        "zero_sorting_requires": j + 1,
        "zero_certificate_before_deletion": conditional[j].bit_count(),
        "single_policy_zero_certificate_size": zeros[j].bit_count(),
        "one_certificate": indices(one_cert),
        "one_certificate_size": one_cert.bit_count(),
        "one_sorting_requires": n - i,
        "one_certificate_before_deletion": conditional[i].bit_count(),
        "single_policy_one_certificate_size": ones[i].bit_count(),
        "certificates_disjoint": True,
        "chosen_union_overlap_events": overlap_events,
        "largest_combined_union_overlap": largest_overlap,
        "chosen_zero_unions_without_size_growth": zero_unions_without_growth,
        "chosen_one_unions_without_size_growth": one_unions_without_growth,
        "chosen_certificate_threshold_violations": violations,
        "scope": "valid inclusion-minimal witnesses, not optimal cardinalities or an asymptotic improvement",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=40)
    parser.add_argument("--output")
    args = parser.parse_args()
    result = json.dumps(probe(args.depth), indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as out:
            out.write(result + "\n")
    else:
        print(result)


if __name__ == "__main__":
    main()
