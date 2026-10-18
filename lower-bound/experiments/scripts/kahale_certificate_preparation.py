"""Exact certificate growth in realizable recursive aligned comparator layers.

No sorting claim: this family challenges universal prefix growth bounds.
"""
import argparse
from fractions import Fraction
import json
import math


def verify_small(d, expected):
    n = 1 << d
    full = (1 << n) - 1
    state = [sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n)]
    heights = [0] * n
    for stage in range(d):
        half = 1 << stage
        for start in range(0, n, 2*half):
            for offset in range(half):
                a,b = start+offset,start+offset+half
                assert heights[a] == heights[b]
                state[a],state[b] = state[a]&state[b],state[a]|state[b]
                heights[b] += 1
    cost = 0
    failures = 0
    for x in range(1 << n):
        output = sum(((f >> x)&1) << i for i,f in enumerate(state))
        failures += output != ((1 << x.bit_count())-1) << (n-x.bit_count())
        for f in state:
            if (f >> x)&1:
                continue
            available = full ^ x
            c = available
            best = n
            while True:
                if not (f >> (full ^ c))&1:
                    best = min(best,c.bit_count())
                if not c:
                    break
                c = (c-1)&available
            cost += best
    assert Fraction(cost,1 << n) == expected
    return dict(independent_truth_table_check=True, nonsorted_inputs=failures,
                all_gates_equal_scalar_height=True)


def probe(max_depth):
    # Every zero baseline of a given read-once output has the same minimum
    # certificate size. Disjoint identical children: AND keeps c; OR doubles c.
    signals = [(Fraction(1,2),1)]
    rows = []
    previous = Fraction(1,2)
    for d in range(1,max_depth+1):
        signals = [out for p,c in signals for out in ((2*p-p*p,c),(p*p,2*c))]
        cost = sum(p*c for p,c in signals)
        n = 1 << d
        amplification = cost/Fraction(n,2)
        biased_mean = cost/(3**d)
        if d >= 3:
            assert biased_mean >= Fraction(7,384)
        row = dict(depth=d,wires=n,expected_zero_certificate_sum=str(cost),
                   amplification=str(amplification), amplification_float=float(amplification),
                   layer_growth=float(cost/(2*previous)),
                   geometric_mean_growth=float(amplification)**(1/d),
                   biased_zero_probability=float(biased_mean))
        middle = [i for i in range(n) if i.bit_count() == d//2]
        row["fixed_middle_antichain_size"] = len(middle)
        if d <= 5:
            lower = sum(1 << i for i in range(n) if i.bit_count() > d//2)
            for assignment in range(1 << len(middle)):
                x = lower | sum(((assignment >> j)&1) << i for j,i in enumerate(middle))
                out = x
                for stage in range(d):
                    half = 1 << stage
                    for start in range(0,n,2*half):
                        for offset in range(half):
                            a,b = start+offset,start+offset+half
                            if (out >> a)&1 and not (out >> b)&1:
                                out ^= (1 << a) | (1 << b)
                assert out == x
            row["exhaustive_fixed_antichain_assignments"] = 1 << len(middle)
        if d <= 3:
            row.update(verify_small(d,cost))
        rows.append(row)
        previous = cost
    return dict(cases=rows,
                derived_bounds="For d>=3: (7/384)*3^d <= expected certificate sum <= 3^d",
                limiting_amortized_growth="3/2 relative to initial n/2",
                status="Exact rational recursion, independent truth tables through 8 wires; asymptotic argument derived, not Lean checked")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth",type=int,default=12)
    parser.add_argument("--output",required=True)
    args = parser.parse_args()
    result = probe(args.max_depth)
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps([dict(depth=r["depth"],wires=r["wires"],
                           amplification=r["amplification_float"],
                           layer_growth=r["layer_growth"],
                           geometric_mean_growth=r["geometric_mean_growth"])
                      for r in result["cases"]],indent=2))
