"""Exact full zero-certificate growth for aligned sorted-block comparators."""
import argparse
from fractions import Fraction
import json
import math


def probe(m):
    # Sorted wire with zero-certificate size j is threshold t=m-j+1.
    # There are F_j zero baselines in one block. At a joint zero baseline,
    # AND has certificate j and OR has certificate 2j, instead of 2j total.
    counts = [sum(math.comb(m, a) for a in range(m-j+1)) for j in range(1,m+1)]
    before = m * (m+3) * 2**(2*m-2)
    gain = sum(j * count**2 for j,count in enumerate(counts,1))
    ratio = Fraction(before+gain, before)
    # Independent direct sum of input-weight cases for small blocks.
    if m <= 8:
        direct_before = direct_after = 0
        for a in range(m+1):
            for b in range(m+1):
                multiplicity = math.comb(m,a)*math.comb(m,b)
                for j in range(1,m+1):
                    t = m-j+1
                    zeros = int(a<t)+int(b<t)
                    direct_before += multiplicity*j*zeros
                    direct_after += multiplicity*j*(3 if zeros==2 else zeros)
        assert direct_before == before and direct_after == before+gain
    return dict(block_size=m, wires=2*m, before_sum=before, increase_sum=gain,
                exact_ratio=str(ratio), ratio=float(ratio))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = dict(family="Two sorted blocks; one layer compares corresponding positions",
                  cases=[probe(m) for m in (2,4,8,16,32,64,128)],
                  limiting_ratio="3/2 (derived using binomial concentration)",
                  status="Exact integer certificate counts, derived limit; not Lean checked; no sorting-depth improvement")
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps([dict(block_size=c["block_size"],ratio=c["ratio"]) for c in result["cases"]]))
