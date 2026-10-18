"""Joint-allocation example and conservative scalar cost envelope.

Exact rational calculations; no network construction or Lean proof.
"""
from fractions import Fraction as F
from uniform_concentration import envelope


def spillover_example():
    width = 3
    protected = [6, 7, 8, 9, 12, 15, 18, 21]
    pool = sorted(set(range(24))-set(protected))
    bins = [[protected[q]]+pool[2*q:2*q+2] for q in range(8)]
    old_errors = [int(not q*width <= v < (q+1)*width)
                  for q, v in enumerate(protected)]
    new_errors = [sum(not q*width <= v < (q+1)*width for v in block)
                  for q, block in enumerate(bins)]
    print(f"Spillover example: protected errors={old_errors}, final bin errors={new_errors}")
    print(f"Bin 2: {bins[2]} (native interval [6,9)); two wrong keys despite no protected error")
    print("All four lower output bins contain only keys <12; upper bins contain only keys >=12.")


def purity_budget():
    A, mu, nu = F(19,4), F(199,10000), F(707,1000)
    root = F(300000)/nu**2
    size = root*A**4+32
    maximum = (size.numerator+size.denominator-1)//size.denominator
    wrong = int(mu*root*A**4)  # all non-native level-4 keys, not only wrong halves
    one_core, depth = envelope(1, maximum, wrong)
    two_core = min(maximum, 2*one_core)
    known = root+32+root/(4*A*A-1)+4*(root*A*A+32)
    # Each term is a rational upper bound on an integer cardinality.
    pool = int(known)+16*two_core
    h = (pool-1).bit_length()
    sorting = h*(h+1)//2
    print(f"Finest-bin purity: maximum={maximum}, wrong-key budget={wrong}")
    print(f"One-sided envelope: core<={one_core}, depth<={depth}")
    print(f"Sequential two-tail core envelope: {two_core}; pool envelope={pool}")
    print(f"Pool sort<={sorting}; conditional cost<=2*{depth}+{sorting}+4={2*depth+sorting+4}")
    print("The bound captures no savings: its two-tail core envelope includes the entire level-4 bag.")


if __name__ == "__main__":
    spillover_example()
    purity_budget()
