#!/usr/bin/env python3
"""Exact deterministic count witness for any sampled fixed receive routing.
The mathematical construction applies to any row permutations; sampling here
checks implementation only, not a universal probabilistic certificate.
"""
import random
from fractions import Fraction


def witness(d, receivers, fringe, rows, seed):
    assert d*rows > fringe
    source_columns = d*receivers
    rng = random.Random(seed)
    heights = [0]*source_columns
    permutations = []
    for row in range(rows):
        perm = list(range(source_columns))
        rng.shuffle(perm)
        permutations.append(perm)
        for i in perm[:d]:  # first d entries feed receiving column zero
            heights[i] = max(heights[i], row+1)
    mass = sum(heights)
    load = sum(sum(heights[i] > row for i in perm[:d])
               for row,perm in enumerate(permutations))
    cost_bound = d*rows*(rows+1)//2
    assert mass <= cost_bound
    assert load == d*rows
    escapes = load-fringe
    assert Fraction(escapes,mass) >= Fraction(d*rows-fringe,cost_bound)
    # The other source rows can be completed arbitrarily: heights <= rows,
    # so there are no additional zeros outside the source's chosen low port.
    deviation = sum(abs(Fraction(h)-Fraction(mass,source_columns))
                    for h in heights)/source_columns
    assert deviation <= Fraction(2*mass,source_columns)
    return mass,load,escapes,cost_bound,deviation


if __name__ == '__main__':
    print('Exact implementation check; universal proof is FRINGE-WITNESS.md')
    for d, receivers, fringe, rows in ((4,64,16,8), (64,256,3968,124),
                                     (256,64,7934,62)):
        ratios=[]
        for seed in range(5):
            h,load,e,bound,dev=witness(d,receivers,fringe,rows,seed)
            ratios.append(Fraction(e,h))
        guaranteed=Fraction(d*rows-fringe,d*rows*(rows+1)//2)
        print(f'd={d} columns={d*receivers} f={fringe} t={rows}: '
              f'guaranteed escapes/H>={guaranteed} '
              f'({float(guaranteed):.8g}); '
              f'sampled min={float(min(ratios)):.8g}')
