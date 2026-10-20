#!/usr/bin/env python3
"""Exact deterministic count witness for any sampled fixed receive routing.
The mathematical construction applies to any row permutations; sampling here
checks implementation only, not a universal probabilistic certificate.
"""
import random
import math
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


def first_row_obstruction(k=8, d=64, receivers=128, seed=0):
    assert receivers%2 == 0
    rng=random.Random(seed)
    outputs=[0]*receivers
    for _ in range(k):
        perm=list(range(d*receivers))
        rng.shuffle(perm)
        heights=[0]*(d*receivers)
        for i in perm[:d*(receivers//2)]:
            heights[i]=1
        assert sum(heights)==d*receivers//2
        deviation=sum(abs(Fraction(h)-Fraction(1,2)) for h in heights)/(d*receivers)
        assert deviation==Fraction(1,2)
        for v in range(receivers):
            outputs[v]+=sum(heights[i] for i in perm[d*v:d*(v+1)])
    load=k*d
    assert outputs==[load]*(receivers//2)+[0]*(receivers//2)
    deviation=sum(abs(Fraction(h)-Fraction(load,2)) for h in outputs)/receivers
    assert deviation==Fraction(load,2)
    return deviation


if __name__ == '__main__':
    print('Exact implementation check; universal proof is FRINGE-WITNESS.md')
    out=first_row_obstruction()
    c_squared=Fraction(512*512,2*Fraction(2049,4))
    print(f'first-row obstruction: input e=1/2, output e={out}, '
          f'C^2>={c_squared}, C>={math.sqrt(float(c_squared)):.8f}')
    for d, receivers, fringe, rows in ((4,128,16,8), (64,1024,3968,124)):
        ratios=[]
        for seed in range(5 if d==4 else 1):
            h,load,e,bound,dev=witness(d,receivers,fringe,rows,seed)
            assert h <= Fraction(fringe*receivers,8)  # delta_F support
            ratios.append(Fraction(e,h))
        guaranteed=Fraction(d*rows-fringe,d*rows*(rows+1)//2)
        print(f'd={d} columns={d*receivers} f={fringe} t={rows}: '
              f'guaranteed escapes/H>={guaranteed} '
              f'({float(guaranteed):.8g}); '
              f'sampled min={float(min(ratios)):.8g}')
