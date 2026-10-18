"""Four-block research oracle: exhaustive threshold-count dynamics.

The oracle assumes a paired repair with relative outside-core residuals.
It is not an implementation of comparator networks or the local support guard.
"""
from fractions import Fraction as F
from itertools import product


SCHEDULES = {
    "adjacent_sweep": [[(0,1),(2,3)],[(1,2)]],
    "four_block_sort": [[(0,1),(2,3)],[(0,2),(1,3)],[(1,2)]],
    "four_adjacent_phases": [[(0,1),(2,3)],[(1,2)],[(0,1),(2,3)],[(1,2)]],
}


def outcomes(state, pair, m, error):
    i,j = pair
    H,L = m-state[i],state[j]
    delta = L-H
    cap_a,cap_b = int(error*H),int(error*L)
    possibilities = set()
    for a in range(cap_a+1):
        for b in range(cap_b+1):
            new = list(state)
            new[i] = m-max(a,b-delta)
            new[j] = state[i]+state[j]-new[i]
            possibilities.add(tuple(new))
    return possibilities


def advance(states, phase, m, error):
    for pair in phase:
        states = set().union(*(outcomes(s,pair,m,error) for s in states))
    return states


def main():
    m = 8
    error = F(1,4)
    for name,phases in SCHEDULES.items():
        worst = F(0)
        witness = None
        for cut in (1,2,3):
            for state in product(range(m+1), repeat=4):
                if sum(state) != cut*m:
                    continue
                before = cut*m-sum(state[:cut])
                if before == 0:
                    continue
                outputs = {state}
                for phase in phases:
                    outputs = advance(outputs,phase,m,error)
                after,final = max((cut*m-sum(s[:cut]),s) for s in outputs)
                ratio = F(after,before)
                if ratio > worst:
                    worst = ratio
                    witness = cut,state,final,before,after
        print(f"{name}: worst directional error ratio={worst}, witness={witness}")


if __name__ == "__main__":
    main()
