#!/usr/bin/env python3
"""Exact sparse-support adversary for a fixed multiround row-scramble core.

For support at most ``support`` ones, every active row lies among the first
``support`` rows after column sorting. The MILP encodes all initial monotone
column-height profiles and maximizes the largest output column height.
"""
import argparse

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from local_core_multiround_adversary import evaluate, make_scrambles


def gf64_mul(a, b):
    """Multiply in GF(2^6), using x^6+x+1 as the reduction polynomial."""
    product = 0
    while b:
        if b & 1:
            product ^= a
        b >>= 1
        a <<= 1
        if a & 64:
            a ^= 0x43
    return product


def solve(columns=64, support=18, rounds=3, seed=0, time_limit=120,
          cyclic_multipliers=None, xor_multipliers=None):
    if cyclic_multipliers is not None and xor_multipliers is not None:
        raise ValueError("choose one structured scramble family")
    if xor_multipliers is not None:
        if columns != 64 or len(xor_multipliers) != rounds:
            raise ValueError("GF(2^6) translations need 64 columns and one multiplier per round")
        # In row r, source column c moves to c XOR (a*r) in GF(2^6).
        scrambles = [
            [[source ^ gf64_mul(multiplier, row)
              for source in range(columns)]
             for row in range(support)]
            for multiplier in xor_multipliers
        ]
    elif cyclic_multipliers is None:
        scrambles = make_scrambles(support, columns, seed, rounds)
    else:
        if len(cyclic_multipliers) != rounds:
            raise ValueError("need one cyclic multiplier per round")
        # In row r, source column c moves to c + multiplier*r (mod n).
        # This is a deterministic family of valid row permutations.
        scrambles = [
            [[(source + multiplier * row) % columns
              for source in range(columns)]
             for row in range(support)]
            for multiplier in cyclic_multipliers
        ]
    inverse = []
    for stage in scrambles:
        inverse_stage = []
        for source_to_dest in stage:
            inv = [0] * columns
            for source, dest in enumerate(source_to_dest):
                inv[dest] = source
            inverse_stage.append(inv)
        inverse.append(inverse_stage)

    # x[t,j,r] says column j has a one in row r entering round t.
    nx = rounds * columns * support
    z0 = nx
    tvar = nx + columns
    nvars = tvar + 1

    def x(t, j, r):
        return (t * columns + j) * support + r

    rows, lower, upper = [], [], []

    def add(terms, lo=-np.inf, hi=np.inf):
        rows.append({i: c for i, c in terms.items() if c})
        lower.append(lo)
        upper.append(hi)

    # Initial column heights form a monotone profile with at most `support`
    # ones in total.
    for j in range(columns):
        for r in range(support - 1):
            add({x(0, j, r + 1): 1, x(0, j, r): -1}, hi=0)
    add({x(0, j, r): 1 for j in range(columns)
         for r in range(support)}, hi=support)

    # A row permutation sends each input row's ones to a uniform relabeling
    # of columns. Column sorting then turns output heights into threshold bits.
    for stage in range(rounds):
        for dest in range(columns):
            height = {x(stage, inverse[stage][r][dest], r): 1
                      for r in range(support)}
            if stage + 1 == rounds:
                continue
            for level in range(support):
                # height >= level+1 iff the next threshold bit is one.
                lower_terms = dict(height)
                lower_terms[x(stage + 1, dest, level)] = -(level + 1)
                add(lower_terms, lo=0)
                # height <= level iff the next threshold bit is zero.
                upper_terms = dict(height)
                upper_terms[x(stage + 1, dest, level)] = -(support - level)
                add(upper_terms, hi=level)

    # Select one terminal column and maximize its height.
    add({z0 + j: 1 for j in range(columns)}, lo=1, hi=1)
    for dest in range(columns):
        height = {x(rounds - 1, inverse[rounds - 1][r][dest], r): -1
                  for r in range(support)}
        height[tvar] = 1
        height[z0 + dest] = support
        add(height, hi=support)

    rr, cc, data = [], [], []
    for row_id, terms in enumerate(rows):
        for col_id, value in terms.items():
            rr.append(row_id)
            cc.append(col_id)
            data.append(value)
    matrix = coo_matrix((data, (rr, cc)), shape=(len(rows), nvars)).tocsr()

    objective = np.zeros(nvars)
    objective[tvar] = -1
    integrality = np.zeros(nvars, dtype=np.uint8)
    integrality[:nx + columns] = 1
    lb = np.zeros(nvars)
    ub = np.ones(nvars)
    ub[tvar] = support
    result = milp(
        objective,
        integrality=integrality,
        bounds=Bounds(lb, ub),
        constraints=LinearConstraint(matrix, lower, upper),
        options={"time_limit": time_limit},
    )

    out = {"columns": columns, "support": support, "rounds": rounds,
           "seed": seed, "variables": nvars, "constraints": len(rows),
           "status": int(result.status), "success": bool(result.success),
           "message": result.message}
    if result.x is not None:
        vector = np.rint(result.x[:nx]).astype(int)
        initial = [sum(vector[x(0, j, r)] for r in range(support))
                   for j in range(columns)]
        profiles, total, area = evaluate(initial, scrambles)
        terminal = profiles[-1]
        out.update({"max_height": int(round(result.x[tvar])),
                    "initial_heights": initial,
                    "round_heights": [max(profile) for profile in profiles],
                    "terminal_max_height": max(terminal),
                    "terminal_area": area, "support_used": total})
        assert out["max_height"] == out["terminal_max_height"]
        assert total <= support
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--support", type=int, default=18)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    parser.add_argument("--time-limit", type=float, default=120)
    parser.add_argument("--cyclic-multipliers", type=int, nargs="+")
    parser.add_argument("--xor-multipliers", type=int, nargs="+")
    args = parser.parse_args()
    for seed in args.seeds:
        print(solve(args.columns, args.support, args.rounds, seed,
                    args.time_limit, args.cyclic_multipliers,
                    args.xor_multipliers), flush=True)
