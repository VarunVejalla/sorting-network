#!/usr/bin/env python3
"""Exact MILP maximum of full-row aggregate defect for fixed scrambles.

Unary variables encode the input column heights, the first output heights,
the final output heights, and total mass. The model is an exact finite
adversary for the specified rectangle and scramble pair; it is not an
all-width proof.
"""
import argparse
import random

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from local_core_adversary import make_inverse_scrambles


def maximize(rows, columns, seed=0, time_limit=120, relax=False):
    inv1, inv2 = make_inverse_scrambles(rows, columns, seed)
    mn = rows * columns
    x0, y0, z0, h0 = 0, mn, 2 * mn, 3 * mn
    variables = 4 * mn
    objective = np.zeros(variables)
    for col in range(columns):
        for s in range(1, rows + 1):
            objective[z0 + col * rows + s - 1] = -(2 * s - 1)
    for s in range(1, mn + 1):
        # Increment of the minimum squared column-height sum at total mass s.
        objective[h0 + s - 1] = 2 * ((s - 1) // columns) + 1

    row_ids, col_ids, data = [], [], []
    lower, upper = [], []

    def constraint(terms, lo=-np.inf, hi=np.inf):
        rid = len(lower)
        for col, value in terms.items():
            if value:
                row_ids.append(rid)
                col_ids.append(col)
                data.append(value)
        lower.append(lo)
        upper.append(hi)

    # Each source column is an initial unary height profile.
    for col in range(columns):
        for r in range(rows - 1):
            constraint({x0 + col * rows + r + 1: 1,
                        x0 + col * rows + r: -1}, hi=0)

    # A column sort preserves each destination column's number of ones.
    # The unary y profile is the sorted output, so constrain its total to the
    # row-scrambled input total (not row-by-row equality with the unsorted bits).
    for dest in range(columns):
        terms = {}
        for r in range(rows):
            terms[y0 + dest * rows + r] = 1
            for source in range(columns):
                if inv1[r][source] == dest:
                    terms[x0 + source * rows + r] = -1
        constraint(terms, lo=0, hi=0)
    for col in range(columns):
        for r in range(rows - 1):
            constraint({y0 + col * rows + r + 1: 1,
                        y0 + col * rows + r: -1}, hi=0)

    # The second column sort likewise preserves only each column total.
    for dest in range(columns):
        terms = {}
        for r in range(rows):
            terms[z0 + dest * rows + r] = 1
            for source in range(columns):
                if inv2[r][source] == dest:
                    terms[y0 + source * rows + r] = -1
        constraint(terms, lo=0, hi=0)
    for col in range(columns):
        for s in range(rows - 1):
            constraint({z0 + col * rows + s + 1: 1,
                        z0 + col * rows + s: -1}, hi=0)

    # Unary total-mass profile and exact mass conservation.
    for s in range(mn - 1):
        constraint({h0 + s + 1: 1, h0 + s: -1}, hi=0)
    terms = {h0 + s: 1 for s in range(mn)}
    for col in range(columns):
        for r in range(rows):
            terms[x0 + col * rows + r] = -1
    constraint(terms, lo=0, hi=0)

    matrix = coo_matrix((data, (row_ids, col_ids)),
                        shape=(len(lower), variables)).tocsr()
    # x, y, and z must be Boolean unary profiles. The h variables encode the
    # balanced-square baseline as a convex piecewise-linear function of the
    # integral total mass, so they need not be integer.
    integrality = np.zeros(variables, dtype=np.uint8)
    if not relax:
        integrality[x0:h0] = 1

    result = milp(
        objective,
        integrality=integrality,
        bounds=Bounds(np.zeros(variables), np.ones(variables)),
        constraints=LinearConstraint(matrix, np.asarray(lower),
                                     np.asarray(upper)),
        options={"time_limit": time_limit},
    )
    out = {"rows": rows, "columns": columns, "seed": seed,
           "relaxation": relax,
           "variables": variables, "constraints": len(lower),
           "nonzeros": len(data), "success": bool(result.success),
           "status": int(result.status), "message": result.message}
    if result.x is not None:
        out["area"] = round(-result.fun / 2)
        out["area_fraction"] = -result.fun / (2 * rows * columns)
        out["relative_gap"] = getattr(result, "mip_gap", None)
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=16)
    parser.add_argument("--columns", type=int, default=4)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--time-limit", type=float, default=120)
    parser.add_argument("--relax", action="store_true")
    args = parser.parse_args()
    print(maximize(args.rows, args.columns, args.seed, args.time_limit,
                   args.relax))
