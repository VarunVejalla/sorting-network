#!/usr/bin/env python3
"""Exact MILP for area over low-fringe one-sided-gradient profiles.

The transition sorts/packs only the first40 rows; middle rows use each actual
column's active bit under slope49. The profile class is h in [0,103] with
h[i] <= h[i-1]+1. Integer one-hot products encode the exact quadratic area.
This is a finite provider gate, not an all-depth sorting proof.
"""
import argparse
import json
import math

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

N = 64
EDGE = 40
CAP = 103
OFFSETS = (0, 27, 42, 52, 58, 23, 38, 49, 20, 62, 18, 36, 16, 47,
           14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
           28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39)


class Model:
    def __init__(self):
        self.lb, self.ub, self.integrality, self.objective = [], [], [], []
        self.rows, self.row_lb, self.row_ub = [], [], []

    def var(self, lb=0, ub=1, objective=0):
        i = len(self.lb)
        self.lb.append(lb); self.ub.append(ub)
        self.integrality.append(1)
        self.objective.append(objective)
        return i

    def add(self, terms, lb=-np.inf, ub=np.inf):
        self.rows.append({i: c for i, c in terms.items() if c})
        self.row_lb.append(lb); self.row_ub.append(ub)

    def solve(self, time_limit, relax=False):
        rr, cc, data = [], [], []
        for r, row in enumerate(self.rows):
            for c, value in row.items():
                rr.append(r); cc.append(c); data.append(value)
        mat = coo_matrix((data, (rr, cc)),
                         shape=(len(self.rows), len(self.lb))).tocsr()
        return milp(np.asarray(self.objective, dtype=float),
                    integrality=(np.zeros(len(self.integrality), dtype=np.uint8)
                                 if relax else
                                 np.asarray(self.integrality, dtype=np.uint8)),
                    bounds=Bounds(self.lb, self.ub),
                    constraints=LinearConstraint(mat, self.row_lb,
                                                 self.row_ub),
                    options={"time_limit": time_limit, "mip_rel_gap": 0.0})


def encode_square(m, value, upper, objective_sign):
    """Add binary expansion and exact AND products; return square bits."""
    bits = math.ceil(math.log2(upper + 1))
    b = [m.var(objective=objective_sign * (1 << (2 * i)))
         for i in range(bits)]
    m.add({value: 1, **{v: -(1 << i) for i, v in enumerate(b)}}, lb=0, ub=0)
    square_terms = {b[i]: 1 << (2 * i) for i in range(bits)}
    for i in range(bits):
        for j in range(i + 1, bits):
            p = m.var(objective=objective_sign * (1 << (i + j + 1)))
            m.add({p: 1, b[i]: -1}, ub=0)
            m.add({p: 1, b[j]: -1}, ub=0)
            m.add({p: 1, b[i]: -1, b[j]: -1}, lb=-1)
            square_terms[p] = 1 << (i + j + 1)
    return square_terms


def solve(time_limit=300, relax=False):
    m = Model()
    # x[c,k] = [h[c] >= k], a compact exact unary encoding.
    x = [[m.var() for _ in range(CAP)] for _ in range(N)]
    for c in range(N):
        for k in range(CAP - 1):
            m.add({x[c][k + 1]: 1, x[c][k]: -1}, ub=0)
    for c in range(N):
        prev = (c - 1) % N
        terms = {x[c][k]: 1 for k in range(CAP)}
        for k in range(CAP):
            terms[x[prev][k]] = terms.get(x[prev][k], 0) - 1
        m.add(terms, ub=1)

    # q[r,k] = [width of packed row r >= k].
    q = [[m.var() for _ in range(N)] for _ in range(EDGE)]
    for r in range(EDGE):
        for k in range(N - 1):
            m.add({q[r][k + 1]: 1, q[r][k]: -1}, ub=0)
        terms = {v: 1 for v in q[r]}
        for c in range(N):
            terms[x[c][r]] = terms.get(x[c][r], 0) - 1
        m.add(terms, lb=0, ub=0)

    z = [m.var(0, 104) for _ in range(N)]
    for d in range(N):
        terms = {z[d]: 1}
        for r in range(EDGE):
            dist = (d - OFFSETS[r]) % N
            terms[q[r][dist]] = terms.get(q[r][dist], 0) - 1
        for c in range(N):
            for k in range(EDGE + 1, CAP + 1):
                row = k - 1
                if (35 * c + 49 * row) % N == d:
                    terms[x[c][k - 1]] = terms.get(x[c][k - 1], 0) - 1
        m.add(terms, lb=0, ub=0)

    # Exact integer mass conservation and binary expansions for the square.
    mass = m.var(0, CAP * N)
    total_terms = {mass: 1}
    for c in range(N):
        for k in range(CAP):
            total_terms[x[c][k]] = total_terms.get(x[c][k], 0) - 1
    m.add(total_terms, lb=0, ub=0)

    # Minimize -F, where F=64*sum(z_d^2)-mass^2=128*Aw.
    for d in range(N):
        encode_square(m, z[d], 104, objective_sign=-64)
    encode_square(m, mass, CAP * N, objective_sign=1)

    result = m.solve(time_limit, relax=relax)
    report = {"status": int(result.status), "message": result.message,
              "variables": len(m.lb), "constraints": len(m.rows),
              "mip_gap": getattr(result, "mip_gap", None),
              "dual_bound": getattr(result, "mip_dual_bound", None),
              "objective_value": getattr(result, "fun", None)}
    if result.fun is not None:
        report["area_upper_bound_from_objective"] = -float(result.fun) / 128
    if result.x is not None and not relax:
        values = np.rint(result.x).astype(np.int64)
        heights = [sum(values[i] for i in row) for row in x]
        output = [int(values[i]) for i in z]
        actual_mass = sum(heights)
        area = 0.5 * (sum(v * v for v in output) - actual_mass**2 / N)
        report.update({"Aw": area, "Aw_per_column": area / N,
                       "output_range": max(output) - min(output),
                       "heights": heights, "output": output,
                       "gradient_valid": all(
                           heights[c] <= heights[(c - 1) % N] + 1
                           for c in range(N))})
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--time-limit", type=float, default=300)
    parser.add_argument("--relax", action="store_true")
    args = parser.parse_args()
    print(json.dumps(solve(args.time_limit, args.relax), separators=(",", ":")),
          flush=True)
