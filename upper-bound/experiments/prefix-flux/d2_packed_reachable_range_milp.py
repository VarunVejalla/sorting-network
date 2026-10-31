#!/usr/bin/env python3
"""Exact MILP gate for the low-fringe packed-49 transition.

Inputs are arbitrary height profiles h[0..63] in [0,103] with the checked
one-sided slope-35 condition h[i] <= h[i-1]+1. The first 40 rows are sorted
and packed using the fixed offsets; the remaining active rows retain their
actual (possibly disconnected) column sets and use the physical slope-49
permutation. The model maximizes output range, not area, so a zero-gap range
at most 16 would certify the 4096-row dense-area allowance via Popoviciu.
"""
import argparse
import json

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


N = 64
OFFSETS = (0, 27, 42, 52, 58, 23, 38, 49, 20, 62, 18, 36, 16, 47,
           14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
           28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39)


class Model:
    def __init__(self):
        self.lb, self.ub, self.integrality, self.objective = [], [], [], []
        self.rows, self.row_lb, self.row_ub = [], [], []

    def var(self, lb=0, ub=1, integer=True, objective=0):
        i = len(self.lb)
        self.lb.append(lb); self.ub.append(ub)
        self.integrality.append(1 if integer else 0)
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


def solve(height_cap=103, time_limit=300, pair=None, relax=False):
    m = Model()
    # Unary source heights: x[c,k] = 1 iff h[c] >= k. This avoids one-hot
    # symmetry and makes every height-threshold row a direct linear form.
    x = [[m.var() for _ in range(height_cap)] for _ in range(N)]
    for c in range(N):
        for k in range(height_cap - 1):
            m.add({x[c][k + 1]: 1, x[c][k]: -1}, ub=0)
    for c in range(N):
        prev = (c - 1) % N
        terms = {x[c][k]: 1 for k in range(height_cap)}
        for k in range(height_cap):
            terms[x[prev][k]] = terms.get(x[prev][k], 0) - 1
        m.add(terms, ub=1)

    # q[r,k] = 1 iff the packed row width is at least k.
    q = [[m.var() for _ in range(N)] for _ in range(len(OFFSETS))]
    for r, row in enumerate(q):
        for k in range(N - 1):
            m.add({row[k + 1]: 1, row[k]: -1}, ub=0)
        terms = {v: 1 for v in row}
        for c in range(N):
            terms[x[c][r]] = terms.get(x[c][r], 0) - 1
        m.add(terms, lb=0, ub=0)

    # Exact output column heights: packed prefixes at top, actual source
    # membership under the ordinary cyclic map in every active middle row.
    z = [m.var(0, 104) for _ in range(N)]
    for d in range(N):
        terms = {z[d]: 1}
        for r, row in enumerate(q):
            distance = (d - OFFSETS[r]) % N
            terms[row[distance]] = terms.get(row[distance], 0) - 1
        for c in range(N):
            for k in range(1, height_cap + 1):
                row = k - 1
                if row >= len(OFFSETS) and (35 * c + 49 * row) % N == d:
                    terms[x[c][k - 1]] = terms.get(x[c][k - 1], 0) - 1
        m.add(terms, lb=0, ub=0)

    if pair is None:
        # Select actual maximum/minimum output columns; 104 bounds every load.
        maxv = m.var(0, 104, objective=-1)
        minv = m.var(0, 104, objective=1)
        smax = [m.var() for _ in range(N)]
        smin = [m.var() for _ in range(N)]
        m.add({v: 1 for v in smax}, lb=1, ub=1)
        m.add({v: 1 for v in smin}, lb=1, ub=1)
        M = 104
        for d in range(N):
            m.add({z[d]: 1, maxv: -1}, ub=0)
            m.add({maxv: 1, z[d]: -1, smax[d]: M}, ub=M)
            m.add({minv: 1, z[d]: -1}, ub=0)
            m.add({minv: 1, z[d]: -1, smin[d]: -M}, lb=-M)
    else:
        a, b = pair
        m.objective[z[a]] = -1
        m.objective[z[b]] = 1

    res = m.solve(time_limit, relax=relax)
    report = {"status": int(res.status), "message": res.message,
              "variables": len(m.lb), "constraints": len(m.rows),
              "mip_gap": getattr(res, "mip_gap", None),
              "dual_bound": getattr(res, "mip_dual_bound", None)}
    if res.fun is not None:
        report["objective_value"] = -float(res.fun)
    if pair is not None:
        bound = (-float(res.fun) if relax or int(res.status) == 0 else
                 (-float(res.mip_dual_bound)
                  if getattr(res, "mip_dual_bound", None) is not None else None))
        report["pair_difference_upper_bound"] = bound
    if res.x is not None and not relax:
        solution = np.rint(res.x).astype(np.int64)
        heights = [int(sum(solution[i] for i in row)) for row in x]
        out = [0] * N
        for r, row in enumerate(q):
            width = int(sum(solution[i] for i in row))
            for k in range(width):
                out[(OFFSETS[r] + k) % N] += 1
        for c, h in enumerate(heights):
            for r in range(40, h):
                out[(35 * c + 49 * r) % N] += 1
        range_value = (max(out) - min(out) if pair is None else
                       out[pair[0]] - out[pair[1]])
        report.update({"range_or_pair_difference": range_value,
                       "heights": heights,
                       "output": out, "one_sided_gradient": all(
                           heights[c] <= heights[(c - 1) % N] + 1
                           for c in range(N))})
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height-cap", type=int, default=103)
    parser.add_argument("--time-limit", type=float, default=300)
    parser.add_argument("--pair", type=int, nargs=2)
    parser.add_argument("--relax", action="store_true")
    args = parser.parse_args()
    print(json.dumps(solve(args.height_cap, args.time_limit,
                           None if args.pair is None else tuple(args.pair),
                           args.relax),
                     separators=(",", ":")), flush=True)
