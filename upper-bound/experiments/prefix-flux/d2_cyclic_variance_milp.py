#!/usr/bin/env python3
"""Exact finite MILP screen for two periodic row-cyclic shuffles.

For coprime slopes a,b modulo n, an n-row cycle sends height vector x to
Q+R, where Q=sum floor(x_j/n), t_j=x_j mod n, and
R_c=sum_j [((c-j)*a^{-1} mod n) < t_j]. A second cycle depends only on
Q mod n and R mod n. Thus this model maximizes the final column variance
over every residue profile and every possible Q mod n. It is an integer
optimization certificate only when the solver proves a zero-gap optimum;
the returned primal is independently re-evaluated below.
"""
import argparse
from math import gcd

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


class Model:
    def __init__(self):
        self.lb = []
        self.ub = []
        self.integrality = []
        self.objective = []
        self.rows = []
        self.row_lb = []
        self.row_ub = []

    def var(self, lb=0, ub=1, integer=True, objective=0):
        i = len(self.lb)
        self.lb.append(lb); self.ub.append(ub)
        self.integrality.append(1 if integer else 0)
        self.objective.append(objective)
        return i

    def eq(self, terms, rhs=0):
        self.rows.append({i: c for i, c in terms.items() if c})
        self.row_lb.append(rhs); self.row_ub.append(rhs)

    def le(self, terms, rhs=0):
        self.rows.append({i: c for i, c in terms.items() if c})
        self.row_lb.append(-np.inf); self.row_ub.append(rhs)

    def solve(self, time_limit):
        rr, cc, data = [], [], []
        for r, row in enumerate(self.rows):
            for c, value in row.items():
                rr.append(r); cc.append(c); data.append(value)
        mat = coo_matrix((data, (rr, cc)),
                         shape=(len(self.rows), len(self.lb))).tocsr()
        return milp(
            np.asarray(self.objective, dtype=float),
            integrality=np.asarray(self.integrality, dtype=np.uint8),
            bounds=Bounds(self.lb, self.ub),
            constraints=LinearConstraint(mat, self.row_lb, self.row_ub),
            options={"time_limit": time_limit, "mip_rel_gap": 0.0})


def solve(n=64, a=1, b=35, time_limit=300):
    if gcd(a, n) != 1 or gcd(b, n) != 1:
        raise ValueError("both slopes must be coprime to the column count")
    inv_a, inv_b = pow(a, -1, n), pow(b, -1, n)
    m = Model()

    # u[j,r] = [t_j > r], for t_j in {0,...,n-1}.
    u = [[m.var() for _ in range(n - 1)] for _ in range(n)]
    for j in range(n):
        for r in range(n - 2):
            m.le({u[j][r + 1]: 1, u[j][r]: -1})

    q = m.var(0, n - 1)
    k = [m.var() for _ in range(n)]
    s = [m.var(0, n - 1) for _ in range(n)]
    R = []
    for c in range(n):
        terms = {u[j][(inv_a * (c - j)) % n]: 1
                 for j in range(n) if (inv_a * (c - j)) % n < n - 1}
        R.append(terms)
        equation = {s[c]: 1, q: -1, k[c]:  n}
        for i, coefficient in terms.items():
            equation[i] = equation.get(i, 0) - coefficient
        m.eq(equation)

    # w[c,r] = [s_c > r]. Then S_d is the second cyclic interval sum.
    w = [[m.var() for _ in range(n - 1)] for _ in range(n)]
    for c in range(n):
        m.eq({s[c]: 1, **{w[c][r]: -1 for r in range(n - 1)}})
        for r in range(n - 2):
            m.le({w[c][r + 1]: 1, w[c][r]: -1})

    # One-hot output counts linearize the exact quadratic variance:
    # 2*n*Aw = n*sum(S_d^2) - (sum S_d)^2.
    S = []
    output_onehot = []
    for d in range(n):
        terms = {}
        for c in range(n):
            r = (inv_b * (d - c)) % n
            if r < n - 1:
                terms[w[c][r]] = terms.get(w[c][r], 0) - 1
        S.append(m.var(0, n))
        m.eq({S[d]: 1, **terms})
        hot = [m.var(objective=-n * value * value)
               for value in range(n + 1)]
        output_onehot.append(hot)
        m.eq({**{v: 1 for v in hot}} , 1)
        count_eq = {S[d]: 1}
        for value, v in enumerate(hot):
            count_eq[v] = -value
        m.eq(count_eq)

    total = m.var(0, n * n)
    total_hot = [m.var(objective=value * value)
                 for value in range(n * n + 1)]
    m.eq({**{v: 1 for v in total_hot}}, 1)
    total_eq = {total: 1}
    for value, v in enumerate(total_hot):
        total_eq[v] = -value
    m.eq(total_eq)
    sum_eq = {total: 1}
    for v in S:
        sum_eq[v] = -1
    m.eq(sum_eq)

    result = m.solve(time_limit)
    report = {"n": n, "a": a, "b": b, "variables": len(m.lb),
              "constraints": len(m.rows), "status": int(result.status),
              "message": result.message,
              "mip_gap": getattr(result, "mip_gap", None),
              "dual_bound": getattr(result, "mip_dual_bound", None)}
    if result.x is not None:
        x = np.rint(result.x).astype(np.int64)
        t = [sum(x[u[j][r]] for r in range(n - 1)) for j in range(n)]
        qr = int(x[q])
        Rv = [sum(((inv_a * (c - j)) % n) < t[j]
                  for j in range(n)) for c in range(n)]
        sv = [(qr + value) % n for value in Rv]
        Sv = [sum(((inv_b * (d - c)) % n) < sv[c]
                  for c in range(n)) for d in range(n)]
        T = sum(Sv)
        objective = n * sum(value * value for value in Sv) - T * T
        report.update({"residue_q": qr, "Aw_times_2n": objective,
                       "Aw": objective / (2 * n),
                       "Aw_per_column": objective / (2 * n * n),
                       "output_range": max(Sv) - min(Sv),
                       "input_residues": t, "output_residues": Sv,
                       "exact_primal_objective_matches":
                           abs(float(result.fun) + objective) < 1e-5})
    return report


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--first-slope", type=int, default=1)
    ap.add_argument("--second-slope", type=int, default=35)
    ap.add_argument("--time-limit", type=float, default=300)
    args = ap.parse_args()
    print(solve(args.columns, args.first_slope, args.second_slope,
                args.time_limit), flush=True)
