#!/usr/bin/env python3
"""Exact range gate for reachable low-fringe (1,35,packed-49) profiles.

The model follows residue heights through two cyclic shuffles exactly. In the
low-fringe case, the common quotient after the second shuffle is at most39;
then the final 4096-row layer consists of packed rows0..39 and actual cyclic
subsets in rows40..102. It maximizes the final output range. A zero-gap
optimum <=16 would imply Aw<=2048 by Popoviciu. This is a finite local gate.
"""
import argparse
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

N, EDGE, CAP, KCAP = 64, 40, 103, 39
OFFSETS = (0, 27, 42, 52, 58, 23, 38, 49, 20, 62, 18, 36, 16, 47,
           14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
           28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39)


class Model:
    def __init__(self):
        self.lb, self.ub, self.integer, self.obj = [], [], [], []
        self.rows, self.lbs, self.ubs = [], [], []

    def var(self, lb=0, ub=1, objective=0):
        i = len(self.lb)
        self.lb.append(lb); self.ub.append(ub); self.integer.append(1)
        self.obj.append(objective)
        return i

    def add(self, terms, lb=-np.inf, ub=np.inf):
        self.rows.append({i: a for i, a in terms.items() if a})
        self.lbs.append(lb); self.ubs.append(ub)

    def solve(self, limit, relax=False):
        rr, cc, vv = [], [], []
        for r, row in enumerate(self.rows):
            for c, a in row.items():
                rr.append(r); cc.append(c); vv.append(a)
        A = coo_matrix((vv, (rr, cc)), shape=(len(self.rows), len(self.lb))).tocsr()
        return milp(np.asarray(self.obj, dtype=float),
                    integrality=(np.zeros(len(self.integer), dtype=np.uint8)
                                 if relax else
                                 np.asarray(self.integer, dtype=np.uint8)),
                    bounds=Bounds(self.lb, self.ub),
                    constraints=LinearConstraint(A, self.lbs, self.ubs),
                    options={"time_limit": limit, "mip_rel_gap": 0.0})


def solve(time_limit=300, pair=None, relax=False):
    m = Model()
    inv1, inv35 = 1, pow(35, -1, N)

    # Input residues t[j] in [0,63], unary u[j,r]=[t[j]>r].
    u = [[m.var() for _ in range(N - 1)] for _ in range(N)]
    for j in range(N):
        for r in range(N - 2):
            m.add({u[j][r + 1]: 1, u[j][r]: -1}, ub=0)
    q0 = m.var(0, N - 1)
    R = [m.var(0, N) for _ in range(N)]
    for c in range(N):
        terms = {R[c]: 1}
        for j in range(N):
            r = (inv1 * (c - j)) % N
            if r < N - 1:
                terms[u[j][r]] = -1
        m.add(terms, lb=0, ub=0)

    # Second-round input s[c]=(q0+R[c]) mod64, k[c] records its carry.
    s = [m.var(0, N - 1) for _ in range(N)]
    k = [m.var(0, 1) for _ in range(N)]
    carry = m.var(0, KCAP)
    m.add({carry: 1, **{v: -1 for v in k}}, lb=0, ub=0)
    for c in range(N):
        m.add({s[c]: 1, q0: -1, R[c]: -1, k[c]: N}, lb=0, ub=0)

    # Unary second-round residues and physical output S[d] in [0,64].
    w = [[m.var() for _ in range(N - 1)] for _ in range(N)]
    for c in range(N):
        m.add({s[c]: 1, **{w[c][r]: -1 for r in range(N - 1)}}, lb=0, ub=0)
        for r in range(N - 2):
            m.add({w[c][r + 1]: 1, w[c][r]: -1}, ub=0)
    S = [m.var(0, N) for _ in range(N)]
    for d in range(N):
        terms = {S[d]: 1}
        for c in range(N):
            r = (inv35 * (d - c)) % N
            if r < N - 1:
                terms[w[c][r]] = -1
        m.add(terms, lb=0, ub=0)

    # Absolute final heights h[d]=carry+S[d], capped at103 automatically.
    h = [m.var(0, CAP) for _ in range(N)]
    x = [[m.var() for _ in range(CAP)] for _ in range(N)]
    for d in range(N):
        m.add({h[d]: 1, carry: -1, S[d]: -1}, lb=0, ub=0)
        m.add({h[d]: 1, **{v: -1 for v in x[d]}}, lb=0, ub=0)
        for r in range(CAP - 1):
            m.add({x[d][r + 1]: 1, x[d][r]: -1}, ub=0)

    # Packed edge row widths q[r,k]=[width(row r)>=k].
    a = [[m.var() for _ in range(N)] for _ in range(EDGE)]
    for r in range(EDGE):
        for j in range(N - 1):
            m.add({a[r][j + 1]: 1, a[r][j]: -1}, ub=0)
        terms = {v: 1 for v in a[r]}
        for d in range(N):
            terms[x[d][r]] = terms.get(x[d][r], 0) - 1
        m.add(terms, lb=0, ub=0)

    z = [m.var(0, 104) for _ in range(N)]
    for d in range(N):
        terms = {z[d]: 1}
        for r in range(EDGE):
            distance = (d - OFFSETS[r]) % N
            terms[a[r][distance]] = terms.get(a[r][distance], 0) - 1
        for c in range(N):
            for r in range(EDGE, CAP):
                if (c + 49 * r) % N == d:
                    terms[x[c][r]] = terms.get(x[c][r], 0) - 1
        m.add(terms, lb=0, ub=0)

    if pair is None:
        maxv = m.var(0, 104, objective=-1)
        minv = m.var(0, 104, objective=1)
        hi = [m.var() for _ in range(N)]
        lo = [m.var() for _ in range(N)]
        m.add({v: 1 for v in hi}, lb=1, ub=1)
        m.add({v: 1 for v in lo}, lb=1, ub=1)
        M = 104
        for d in range(N):
            m.add({z[d]: 1, maxv: -1}, ub=0)
            m.add({maxv: 1, z[d]: -1, hi[d]: M}, ub=M)
            m.add({minv: 1, z[d]: -1}, ub=0)
            m.add({minv: 1, z[d]: -1, lo[d]: -M}, lb=-M)
    else:
        p, q = pair
        m.obj[z[p]] = -1
        m.obj[z[q]] = 1

    res = m.solve(time_limit, relax=relax)
    result = {"status": int(res.status), "message": res.message,
              "variables": len(m.lb), "constraints": len(m.rows),
              "mip_gap": getattr(res, "mip_gap", None),
              "dual_bound": getattr(res, "mip_dual_bound", None),
              "objective": getattr(res, "fun", None)}
    if res.fun is not None and pair is not None:
        result["pair_difference_upper_bound"] = -float(res.fun) if relax else None
    if res.x is not None and not relax:
        v = np.rint(res.x).astype(np.int64)
        heights = [int(v[i]) for i in h]
        output = [int(v[i]) for i in z]
        result.update({"range_or_pair": (max(output) - min(output)
                                          if pair is None else
                                          output[pair[0]] - output[pair[1]]),
                       "carry": int(v[carry]), "heights": heights,
                       "output": output})
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--time-limit", type=float, default=300)
    p.add_argument("--pair", type=int, nargs=2)
    p.add_argument("--relax", action="store_true")
    args = p.parse_args()
    print(json.dumps(solve(args.time_limit,
                           None if args.pair is None else tuple(args.pair),
                           args.relax),
                     separators=(",", ":")), flush=True)
