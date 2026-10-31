#!/usr/bin/env python3
"""Test whether a proposed slope-35 profile comes from a slope-1 output.

The source g must itself satisfy the necessary one-sided slope-1 gradient.
The target is indexed in the slope-35 layer coordinate d=35*layer. This is an
exact finite MILP feasibility check for a fixed profile, not a proof about all
profiles.
"""
import argparse
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

N = 64
DEFAULT = [8,9,10,10,10,10,10,11,12,13,14,15,16,17,18,19,20,21,22,23,
           24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,
           44,45,46,47,48,49,50,50,51,52,52,53,53,54,53,54,53,51,28,28,
           8,8,8,8]


def check(target, time_limit=120):
    if len(target) != N or any(v < 0 or v > N for v in target):
        raise ValueError("target must have64 heights in [0,64]")
    # x[c,k] is [sourceHeight[c] >= k], k=1,...,64.
    ix = lambda c, k: c * N + k - 1
    rows, lbs, ubs = [], [], []

    def add(terms, lb=-np.inf, ub=np.inf):
        rows.append({i: a for i, a in terms.items() if a})
        lbs.append(lb); ubs.append(ub)

    for c in range(N):
        for k in range(1, N):
            add({ix(c, k + 1): 1, ix(c, k): -1}, ub=0)
        prev = (c - 1) % N
        terms = {ix(c, k): 1 for k in range(1, N + 1)}
        for k in range(1, N + 1):
            terms[ix(prev, k)] = terms.get(ix(prev, k), 0) - 1
        add(terms, ub=1)

    inv35 = pow(35, -1, N)
    for layer, wanted in enumerate(target):
        dest = (35 * layer) % N
        terms = {}
        for c in range(N):
            threshold = (inv35 * (dest - c)) % N
            terms[ix(c, threshold + 1)] = 1
        add(terms, lb=wanted, ub=wanted)

    rr, cc, vv = [], [], []
    for r, row in enumerate(rows):
        for c, a in row.items():
            rr.append(r); cc.append(c); vv.append(a)
    A = coo_matrix((vv, (rr, cc)), shape=(len(rows), N * N)).tocsr()
    result = milp(np.zeros(N * N),
                  integrality=np.ones(N * N, dtype=np.uint8),
                  bounds=Bounds(0, 1),
                  constraints=LinearConstraint(A, lbs, ubs),
                  options={"time_limit": time_limit, "mip_rel_gap": 0.0})
    report = {"status": int(result.status), "message": result.message,
              "variables": N * N, "constraints": len(rows),
              "mip_gap": getattr(result, "mip_gap", None),
              "target_gradient": all(target[i] <= target[(i - 1) % N] + 1
                                      for i in range(N))}
    if result.x is not None:
        x = np.rint(result.x).astype(np.int64)
        source = [sum(x[ix(c, k)] for k in range(1, N + 1))
                  for c in range(N)]
        report["source"] = source
        report["source_gradient"] = all(
            source[i] <= source[(i - 1) % N] + 1 for i in range(N))
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", type=int, nargs=N, default=DEFAULT)
    parser.add_argument("--time-limit", type=float, default=120)
    args = parser.parse_args()
    print(json.dumps(check(args.profile, args.time_limit),
                     separators=(",", ":")), flush=True)
