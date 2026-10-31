#!/usr/bin/env python3
"""Generate and exactly verify dual potentials for the 35/49 range bound.

For each output separation delta, the LP finds integer layer potentials p and
nonnegative integer edge budgets b satisfying

  unary_delta(c,t) <= b[i] + p[i-1,u] - p[i,t]

for every transition t <= u+1, with c=35*i mod 64. The certificate is rounded
and all inequalities are rechecked with Python integers before it is saved.
"""
from __future__ import annotations

import json
import math
import argparse
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


N = 64
HEIGHTS = N + 1
LAYERS = N
P_COUNT = N * HEIGHTS
VARIABLES = P_COUNT + LAYERS
PREVIOUS_SLOPE = 35
FINAL_SLOPE = 49
FINAL_INVERSE = pow(FINAL_SLOPE, -1, N)


def build_matrix():
    rows: list[int] = []
    cols: list[int] = []
    vals: list[float] = []
    for i in range(LAYERS):
        prev = (i - 1) % LAYERS
        for t in range(HEIGHTS):
            for u in range(max(0, t - 1), HEIGHTS):
                r = len(rows) // 3
                rows.extend((r, r, r))
                cols.extend((i * HEIGHTS + t,
                             prev * HEIGHTS + u,
                             P_COUNT + i))
                vals.extend((1.0, -1.0, -1.0))
    return coo_matrix((vals, (rows, cols)),
                      shape=(len(rows) // 3, VARIABLES)).tocsr()


def unary(delta: int, column: int, height: int) -> int:
    at_zero = FINAL_INVERSE * ((-column) % N) % N
    at_delta = FINAL_INVERSE * ((delta - column) % N) % N
    return int(at_zero < height) + int(height <= at_delta)


def verify(delta: int, potentials: list[list[int]], budgets: list[int]) -> None:
    assert len(potentials) == LAYERS
    assert all(len(row) == HEIGHTS for row in potentials)
    assert len(budgets) == LAYERS and all(b >= 0 for b in budgets)
    for i in range(LAYERS):
        column = PREVIOUS_SLOPE * i % N
        prev = (i - 1) % LAYERS
        for t in range(HEIGHTS):
            for u in range(max(0, t - 1), HEIGHTS):
                assert unary(delta, column, t) <= (
                    budgets[i] + potentials[prev][u] - potentials[i][t]
                ), (delta, i, t, u)


def main() -> None:
    global PREVIOUS_SLOPE, FINAL_SLOPE, FINAL_INVERSE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--previous-slope", type=int, default=35)
    parser.add_argument("--final-slope", type=int, default=49)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    PREVIOUS_SLOPE = args.previous_slope
    FINAL_SLOPE = args.final_slope
    if math.gcd(FINAL_SLOPE, N) != 1 or math.gcd(PREVIOUS_SLOPE, N) != 1:
        raise ValueError("both slopes must be coprime to64")
    FINAL_INVERSE = pow(FINAL_SLOPE, -1, N)
    matrix = build_matrix()
    cost = np.r_[np.zeros(P_COUNT), np.ones(LAYERS)]
    bounds = [(None, None)] * P_COUNT + [(0, None)] * LAYERS
    certificates = []
    worst_budget = 0
    for delta in range(N):
        rhs = []
        for i in range(LAYERS):
            column = PREVIOUS_SLOPE * i % N
            for t in range(HEIGHTS):
                for _u in range(max(0, t - 1), HEIGHTS):
                    rhs.append(-unary(delta, column, t))
        result = linprog(cost, A_ub=matrix, b_ub=np.asarray(rhs),
                         bounds=bounds, method="highs")
        if not result.success or result.x is None:
            raise RuntimeError(f"delta {delta}: {result.message}")
        rounded = np.rint(result.x).astype(np.int64)
        if np.max(np.abs(result.x - rounded)) > 1e-7:
            raise RuntimeError(f"delta {delta}: nonintegral LP solution")
        potentials = rounded[:P_COUNT].reshape(LAYERS, HEIGHTS).tolist()
        budgets = rounded[P_COUNT:].tolist()
        verify(delta, potentials, budgets)
        total = sum(budgets)
        if total > 128:
            raise RuntimeError(f"delta {delta}: unexpected budget {total} > 128")
        worst_budget = max(worst_budget, total)
        certificates.append({"delta": delta, "potentials": potentials,
                             "budgets": budgets})
        print(f"delta={delta:2} budget={total}")

    out = args.output or Path(__file__).with_name(
        f"d2_slope{FINAL_SLOPE}_potentials.json")
    out.write_text(json.dumps(certificates, separators=(",", ":")) + "\n",
                   encoding="utf-8")
    print(f"verified={len(certificates)} worst_budget={worst_budget}")
    print(f"certificate={out.name}")


if __name__ == "__main__":
    main()
