#!/usr/bin/env python3
"""Maximize output range for the reduced cyclic two-scramble map.

Unlike ``d2_cyclic_variance_milp.py``, this uses a linear objective. A proof
that the output range is at most R immediately gives
Aw/n <= R^2/8, so R<=19 would imply the proposed Gamma=48 cap.
"""
import argparse
from math import gcd

from d2_cyclic_variance_milp import Model


def solve(n=64, a=1, b=35, offset=17, time_limit=300, min_range=0,
          third_slope=None, third_offset=0, delta=None,
          relax_integrality=False):
    slopes = [a, b] + ([] if third_slope is None else [third_slope])
    if any(gcd(slope, n) != 1 for slope in slopes):
        raise ValueError("all slopes must be coprime to the column count")
    inv_a, inv_b = pow(a, -1, n), pow(b, -1, n)
    m = Model()
    u = [[m.var() for _ in range(n - 1)] for _ in range(n)]
    for j in range(n):
        for r in range(n - 2):
            m.le({u[j][r + 1]: 1, u[j][r]: -1})
    q = m.var(0, n - 1)
    k = [m.var() for _ in range(n)]
    s = [m.var(0, n - 1) for _ in range(n)]
    for c in range(n):
        equation = {s[c]: 1, q: -1, k[c]: n}
        for j in range(n):
            r = (inv_a * (c - j)) % n
            if r < n - 1:
                equation[u[j][r]] = equation.get(u[j][r], 0) - 1
        m.eq(equation)

    w = [[m.var() for _ in range(n - 1)] for _ in range(n)]
    for c in range(n):
        equation = {s[c]: 1}
        equation.update({w[c][r]: -1 for r in range(n - 1)})
        m.eq(equation)
        for r in range(n - 2):
            m.le({w[c][r + 1]: 1, w[c][r]: -1})
    S = [m.var(0, n) for _ in range(n)]
    for d in range(n):
        equation = {S[d]: 1}
        for c in range(n):
            r = (inv_b * (d - c - offset)) % n
            if r < n - 1:
                equation[w[c][r]] = equation.get(w[c][r], 0) - 1
        m.eq(equation)

    profile = S
    if third_slope is not None:
        inv_c = pow(third_slope, -1, n)
        # The second-round common quotient is the sum of the first-round
        # quotients k[c]. Its residue affects the third-round shuffle.
        second_base = m.var(0, n)
        m.eq({second_base: 1, **{v: -1 for v in k}})
        third_q = [m.var(0, 2) for _ in range(n)]
        third_residue = [m.var(0, n - 1) for _ in range(n)]
        for d in range(n):
            m.eq({third_residue[d]: 1, third_q[d]: n,
                  second_base: -1, S[d]: -1})
        third_unary = [[m.var() for _ in range(n - 1)] for _ in range(n)]
        for d in range(n):
            m.eq({third_residue[d]: 1,
                  **{third_unary[d][r]: -1 for r in range(n - 1)}})
            for r in range(n - 2):
                m.le({third_unary[d][r + 1]: 1,
                      third_unary[d][r]: -1})
        profile = [m.var(0, n) for _ in range(n)]
        for e in range(n):
            equation = {profile[e]: 1}
            for d in range(n):
                r = (inv_c * (e - d - third_offset)) % n
                if r < n - 1:
                    equation[third_unary[d][r]] = -1
            m.eq(equation)

    # Rotation invariance lets the high endpoint be wire 0. Select the other
    # endpoint delta and maximize S[0]-S[delta].
    radius = m.var(min_range, n, objective=(-1 if min_range == 0 else 0))
    if delta is not None:
        if not 1 <= delta < n:
            raise ValueError("delta must be in 1,...,n-1")
        # Rotation equivariance lets the high endpoint be fixed at0.
        m.le({radius: 1, profile[0]: -1, profile[delta]: 1}, 0)
    else:
        choose = [m.var() for _ in range(n - 1)]
        m.eq({v: 1 for v in choose}, 1)
        for delta, selected in enumerate(choose, start=1):
            # radius <= profile[0]-profile[delta] + n*(1-selected)
            m.le({radius: 1, profile[0]: -1, profile[delta]: 1,
                  selected: n}, n)

    if relax_integrality:
        m.integrality = [0] * len(m.integrality)
    result = m.solve(time_limit)
    report = {"n": n, "a": a, "b": b, "offset": offset,
              "third_slope": third_slope,
              "third_offset": third_offset, "delta": delta,
              "relaxed": relax_integrality,
              "variables": len(m.lb), "constraints": len(m.rows),
              "status": int(result.status), "message": result.message,
              "mip_gap": getattr(result, "mip_gap", None),
              "dual_bound": getattr(result, "mip_dual_bound", None),
              "objective_value": getattr(result, "fun", None),
              "max_range_upper_bound": (
                  -float(result.mip_dual_bound)
                  if min_range == 0 and
                  getattr(result, "mip_dual_bound", None) is not None
                  else (-float(result.fun)
                        if relax_integrality and int(result.status) == 0 and
                        min_range == 0 and result.fun is not None else None))}
    if result.x is not None and not relax_integrality:
        x = result.x.round().astype(int)
        residues = [sum(x[u[j][r]] for r in range(n - 1))
                    for j in range(n)]
        qv = int(x[q])
        R = [sum(((inv_a * (c - j)) % n) < residues[j]
                 for j in range(n)) for c in range(n)]
        sv = [(qv + value) % n for value in R]
        second_profile = [sum(((inv_b * (d - c - offset)) % n) < sv[c]
                              for c in range(n)) for d in range(n)]
        if third_slope is None:
            final_profile = second_profile
        else:
            second_base_value = sum((qv + value) // n for value in R)
            third_residue_values = [
                (second_base_value + value) % n for value in second_profile]
            inv_c = pow(third_slope, -1, n)
            final_profile = [sum(
                ((inv_c * (e - d - third_offset)) % n) <
                third_residue_values[d] for d in range(n))
                for e in range(n)]
        actual_range = max(final_profile) - min(final_profile)
        report.update({"primal_radius": int(x[radius]),
                       "recomputed_range": actual_range,
                       "residue_q": qv,
                       "input_residues": residues,
                       "output_profile": final_profile,
                       "primal_matches": actual_range == int(x[radius])})
    return report


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--first-slope", type=int, default=1)
    ap.add_argument("--second-slope", type=int, default=35)
    ap.add_argument("--second-offset", type=int, default=17)
    ap.add_argument("--third-slope", type=int,
                    help="include a third cyclic round")
    ap.add_argument("--third-offset", type=int, default=0)
    ap.add_argument("--delta", type=int,
                    help="fix the low endpoint delta from the high endpoint")
    ap.add_argument("--relax-integrality", action="store_true",
                    help="solve the LP relaxation for a rigorous upper bound")
    ap.add_argument("--time-limit", type=float, default=300)
    ap.add_argument("--require-range", type=int, default=0,
                    help="feasibility gate: require an output range at least this large")
    args = ap.parse_args()
    print(solve(args.columns, args.first_slope, args.second_slope,
                args.second_offset, args.time_limit,
                args.require_range, args.third_slope,
                args.third_offset, args.delta,
                args.relax_integrality), flush=True)
