#!/usr/bin/env python3
"""Exact quotient LP for the local-profile D2 port-flow relaxation.

The quotient is formed by equitable refinement of the time-layered address
graph. A class keeps identical local sender polytopes and identical labeled
port incidence to neighboring classes. Summing the member LPs is then exact
for this relaxation. Ordered global-prefix constraints are deliberately not
included. By default the root has only its exact threshold mass, not a sorted
profile. ``--sorted-root`` retains the older, optimistic fixed-point
diagnostic; ``--compare-raw`` compares only against that sorted-root model.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
import argparse

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from flow_dag import FlowDAG
from first_column import minimum_rectangular_prefix_zeros
from oracle import Par
from profile_cut_closure import occupied_bag_keys, rank_before
from rank_recurrence import prefix_interval, run as run_history


def address_shell(index, spine, k, level):
    if index == spine:
        return ("spine",)
    ds = [(index // k**p) % k for p in range(level - 1, -1, -1)]
    qs = [(spine // k**p) % k for p in range(level - 1, -1, -1)]
    split = next(j for j, (a, b) in enumerate(zip(ds, qs)) if a != b)
    return (split, -1 if index < spine else 1, ds[split] - qs[split])


def build(depth=5, scale=8192, row_count=8192, params=(3, 3, 2),
          time_limit=120, compare_raw=False, distance_tail_profile=(),
          sorted_root=False):
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    T = len(flow.rows)
    N = p.k**depth * scale
    q = N // 3
    _, history = run_history(depth, scale, F(1, 3), include_history=True,
                             params=params, row_count=row_count)

    bag_keys = sorted({key for t in range(T + 1)
                       for key in occupied_bag_keys(flow, t)})
    vertices = [(t, lev, idx) for t in range(T + 1)
                for lev, idx in bag_keys]
    vertex_set = set(vertices)

    node = {}
    h_bounds = {}
    shell = {}
    profile = {}
    base = {}
    for v in vertices:
        t, lev, idx = v
        state = flow.lookup(t, lev, idx)
        a = flow.allocation(state)
        hlo, hhi = history[t].get((lev, idx), (0, 0))
        hlo, hhi = max(0, hlo), min(a, hhi)
        node[v] = state
        h_bounds[v] = (hlo, hhi)
        sh = address_shell(idx, q // flow.native(lev), p.k, lev)
        shell[v] = sh

        row = flow.rows[t].get(state) if t < T else None
        active = row is not None and (lev == 0 if t == 0 else p.active(depth, lev, t))
        pdata = None
        if active:
            a, pi, blocks = row
            if pi < a:
                h = pi // 2
                cuts = sorted(set([0, h, a] +
                                  [h + sum(blocks[:j])
                                   for j in range(1, len(blocks) + 1)]))
                y_bounds = []
                for cut in cuts:
                    ylo, yhi = prefix_interval(a, (hlo, hhi), cut, row_count)
                    if a and a % row_count == 0:
                        columns = a // row_count
                        row_cut = (cut // columns) * columns
                        ylo = max(ylo, minimum_rectangular_prefix_zeros(
                            a, hlo, row_cut, rows=row_count))
                    # The root has exactly q threshold zeros, but arbitrary
                    # inputs do not place them in sorted order. Keep the
                    # certified local prefix interval unless explicitly
                    # running the legacy sorted-root diagnostic.
                    if sorted_root and t == 0 and (lev, idx) == (0, 0):
                        ylo = yhi = min(q, cut)
                    y_bounds.append((ylo, yhi))
                pdata = (a, pi, tuple(blocks), tuple(cuts), tuple(y_bounds))
        terminal_kind = 0
        if t == T and a:
            wires = flow.bag_intervals(state, idx)
            before = rank_before(wires, q)
            terminal_kind = 1 if before == a else (-1 if before == 0 else 0)
        profile[v] = pdata
        # This base label makes all member local polytopes and objective
        # coefficients identical. Flow state includes exact block geometry.
        base[v] = (t, lev, state, sh, (hlo, hhi), pdata, terminal_kind)

    out_edges = {v: [] for v in vertices}
    in_edges = {v: [] for v in vertices}

    def add_edge(src, dst, label):
        if dst not in vertex_set:
            return
        out_edges[src].append((label, dst))
        in_edges[dst].append((label, src))

    for t in range(T):
        row = flow.rows[t]
        for lev, idx in bag_keys:
            src = (t, lev, idx)
            state = node[src]
            rdata = row.get(state)
            active = rdata is not None and (lev == 0 if t == 0 else p.active(depth, lev, t))
            if not active:
                add_edge(src, (t + 1, lev, idx), ("carry",))
                continue
            a, pi, blocks = rdata
            if lev > 0:
                parent = (t + 1, lev - 1, idx // p.k)
                if pi == a:
                    if a:
                        add_edge(src, parent, ("allH",))
                elif pi:
                    h = pi // 2
                    ports = tuple((lo, hi) for lo, hi in ((0, h), (a - h, a))
                                  if lo < hi)
                    if ports:
                        add_edge(src, parent, ("ports", ports))
            if pi < a:
                h = pi // 2
                pos = h
                for j, width in enumerate(blocks):
                    if width:
                        add_edge(src, (t + 1, lev + 1, idx * p.k + j),
                                 ("ports", ((pos, pos + width),)))
                    pos += width

    # Equitable partition refinement: same base type and the same labeled
    # incoming/outgoing class multiset. This makes class-level port equations
    # exactly the sums of the uncompressed per-address equations.
    def intern(values):
        ids = {}
        colors = {}
        for v in vertices:
            key = values(v)
            if key not in ids:
                ids[key] = len(ids)
            colors[v] = ids[key]
        return colors

    colors = intern(lambda v: base[v])
    iterations = 0
    while True:
        iterations += 1
        def signature(v):
            outgoing = tuple(sorted(((repr(label), colors[dst])
                                     for label, dst in out_edges[v])))
            incoming = tuple(sorted(((repr(label), colors[src])
                                     for label, src in in_edges[v])))
            return colors[v], outgoing, incoming
        refined = intern(signature)
        if len(set(refined.values())) == len(set(colors.values())):
            colors = refined
            break
        colors = refined
        if iterations > len(vertices):
            raise RuntimeError("partition refinement failed to stabilize")

    members = defaultdict(list)
    for v, color in colors.items():
        members[color].append(v)
    representatives = {color: group[0] for color, group in members.items()}

    # Assert every class has exactly the representative's labeled incidence.
    for color, group in members.items():
        rep = representatives[color]
        rep_out = Counter((label, colors[dst]) for label, dst in out_edges[rep])
        rep_in = Counter((label, colors[src]) for label, src in in_edges[rep])
        for v in group[1:]:
            assert Counter((label, colors[dst]) for label, dst in out_edges[v]) == rep_out
            assert Counter((label, colors[src]) for label, src in in_edges[v]) == rep_in

    var_bounds = []
    var = {}

    def new(key, bounds):
        var[key] = len(var_bounds)
        var_bounds.append(bounds)
        return var[key]

    H = {}
    Y = {}
    for color, group in members.items():
        rep = representatives[color]
        hlo, hhi = h_bounds[rep]
        mult = len(group)
        H[color] = new(("H", color), (mult * hlo, mult * hhi))
        pdata = profile[rep]
        if pdata is not None:
            _, _, _, cuts, bounds = pdata
            for cut, (ylo, yhi) in zip(cuts, bounds):
                Y[(color, cut)] = new(("Y", color, cut),
                                      (mult * ylo, mult * yhi))

    eq_rows, eq_rhs, ub_rows, ub_rhs = [], [], [], []
    tail_constraint_count = 0

    def add(rows, rhs, terms, value=0):
        rows.append({i: c for i, c in terms.items() if c})
        rhs.append(value)

    # Sum every local sender polytope over its class.
    for color, group in members.items():
        rep = representatives[color]
        pdata = profile[rep]
        if pdata is None:
            continue
        a, pi, blocks, cuts, _ = pdata
        mult = len(group)
        y = {cut: Y[(color, cut)] for cut in cuts}
        add(eq_rows, eq_rhs, {y[cuts[0]]: 1})
        add(eq_rows, eq_rhs, {y[cuts[-1]]: 1, H[color]: -1})
        for left, right in zip(cuts, cuts[1:]):
            width = right - left
            add(ub_rows, ub_rhs, {y[left]: 1, y[right]: -1}, 0)
            add(ub_rows, ub_rhs, {y[right]: 1, y[left]: -1}, width * mult)

        if distance_tail_profile and a and a % row_count == 0:
            columns = a // row_count
            hlo, hhi = h_bounds[rep]
            for cut in cuts:
                if cut == 0 or cut == a or cut % columns:
                    continue
                if hhi < cut:
                    distance = (cut - hhi) // columns
                    terms = {H[color]: 1, y[cut]: -1}
                elif hlo > cut:
                    distance = (hlo - cut) // columns
                    terms = {y[cut]: -1}
                else:
                    continue
                eligible = [(r, cap) for r, cap in distance_tail_profile
                            if r <= distance]
                if eligible:
                    _, cap = eligible[-1]
                    add(ub_rows, ub_rhs, terms, float(cap * a * mult))
                    tail_constraint_count += 1

    # Sum the exact port-flow equation for each destination class.
    incoming_by_dest = defaultdict(list)
    for source_color, group in members.items():
        rep = representatives[source_color]
        edge_counts = Counter((label, colors[dst])
                              for label, dst in out_edges[rep])
        for (label, dest_color), edge_mult in edge_counts.items():
            incoming_by_dest[dest_color].append((source_color, label, edge_mult))
    for dest_color in members:
        if representatives[dest_color][0] == 0:
            continue
        terms = {H[dest_color]: 1}
        for source_color, label, edge_mult in incoming_by_dest[dest_color]:
            if label == ("carry",) or label == ("allH",):
                terms[H[source_color]] = terms.get(H[source_color], 0) - edge_mult
                continue
            kind, ports = label
            assert kind == "ports" and profile[representatives[source_color]] is not None
            for left, right in ports:
                terms[Y[(source_color, right)]] = terms.get(Y[(source_color, right)], 0) - edge_mult
                terms[Y[(source_color, left)]] = terms.get(Y[(source_color, left)], 0) + edge_mult
        add(eq_rows, eq_rhs, terms)

    # Terminal wrong mass, counting only wholly one-colored target blocks.
    objective = np.zeros(len(var_bounds))
    constant = 0
    for color, group in members.items():
        rep = representatives[color]
        if rep[0] != T:
            continue
        kind = base[rep][-1]
        a = flow.allocation(node[rep])
        if kind == 1:
            objective[H[color]] -= 1
            constant += len(group) * a
        elif kind == -1:
            objective[H[color]] += 1

    nvars = len(var_bounds)
    def to_sparse(rows):
        rr, cc, data = [], [], []
        for i, row in enumerate(rows):
            for j, val in row.items():
                rr.append(i); cc.append(j); data.append(float(val))
        return coo_matrix((data, (rr, cc)), shape=(len(rows), nvars)).tocsr()
    Aub, Aeq = to_sparse(ub_rows), to_sparse(eq_rows)
    result = linprog(-objective, A_ub=Aub, b_ub=np.asarray(ub_rhs),
                     A_eq=Aeq, b_eq=np.asarray(eq_rhs),
                     bounds=var_bounds, method="highs",
                     options={"time_limit": time_limit})
    out = {"depth": depth, "scale": scale, "row_count": row_count,
           "stages": T, "vertices": len(vertices), "classes": len(members),
           "refinement_iterations": iterations, "variables": nvars,
           "equalities": len(eq_rows), "inequalities": len(ub_rows),
           "distance_tail_constraints": tail_constraint_count,
           "success": bool(result.success), "status": int(result.status),
           "message": result.message}
    if result.fun is not None:
        out["max_terminal_wrong"] = float(constant - result.fun)
    if result.x is not None:
        eq_residual = (Aeq @ result.x) - np.asarray(eq_rhs)
        ub_slack = np.asarray(ub_rhs) - (Aub @ result.x)
        lower_slack = np.asarray([result.x[i] - lo for i, (lo, _hi) in enumerate(var_bounds)])
        upper_slack = np.asarray([hi - result.x[i] for i, (_lo, hi) in enumerate(var_bounds)])
        out["max_abs_equality_residual"] = float(np.max(np.abs(eq_residual), initial=0.0))
        out["max_inequality_violation"] = float(np.max(-ub_slack, initial=0.0))
        out["max_bound_violation"] = float(max(
            np.max(-lower_slack, initial=0.0), np.max(-upper_slack, initial=0.0)))

    if compare_raw:
        if not sorted_root:
            raise ValueError("raw comparison currently uses the legacy sorted-root model; pass sorted_root=True")
        from coupled_rank_lp import solve as solve_raw
        raw = solve_raw(depth, scale, F(1, 3), ordered_prefix=False,
                        time_limit=time_limit, params=params,
                        row_count=row_count,
                        distance_tail_profile=distance_tail_profile)
        out["raw_variables"] = raw["variables"]
        out["raw_max_terminal_wrong"] = raw["max_total_wrong"]
        if result.success and raw.get("success"):
            out["objective_difference"] = (
                out["max_terminal_wrong"] - float(raw["max_total_wrong"]))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=4)
    ap.add_argument("--scale", type=int, default=8192)
    ap.add_argument("--row-count", type=int, default=8192)
    ap.add_argument("--time-limit", type=float, default=120)
    ap.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    ap.add_argument("--distance-tail-profile", default="",
                    help="comma-separated row=cap pairs")
    ap.add_argument("--compare-raw", action="store_true",
                    help="compare with the raw legacy sorted-root LP")
    ap.add_argument("--sorted-root", action="store_true",
                    help="legacy diagnostic fixing the root to an already-sorted profile")
    args = ap.parse_args()
    tail_profile = tuple((int(item.split("=")[0]), F(item.split("=")[1]))
                         for item in args.distance_tail_profile.split(",") if item)
    print(build(args.depth, args.scale, args.row_count, tuple(args.params),
                args.time_limit, args.compare_raw, tail_profile,
                args.sorted_root), flush=True)
