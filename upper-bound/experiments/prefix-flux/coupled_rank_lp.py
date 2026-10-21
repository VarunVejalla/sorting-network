#!/usr/bin/env python3
"""Global LP relaxation retaining port correlations across the D2 flow.

Default mode uses the tail-only model. `--ordered-prefix` adds global
static-wire profiles, a backward-closed finite set of local input-prefix
constraints, and exact bag-mass identities. These remain selected cuts rather
than every wire cut, so a nonzero terminal objective diagnoses an insufficient
relaxation, not a counterexample to the fixed comparator network.
"""
from fractions import Fraction as F
import argparse

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from flow_dag import FlowDAG
from first_column import minimum_rectangular_prefix_zeros
from profile_cut_closure import cut_system, prefix_components, rank_before, wire_cut_at_rank
from rank_recurrence import prefix_interval, run as interval_run


def add_row(rows, rhs, terms, value=0):
    rows.append(terms)
    rhs.append(value)


def solve(depth=4, scale=65536, threshold=F(1, 3), ordered_prefix=False,
          root_error=0, root_tail=False):
    cut_data = (cut_system(depth, scale, threshold, root_rows=root_tail)
                if ordered_prefix else None)
    flow = (cut_data[0] if ordered_prefix else
            FlowDAG(depth, scale=scale).build())
    p = flow.p
    N = p.k ** depth * scale
    q = int(threshold * N)
    scalar, history = interval_run(depth, scale, threshold, include_history=True)
    T = len(flow.rows)

    var = {}
    bounds = []

    def new(key, bound):
        var[key] = len(bounds)
        bounds.append(bound)
        return var[key]

    bag_keys = [(lev, idx) for lev in range(depth + 1)
                for idx in range(p.k ** lev)]
    for t in range(T + 1):
        for key in bag_keys:
            node = flow.lookup(t, *key)
            a = flow.allocation(node)
            lo, hi = history[t].get(key, (0, 0))
            var_key = ('H', t, *key)
            new(var_key, (max(0, lo), min(a, hi)))

    ykeys = {}
    for t, row in enumerate(flow.rows):
        active = [(lev, idx) for lev, idx in bag_keys
                  if flow.lookup(t, lev, idx) in row
                  and (lev == 0 if t == 0 else p.active(depth, lev, t))]
        for lev, idx in active:
            node = flow.lookup(t, lev, idx)
            a, pi, blocks = row[node]
            if pi == a:
                continue
            h = pi // 2
            if ordered_prefix:
                cuts = sorted(cut_data[1][t][(lev, idx)])
            else:
                cuts = [0, h]
                cuts.extend([h + sum(blocks[:j]) for j in range(1, len(blocks) + 1)])
                cuts.append(a)
            cuts = sorted(set(cuts))
            yids = []
            Hlo, Hhi = history[t].get((lev, idx), (0, 0))
            for cut in cuts:
                ylo, yhi = prefix_interval(a, (Hlo, Hhi), cut)
                # The root receives the already sorted native input. Every
                # ascending comparator fixes it exactly, so preserve that
                # profile instead of allowing the rank-tail relaxation to
                # invent a root error.
                if (t == 0 and (lev, idx) == (0, 0) and
                        (not ordered_prefix or (root_error == 0 and not root_tail))):
                    ylo = yhi = min(q, cut)
                ykey = ('Y', t, lev, idx, cut)
                yids.append(new(ykey, (ylo, yhi)))
            ykeys[(t, lev, idx)] = (cuts, yids)

    zkeys = {}
    if ordered_prefix:
        global_cuts = cut_data[2]
        for t, cuts in enumerate(global_cuts):
            for cut in sorted(cuts):
                ideal = min(q, cut)
                if t == 0:
                    lower = (prefix_interval(N, (q, q), cut)[0] if root_tail else
                             max(0, ideal - root_error))
                    columns = N // 4096
                    if N % 4096 == 0 and cut % columns == 0:
                        lower = max(lower, minimum_rectangular_prefix_zeros(
                            N, q, cut, rows=4096
                        ))
                    upper = ideal
                else:
                    lower, upper = 0, cut
                zkeys[(t, cut)] = new(('Z', t, cut), (lower, upper))

    eq_rows, eq_rhs, ub_rows, ub_rhs = [], [], [], []

    def eq(terms, value=0):
        add_row(eq_rows, eq_rhs, terms, value)

    def ub(terms, value):
        add_row(ub_rows, ub_rhs, terms, value)

    def hvar(t, key):
        return var[('H', t, *key)]

    def zvar(t, cut):
        return zkeys[(t, cut)]

    def bag_prefix_expr(t, key, wire_cut):
        lev, idx = key
        terms = {}
        wires = flow.bag_intervals(flow.lookup(t, lev, idx), idx)
        for lo, hi in wires:
            right = min(hi, wire_cut)
            if lo < right:
                terms[zvar(t, right)] = terms.get(zvar(t, right), 0) + 1
                terms[zvar(t, lo)] = terms.get(zvar(t, lo), 0) - 1
        return terms

    def bag_total_expr(t, key):
        lev, idx = key
        terms = {}
        wires = flow.bag_intervals(flow.lookup(t, lev, idx), idx)
        for lo, hi in wires:
            terms[zvar(t, hi)] = terms.get(zvar(t, hi), 0) + 1
            terms[zvar(t, lo)] = terms.get(zvar(t, lo), 0) - 1
        return terms

    def port_expr(t, lev, idx, left, right):
        if left == right:
            return {}
        cuts, yids = ykeys[(t, lev, idx)]
        li, ri = cuts.index(left), cuts.index(right)
        return {yids[ri]: 1, yids[li]: -1}

    if ordered_prefix:
        global_cuts = cut_data[2]
        # Tie every bag mass to the exact static-wire profile at that time.
        for t in range(T + 1):
            for key in bag_keys:
                terms = {hvar(t, key): 1}
                for v, coeff in bag_total_expr(t, key).items():
                    terms[v] = terms.get(v, 0) - coeff
                eq(terms, 0)

        # Each selected local output prefix must dominate its actual input
        # prefix, reconstructed from the global static-wire profile.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            wires = flow.bag_intervals(flow.lookup(t, lev, idx), idx)
            for cut, yid in zip(cuts, yids):
                wire_cut = wire_cut_at_rank(wires, cut)
                terms = bag_prefix_expr(t, (lev, idx), wire_cut)
                terms[yid] = terms.get(yid, 0) - 1
                ub(terms, 0)

        # Global prefix counts remain a feasible Boolean profile.
        for t, cuts in enumerate(global_cuts):
            ordered = sorted(cuts)
            eq({zvar(t, 0): 1}, 0)
            eq({zvar(t, N): 1}, q)
            for left, right in zip(ordered, ordered[1:]):
                ub({zvar(t, left): 1, zvar(t, right): -1}, 0)
                ub({zvar(t, right): 1, zvar(t, left): -1}, right - left)

        # Apply each local profile change to global prefix counts. Wires
        # outside active sorting bags retain their previous values.
        for t in range(T):
            row = flow.rows[t]
            active = [(lev, idx) for lev, idx in bag_keys
                      if flow.lookup(t, lev, idx) in row
                      and (lev == 0 if t == 0 else p.active(depth, lev, t))]
            for wire_cut in sorted(global_cuts[t + 1]):
                terms = {zvar(t + 1, wire_cut): 1, zvar(t, wire_cut): -1}
                for key in active:
                    node = flow.lookup(t, *key)
                    a, pi, _ = row[node]
                    if pi == a or a == 0:
                        continue
                    wires = flow.bag_intervals(node, key[1])
                    cut = rank_before(wires, wire_cut)
                    yid = var[('Y', t, *key, cut)]
                    terms[yid] = terms.get(yid, 0) - 1
                    for v, coeff in bag_prefix_expr(t, key, wire_cut).items():
                        terms[v] = terms.get(v, 0) + coeff
                eq(terms, 0)

    # Every active node has one shared cumulative output profile, not
    # independent intervals for each port.
    for t, row in enumerate(flow.rows):
        active_nodes = [node for node in row
                        if (flow.nodes[node][0] == 0 if t == 0 else
                            p.active(depth, flow.nodes[node][0], t))]
        for node in active_nodes:
            lev, _, _, _, _ = flow.nodes[node]
            a, pi, blocks = row[node]
            idxs = [idx for idx in range(p.k ** lev)
                    if flow.lookup(t, lev, idx) == node]
            # Interned equal states can occur at several addresses. Each
            # address has its own mass and output profile in the global flow.
            for idx in idxs:
                key = (lev, idx)
                if pi == a:
                    continue
                h = pi // 2
                cuts, yids = ykeys[(t, lev, idx)]
                eq({yids[0]: 1}, 0)
                eq({yids[-1]: 1, hvar(t, key): -1}, 0)
                for j in range(len(cuts) - 1):
                    width = cuts[j + 1] - cuts[j]
                    ub({yids[j]: 1, yids[j + 1]: -1}, 0)
                    ub({yids[j + 1]: 1, yids[j]: -1}, width)

    # Each next-stage bag is exactly the union of its routed input ports and,
    # when inactive, its retained old contents.
    for t, row in enumerate(flow.rows):
        active_set = {(lev, idx) for lev, idx in bag_keys
                      if (lev == 0 if t == 0 else p.active(depth, lev, t))}
        for key in bag_keys:
            lev, idx = key
            terms = {hvar(t + 1, key): 1}
            if key not in active_set:
                terms[hvar(t, key)] = terms.get(hvar(t, key), 0) - 1

            if lev > 0:
                parent = (lev - 1, idx // p.k)
                pnode = flow.lookup(t, *parent)
                if pnode in row:
                    a, pi, blocks = row[pnode]
                    if pi < a:
                        h = pi // 2
                        start = h + sum(blocks[:idx % p.k])
                        end = start + blocks[idx % p.k]
                        expr = port_expr(t, *parent, start, end)
                        for v, c in expr.items():
                            terms[v] = terms.get(v, 0) - c

            if lev < depth:
                for j in range(p.k):
                    child = (lev + 1, idx * p.k + j)
                    cnode = flow.lookup(t, *child)
                    if cnode not in row:
                        continue
                    a, pi, blocks = row[cnode]
                    if pi == a:
                        expr = {hvar(t, child): 1}
                    else:
                        h = pi // 2
                        left = port_expr(t, *child, 0, h)
                        right = port_expr(t, *child, a - h, a)
                        expr = left.copy()
                        for v, c in right.items():
                            expr[v] = expr.get(v, 0) + c
                    for v, c in expr.items():
                        terms[v] = terms.get(v, 0) - c
            eq(terms, 0)

    nvars = len(bounds)

    def matrix(rows):
        rr, cc, dd = [], [], []
        for i, terms in enumerate(rows):
            for j, value in terms.items():
                if value:
                    rr.append(i); cc.append(j); dd.append(value)
        return coo_matrix((dd, (rr, cc)), shape=(len(rows), nvars)).tocsr()

    # A sorted-output path is a cheap diagnostic witness. It must satisfy this
    # overapproximation; if not, the transfer encoding itself is wrong.
    witness = np.zeros(nvars)
    if ordered_prefix:
        for (t, cut), z_id in zkeys.items():
            witness[z_id] = min(q, cut)
    W = {(0, 0): q}
    for t, row in enumerate(flow.rows):
        for key in bag_keys:
            witness[hvar(t, key)] = W.get(key, 0)
        active = [(lev, idx) for lev, idx in bag_keys
                  if flow.lookup(t, lev, idx) in row
                  and (lev == 0 if t == 0 else p.active(depth, lev, t))]
        active_set = set(active)
        downs, ups = {}, {}
        for lev, idx in active:
            node = flow.lookup(t, lev, idx)
            a, pi, blocks = row[node]
            mass = W.get((lev, idx), 0)
            if pi == a:
                ups[(lev, idx)] = mass
                continue
            h = pi // 2
            cuts, yids = ykeys[(t, lev, idx)]
            for cut, yid in zip(cuts, yids):
                witness[yid] = min(mass, cut)
            ups[(lev, idx)] = min(mass, h) + mass - min(mass, a - h)
            pos = h
            for j, width in enumerate(blocks):
                downs[(lev, idx, j)] = min(mass, pos + width) - min(mass, pos)
                pos += width
        Wnext = {}
        for lev, idx in bag_keys:
            key = (lev, idx)
            pieces = [W.get(key, 0)] if key not in active_set else []
            if lev > 0:
                parent = (lev - 1, idx // p.k)
                port = idx % p.k
                if (lev - 1, idx // p.k, port) in downs:
                    pieces.append(downs[(lev - 1, idx // p.k, port)])
            if lev < depth:
                for j in range(p.k):
                    child = (lev + 1, idx * p.k + j)
                    if child in ups:
                        pieces.append(ups[child])
            Wnext[key] = sum(pieces)
        W = Wnext
    for key in bag_keys:
        witness[hvar(T, key)] = W.get(key, 0)

    # Maximize total wrong mass outside the one threshold-straddling terminal
    # native interval. All other wholly one-colored blocks must be pure.
    c = np.zeros(nvars)
    constant = 0
    bad = 0
    for lev, idx in bag_keys:
        node = flow.lookup(T, lev, idx)
        a = flow.allocation(node)
        if not a:
            continue
        wires = flow.bag_intervals(node, idx)
        before = sum(max(0, min(hi, q) - lo) for lo, hi in wires)
        after = a - before
        h = hvar(T, (lev, idx))
        if before == a:
            c[h] += 1
            constant += a
            bad += 1
        elif after == a:
            c[h] -= 1
            bad += 1

    A_ub, A_eq = matrix(ub_rows), matrix(eq_rows)
    eq_residual = A_eq @ witness - np.asarray(eq_rhs)
    witness_eq_error = float(np.max(np.abs(eq_residual)))
    worst_eq = int(np.argmax(np.abs(eq_residual)))
    var_by_id = {v: k for k, v in var.items()}
    witness_ub_error = float(max(0, np.max(A_ub @ witness - np.asarray(ub_rhs))))
    witness_bound_error = max(max(lo - value, value - hi, 0)
                              for value, (lo, hi) in zip(witness, bounds))
    result = linprog(c, A_ub=A_ub, b_ub=np.asarray(ub_rhs),
                     A_eq=A_eq, b_eq=np.asarray(eq_rhs),
                     bounds=bounds, method='highs')
    if not result.success:
        return dict(depth=depth, stages=T, success=False, message=result.message,
                    variables=nvars, equalities=len(eq_rows), inequalities=len(ub_rows),
                    sorted_witness_eq_error=witness_eq_error,
                    worst_eq_index=worst_eq,
                    worst_eq_terms={var_by_id[v]: c for v, c in eq_rows[worst_eq].items()},
                    sorted_witness_ub_error=witness_ub_error,
                    sorted_witness_bound_error=witness_bound_error)
    rounded = np.rint(result.x)
    rounded_eq_error = float(np.max(np.abs(A_eq @ rounded - np.asarray(eq_rhs))))
    rounded_ub_error = float(max(0, np.max(A_ub @ rounded - np.asarray(ub_rhs))))
    rounded_bound_error = max(max(lo - value, value - hi, 0)
                              for value, (lo, hi) in zip(rounded, bounds))
    terminal_wrong = []
    for lev, idx in bag_keys:
        node = flow.lookup(T, lev, idx)
        a = flow.allocation(node)
        if not a:
            continue
        wires = flow.bag_intervals(node, idx)
        before = sum(max(0, min(hi, q) - lo) for lo, hi in wires)
        after = a - before
        if before == a:
            terminal_wrong.append((lev, idx, a - int(rounded[hvar(T, (lev, idx))])))
        elif after == a:
            terminal_wrong.append((lev, idx, int(rounded[hvar(T, (lev, idx))])))
    root_defects = []
    if ordered_prefix:
        for (t, cut), z_id in zkeys.items():
            if t == 0:
                defect = min(q, cut) - int(rounded[z_id])
                if defect:
                    root_defects.append((cut, defect))
    return dict(depth=depth, stages=T, success=True, variables=nvars,
                ordered_prefix=ordered_prefix, root_error=root_error,
                root_tail=root_tail,
                equalities=len(eq_rows), inequalities=len(ub_rows),
                sorted_witness_eq_error=witness_eq_error,
                sorted_witness_ub_error=witness_ub_error,
                sorted_witness_bound_error=witness_bound_error,
                terminal_noncrossing_blocks=bad,
                max_total_wrong=(int(round(constant - result.fun))
                                 if np.max(np.abs(result.x - rounded)) < 1e-6
                                 else float(constant - result.fun)),
                integral_solution=bool(np.max(np.abs(result.x - np.round(result.x))) < 1e-6),
                rounded_solution_valid=(rounded_eq_error == 0 and rounded_ub_error == 0
                                        and rounded_bound_error == 0),
                max_single_terminal_wrong=max((x[2] for x in terminal_wrong), default=0),
                terminal_wrong_sample=terminal_wrong[:8],
                root_prefix_defect_sample=root_defects[:12],
                scalar_terminal_bad=scalar['terminal_bad'])


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depth', type=int, default=4)
    ap.add_argument('--scale', type=int, default=65536)
    ap.add_argument('--threshold', default='1/3')
    ap.add_argument('--ordered-prefix', action='store_true',
                    help='add static-wire global profiles and local prefix dominance')
    ap.add_argument('--root-error', type=int, default=0,
                    help='allow this prefix-defect budget in the initial root profile')
    ap.add_argument('--root-tail', action='store_true',
                    help='initialize with the local all-cut rank-tail envelope')
    args = ap.parse_args()
    print('GLOBAL COUPLED LP RELAXATION; not a sorting proof')
    print(solve(args.depth, args.scale, F(args.threshold), args.ordered_prefix,
                args.root_error, args.root_tail))
