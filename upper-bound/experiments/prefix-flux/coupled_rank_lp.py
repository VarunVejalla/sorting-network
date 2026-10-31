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
from bisect import bisect_left, bisect_right
import json
from math import isqrt, sqrt
from pathlib import Path
from types import SimpleNamespace
import os
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix

from flow_dag import FlowDAG
from oracle import Par
from first_column import minimum_rectangular_prefix_zeros
from profile_cut_closure import (cut_system, occupied_bag_keys,
                                 prefix_components, rank_before, wire_cut_at_rank)
from rank_recurrence import prefix_interval, run as interval_run
from sparse_probe import profile_tail, sum_abs_integer_interval


class _StageOffsetSchedule:
    def __init__(self, base, offset):
        self.base = base
        self.offset = offset

    def __getattr__(self, name):
        return getattr(self.base, name)

    def active(self, depth, level, stage):
        return self.base.active(depth, level, stage + self.offset)


def bag_alignment_distance_proxy(wires, mass, threshold):
    """Piecewise-linear sum of threshold distances in a bag's sorted reference."""
    ideal = rank_before(wires, threshold)

    def prefix_distance(rank):
        total = 0.0
        remaining = max(0.0, rank)
        for lo, hi in wires:
            width = hi - lo
            take = min(float(width), remaining)
            whole = int(take)
            fraction = take - whole
            total += sum_abs_integer_interval(lo, lo + whole, threshold)
            if fraction and whole < width:
                total += fraction * abs(lo + whole - threshold)
            remaining -= take
            if remaining <= 0:
                break
        return total

    return prefix_distance(max(float(mass), ideal)) - prefix_distance(min(float(mass), ideal))


def inversion_area_interval(cuts, zero_prefix, q):
    """Exact min/max inversion count over binary fillings between sampled cuts.

    For each interval, endpoint zero counts determine how many misplaced bits
    it contains; putting them at the left or right endpoint extremizes the
    sum of prefix defects. The result is exact when every cut is present and
    otherwise is a rigorous interval for all binary fillings consistent with
    the sampled integer profile.
    """
    cuts = sorted(cuts)
    if not cuts or cuts[0] != 0 or cuts[-1] < q or q not in zero_prefix:
        return None
    lo_total = hi_total = 0
    for a, b in zip(cuts, cuts[1:]):
        if a not in zero_prefix or b not in zero_prefix:
            return None
        length = b - a
        za, zb = zero_prefix[a], zero_prefix[b]
        if not (0 <= zb - za <= length):
            return None
        if b <= q:
            base = a - za
            misplaced = length - (zb - za)
            lo_total += length * base + misplaced * (misplaced - 1) // 2
            hi_total += (length * base +
                         misplaced * (2 * length - misplaced - 1) // 2)
        elif a >= q:
            base = q - za
            misplaced = zb - za
            lo_total += (length * base -
                         misplaced * (2 * length - misplaced - 1) // 2)
            hi_total += length * base - misplaced * (misplaced - 1) // 2
        else:
            return None  # q must itself be a sampled cut
    return lo_total, hi_total


def distance_moment_weight(r, q, order):
    """Coefficient of prefix defect F(r) in the order-s distance moment."""
    if r <= q:
        return (q - r + 1) ** order - (q - r) ** order
    return (r - q) ** order - (r - q - 1) ** order


def add_row(rows, rhs, terms, value=0):
    rows.append(terms)
    rhs.append(value)


def solve(depth=4, scale=65536, threshold=F(1, 3), ordered_prefix=False,
          root_error=0, root_tail=False, all_row_dominance=False,
          row_stride=1, dominance_only_extra_cuts=False, integer=False,
          time_limit=120, params=(2, 3, 2), row_count=1 << 12,
          exact_slope_core=False,
          conditioned_tail_gap=0, aggregate_defect_fraction=None,
          seam_defect_fraction=None, local_cut_defect_fraction=None,
          mass_sensitive_mean=False,
          propagated_tail_gap=0, all_global_cuts=False,
          root_inversion_cap=None, all_root_cuts=False,
          distance_tail_profile=(),
          root_inversion_floor=0, lp_method='highs',
          exact_refresh_stage=None, refresh_alignment_cap=None,
          exact_refresh_stages=(), alignment_drift_stage=None,
          alignment_weight=F(1, 4), alignment_drift_rho=F(1),
          alignment_prev_floor=0, alignment_local_error_weight=F(0),
          alignment_drift_span=1, alignment_error_weight=F(0),
          inversion_drift_stage=None, inversion_drift_rho=F(1),
          inversion_prev_floor=0, inversion_moment_order=1,
          inversion_drift_span=1, alignment_level_weights=None,
          alignment_next_level_weights=None,
          alignment_prev_floor_unweighted=False,
          rank_profile_weight=F(0), rank_profile_exact=False,
          global_profile_path=None, rank_profile_all_cuts=False,
          inversion_sparse_enclosure=False, lp_presolve=None,
          simplex_edge_strategy=None, raw_highspy=False,
          transition_source_stage=None, transition_source_span=1,
          cardinality_prefix_relaxation=False,
          local_cut_history_relaxation=False,
          column_profile_monotone=False,
          variance_prefix_area_gamma=None, mip_presolve=None,
          variance_port_l1_gamma=None, terminal_error_level=None,
          variance_port_l1_residue=False, exact_core_boolean=True,
          pairwise_core_hull=False, local_cut_defect_absolute=None):
    progress_enabled = os.environ.get('SUB300_LP_PROGRESS') == '1'
    progress_start = time.perf_counter()

    def report_progress(message):
        if progress_enabled:
            print(f'[lp-progress +{time.perf_counter() - progress_start:.1f}s] '
                  f'{message}', flush=True)

    if aggregate_defect_fraction is not None:
        assert ordered_prefix and all_row_dominance and row_stride == 1
    if seam_defect_fraction is not None:
        assert ordered_prefix
    if local_cut_defect_fraction is not None:
        assert ordered_prefix and all_row_dominance
        assert row_stride == 1 or local_cut_history_relaxation
    if local_cut_defect_absolute is not None:
        assert ordered_prefix and all_row_dominance
        assert local_cut_defect_absolute >= 0
        assert row_stride == 1 or local_cut_history_relaxation
    if cardinality_prefix_relaxation:
        assert (local_cut_defect_fraction is not None
                or local_cut_defect_absolute is not None)
    if local_cut_history_relaxation:
        assert (local_cut_defect_fraction is not None
                or local_cut_defect_absolute is not None)

    def local_cut_cap(allocation):
        caps = []
        if local_cut_defect_fraction is not None:
            caps.append(local_cut_defect_fraction * allocation)
        if local_cut_defect_absolute is not None:
            caps.append(F(local_cut_defect_absolute))
        return min(caps) if caps else None
    if column_profile_monotone:
        assert ordered_prefix and all_row_dominance
    if terminal_error_level is not None:
        assert 0 <= terminal_error_level <= depth
    variance_area_radius = 0
    variance_area_budget_factor = None
    variance_port_l1_factor = None
    if variance_port_l1_gamma is None:
        variance_port_l1_gamma = variance_prefix_area_gamma
    if variance_port_l1_gamma is not None:
        variance_port_l1_gamma = F(variance_port_l1_gamma)
    if variance_port_l1_gamma is not None:
        assert variance_port_l1_gamma >= 0
        assert ordered_prefix and all_row_dominance
        port_scale = 1_000_000
        port_square_num = (2 * variance_port_l1_gamma.numerator
                           * port_scale * port_scale)
        port_square_den = variance_port_l1_gamma.denominator
        port_root = isqrt(port_square_num // port_square_den)
        while port_root * port_root * port_square_den < port_square_num:
            port_root += 1
        # The variance theorem compares with the uniform-density profile,
        # while the LP's exact rank target is min(H, cut). For a rectangular
        # row-major sender their cumulative discrepancy has total variation
        # at most columns/2. The residue-sensitive option encodes the exact
        # correction 2*r*(1-r/columns), with r = H mod columns, instead.
        variance_port_l1_factor = F(port_root, port_scale)
        if not variance_port_l1_residue:
            variance_port_l1_factor += F(1, 2)
    if variance_port_l1_residue:
        assert variance_port_l1_gamma is not None
    if variance_prefix_area_gamma is not None:
        variance_prefix_area_gamma = F(variance_prefix_area_gamma)
        assert variance_prefix_area_gamma >= 0
        assert ordered_prefix and all_row_dominance
        assert row_count % row_stride == 0
        gamma_half = variance_prefix_area_gamma / 2
        while F((variance_area_radius + 1) ** 2) < gamma_half:
            variance_area_radius += 1
        sqrt_ceil = variance_area_radius + int(
            F(variance_area_radius ** 2) != gamma_half
        )
        variance_area_budget_factor = variance_prefix_area_gamma + sqrt_ceil
        # Truncate the local cones when necessary so sampled neighborhoods
        # remain disjoint; any smaller radius gives a valid weaker bound.
        variance_area_radius = min(variance_area_radius,
                                   (row_stride - 1) // 2)
    if mass_sensitive_mean:
        assert ordered_prefix and all_row_dominance and row_stride == 1
    if propagated_tail_gap:
        assert ordered_prefix and all_row_dominance
        assert 0 < propagated_tail_gap and 2 * propagated_tail_gap <= row_count
        # The tail inequality is pointwise in its baseline and output cuts,
        # so a row-grid subset is still a sound (weaker) relaxation. Require
        # the requested gap to land on that grid so both endpoints exist.
        assert propagated_tail_gap % row_stride == 0
    distance_tail_profile = tuple(sorted(
        ((int(r), F(str(cap))) for r, cap in distance_tail_profile),
        key=lambda item: item[0]))
    assert all(r > 0 and 0 <= cap <= 1
               for r, cap in distance_tail_profile)
    refresh_stages = set(exact_refresh_stages)
    if exact_refresh_stage is not None:
        refresh_stages.add(exact_refresh_stage)
    if refresh_stages:
        assert ordered_prefix and all(0 <= t < depth for t in refresh_stages)
    if refresh_alignment_cap is not None:
        assert exact_refresh_stage is not None and refresh_alignment_cap >= 0
    if alignment_drift_stage is not None:
        assert ordered_prefix and 0 <= alignment_drift_stage < depth
        assert alignment_drift_span >= 1
        assert (0 < alignment_weight <= 1 and alignment_drift_rho >= 0
                and alignment_prev_floor >= 0
                and alignment_local_error_weight >= 0
                and alignment_error_weight >= 0)
        if alignment_level_weights is not None:
            alignment_level_weights = tuple(F(w) for w in alignment_level_weights)
            assert alignment_level_weights and all(w > 0 for w in alignment_level_weights)
        if alignment_next_level_weights is not None:
            alignment_next_level_weights = tuple(F(w) for w in alignment_next_level_weights)
            assert alignment_next_level_weights and all(w > 0 for w in alignment_next_level_weights)
    if inversion_drift_stage is not None:
        assert ordered_prefix and (all_global_cuts or inversion_sparse_enclosure)
        assert 0 <= inversion_drift_stage < depth
        assert inversion_drift_rho >= 0 and inversion_prev_floor >= 0
        assert inversion_moment_order >= 1 and inversion_drift_span >= 1
        assert alignment_drift_stage is None
        if inversion_sparse_enclosure:
            assert inversion_prev_floor == 0, "sparse enclosure does not support inversion_prev_floor"
    if transition_source_stage is not None:
        assert transition_source_stage >= 0
        assert transition_source_span >= 1
        assert inversion_drift_stage == 0
        assert inversion_drift_span == transition_source_span
        assert root_inversion_cap is None and not all_root_cuts
        assert not conditioned_tail_gap
    if root_inversion_cap is not None:
        assert ordered_prefix
        assert 0 <= root_inversion_floor <= root_inversion_cap
    else:
        assert root_inversion_floor == 0
    if conditioned_tail_gap:
        assert ordered_prefix and all_row_dominance
        assert row_stride > 0
        assert 0 < conditioned_tail_gap < row_count
        assert row_count % conditioned_tail_gap == 0
        assert conditioned_tail_gap % row_stride == 0
    flow_override = None
    if transition_source_stage is not None:
        flow_override = FlowDAG(depth, scale=scale, p=Par(*params)).build()
        assert transition_source_stage + transition_source_span < len(flow_override.roots)
        base_schedule = flow_override.p
        flow_override.rows = flow_override.rows[
            transition_source_stage:transition_source_stage + transition_source_span]
        flow_override.roots = flow_override.roots[
            transition_source_stage:transition_source_stage + transition_source_span + 1]
        flow_override.stage_offset = transition_source_stage
        flow_override.p = _StageOffsetSchedule(base_schedule,
                                                transition_source_stage)
    cut_data = (cut_system(depth, scale, threshold,
                           root_rows=(root_tail and transition_source_stage is None),
                           all_row_cuts=all_row_dominance, row_stride=row_stride,
                           params=params, row_count=row_count,
                           all_global_cuts=all_global_cuts,
                           all_root_cuts=all_root_cuts,
                           root_inversion_cap=root_inversion_cap,
                           flow_override=flow_override)
                if ordered_prefix else None)
    report_progress('cut-system construction complete')
    flow = (cut_data[0] if ordered_prefix else
            (flow_override or FlowDAG(depth, scale=scale, p=Par(*params)).build()))
    p = flow.p
    N = p.k ** depth * scale
    q = int(threshold * N)
    if refresh_alignment_cap is not None:
        assert refresh_alignment_cap <= q
    scalar, history = interval_run(depth, scale, threshold, include_history=True,
                                    params=params, row_count=row_count)
    report_progress('interval history construction complete')
    T = len(flow.rows)
    if transition_source_stage is not None:
        history = history[transition_source_stage:transition_source_stage + T + 1]
    if exact_slope_core:
        assert ordered_prefix and all_global_cuts
        assert row_count <= 8, "reduced exact-core gate only"
        assert N <= (1 << 18)
    if pairwise_core_hull:
        assert exact_slope_core and row_count == 2 and not exact_core_boolean

    def active_level(t, level):
        if transition_source_stage is None and t == 0:
            return level == 0
        return p.active(depth, level, t)
    if inversion_drift_stage is not None:
        assert inversion_drift_stage + inversion_drift_span <= T
    if alignment_drift_stage is not None:
        assert alignment_drift_stage + alignment_drift_span <= T

    var = {}
    bounds = []
    integer_ids = set()
    continuous_aux_ids = set()

    def new(key, bound, integral=False):
        var[key] = len(bounds)
        bounds.append(bound)
        if integral:
            integer_ids.add(var[key])
        return var[key]

    bag_keys = sorted({key for t in range(T + 1)
                       for key in occupied_bag_keys(flow, t)})
    for t in range(T + 1):
        for key in bag_keys:
            node = flow.lookup(t, *key)
            a = flow.allocation(node)
            lo, hi = history[t].get(key, (0, 0))
            var_key = ('H', t, *key)
            new(var_key, (max(0, lo), min(a, hi)))
    report_progress(f'bag-mass variables complete; count={len(bounds)}')

    ykeys = {}
    history_local_cut_constraints = 0
    conditioned_tail_constraints = 0
    progress_ybags = 0
    for t, row in enumerate(flow.rows):
        active = [(lev, idx) for lev, idx in bag_keys
                  if flow.lookup(t, lev, idx) in row
                  and active_level(t, lev)]
        for lev, idx in active:
            progress_ybags += 1
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
            if progress_enabled:
                report_progress(f'local prefix sender {progress_ybags}: '
                                f'stage={t}, bag=({lev},{idx}), '
                                f'allocation={a}, cuts-before-dedup={len(cuts)}')
            cuts = sorted(set(cuts))
            if progress_enabled:
                report_progress(f'local prefix cuts deduplicated: '
                                f'sender={progress_ybags}, cuts={len(cuts)}')
            yids = []
            Hlo, Hhi = history[t].get((lev, idx), (0, 0))
            base_cuts = {0, a}
            if pi < a:
                base_cuts.add(h)
                pos = h
                for width in blocks:
                    pos += width
                    base_cuts.add(pos)
            for cut in cuts:
                if cardinality_prefix_relaxation:
                    # Isolate the pointwise B2 cut contract from the separate
                    # profile-tail envelope. Keep cardinality bounds here;
                    # first-column geometry and B2 cuts are imposed below.
                    ylo = max(0, Hlo - (a - cut))
                    yhi = min(Hhi, cut)
                elif ordered_prefix and dominance_only_extra_cuts and cut not in base_cuts:
                    ylo = max(0, Hlo - (a - cut))
                    yhi = min(Hhi, cut)
                else:
                    ylo, yhi = prefix_interval(a, (Hlo, Hhi), cut, row_count)
                if (local_cut_history_relaxation and a % row_count == 0
                        and cut % (a // row_count) == 0):
                    # From min(H,cut)-Y(cut) <= eps*a and H>=Hlo,
                    # retain the valid history-only consequence
                    # Y(cut) >= min(Hlo,cut)-eps*a. This avoids the exact
                    # segment binaries while deliberately weakening B2.
                    ylo = max(ylo, float(min(Hlo, cut) - local_cut_cap(a)))
                    history_local_cut_constraints += 1
                # The later two ascending sorts cannot worsen a local prefix
                # relative to the first column sort. At an arbitrary cut use
                # the preceding full row, whose physical/semantic count is exact.
                if a > 0 and a % row_count == 0:
                    columns = a // row_count
                    full_row_cut = (cut // columns) * columns
                    ylo = max(ylo, minimum_rectangular_prefix_zeros(
                        a, Hlo, full_row_cut, rows=row_count
                    ))
                # The root receives the already sorted native input. Every
                # ascending comparator fixes it exactly, so preserve that
                # profile instead of allowing the rank-tail relaxation to
                # invent a root error.
                if (transition_source_stage is None and t == 0
                        and (lev, idx) == (0, 0)
                        and root_inversion_cap is None
                        and (not ordered_prefix or (root_error == 0 and not root_tail))):
                    ylo = yhi = min(q, cut)
                ykey = ('Y', t, lev, idx, cut)
                yids.append(new(ykey, (ylo, yhi)))
            ykeys[(t, lev, idx)] = (cuts, yids)
    report_progress(f'local prefix variables complete; bags={len(ykeys)}, '
                    f'variables={len(bounds)}')

    zkeys = {}
    if ordered_prefix:
        global_cuts = cut_data[2]
        for t, cuts in enumerate(global_cuts):
            for cut in sorted(cuts):
                ideal = min(q, cut)
                if t == 0 and transition_source_stage is None:
                    if root_inversion_cap is not None:
                        lower, upper = max(0, q - (N - cut)), min(q, cut)
                        left = max(0, q - root_inversion_cap)
                        right = min(N, q + root_inversion_cap + 1)
                        if cut < left or cut >= right:
                            lower = upper = ideal
                    else:
                        lower = (prefix_interval(N, (q, q), cut, row_count)[0] if root_tail else
                                 max(0, ideal - root_error))
                        upper = ideal
                    columns = N // row_count
                    if (root_inversion_cap is None and N % row_count == 0
                            and cut % columns == 0):
                        lower = max(lower, minimum_rectangular_prefix_zeros(
                            N, q, cut, rows=row_count
                        ))
                elif t == 0:
                    lower, upper = max(0, q - (N - cut)), min(q, cut)
                else:
                    lower, upper = 0, cut
                zkeys[(t, cut)] = new(('Z', t, cut), (lower, upper))
    report_progress(f'global prefix variables complete; cuts={len(zkeys)}, '
                    f'variables={len(bounds)}')

    eq_rows, eq_rhs, ub_rows, ub_rhs = [], [], [], []

    def eq(terms, value=0):
        add_row(eq_rows, eq_rhs, terms, value)

    def ub(terms, value):
        add_row(ub_rows, ub_rhs, terms, value)

    column_profile_constraints = 0
    if column_profile_monotone:
        # A final column sort makes row counts nonincreasing. At sampled
        # equal-width row bands this says their average occupancies decrease,
        # i.e. the cumulative prefix profile is concave at those boundaries.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            columns = a // row_count
            y_at = dict(zip(cuts, yids))
            row_cuts = [r * columns
                        for r in range(0, row_count + 1, row_stride)]
            if not set(row_cuts).issubset(y_at):
                raise ValueError('column-profile monotonicity requires every sampled row cut')
            for i in range(len(row_cuts) - 2):
                left, mid, right = (y_at[row_cuts[i]],
                                    y_at[row_cuts[i + 1]],
                                    y_at[row_cuts[i + 2]])
                ub({left: 1, mid: -2, right: 1}, 0)
                column_profile_constraints += 1

    variance_prefix_area_constraints = 0
    variance_port_l1_constraints = 0
    if variance_prefix_area_gamma is not None:
        # A cut defect D forces at least D+2*sum_s(D-s*n)_+ area in its
        # radius-R row neighborhood, since |d(r+1)-d(r)|<=n. The sampled
        # neighborhoods are disjoint. A_w<=Gamma*n bounds total area by
        # n*(Gamma+sqrt(Gamma/2)); the integer budget factor is rounded up.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            columns = a // row_count
            y_at = dict(zip(cuts, yids))
            row_cuts = [r * columns
                        for r in range(row_stride, row_count, row_stride)]
            if not set(row_cuts).issubset(y_at):
                raise ValueError('variance-area budget requires sampled row cuts')
            Hlo, _ = history[t].get((lev, idx), (0, 0))
            if row_stride == 1:
                # With every row cut present, the area is a direct sum. Since
                # min(Hlo,s)<=min(H,s), the history-based signed lower sum is
                # a valid necessary constraint and avoids one epigraph var per cut.
                area_terms = {y_at[cut]: -1 for cut in row_cuts}
                ideal_sum = sum(min(Hlo, cut) for cut in row_cuts)
                ub(area_terms,
                   float(variance_area_budget_factor * columns - ideal_sum))
                variance_prefix_area_constraints += 1
                continue
            area_terms = {}
            for cut in row_cuts:
                ideal_lower = min(Hlo, cut)
                defect = new(('variancePrefixDefect', t, lev, idx, cut),
                             (0, min(a, ideal_lower)))
                continuous_aux_ids.add(defect)
                # defect >= max(0, min(Hlo,cut)-Y(cut)).
                ub({defect: -1, y_at[cut]: -1}, -ideal_lower)
                area_terms[defect] = 1
                for offset in range(1, variance_area_radius + 1):
                    excess = new(('variancePrefixCone', t, lev, idx,
                                  cut, offset), (0, a))
                    continuous_aux_ids.add(excess)
                    # excess >= max(0, defect - offset*columns).
                    ub({defect: 1, excess: -1}, offset * columns)
                    area_terms[excess] = 2
            ub(area_terms,
               float(variance_area_budget_factor * columns))
            variance_prefix_area_constraints += 1

    if variance_port_l1_gamma is not None:
        # If the sender's row bands partition every column, their signed
        # count errors relative to the uniform-density port map have total
        # zero and l1 norm <= sqrt(2*n*Aw) <= sqrt(2*Gamma)*columns.
        # Encode the l1 epigraph on the actual child/fringe port boundaries.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            columns = a // row_count
            if node not in flow.rows[t]:
                continue
            _a, pi, blocks = flow.rows[t][node]
            if pi == a:
                continue
            boundaries = {0, a, pi // 2}
            pos = pi // 2
            for width in blocks:
                pos += width
                boundaries.add(pos)
            boundaries = sorted(boundaries)
            y_at = dict(zip(cuts, yids))
            if not set(boundaries).issubset(y_at):
                raise ValueError('variance port l1 requires all port boundaries')
            h_id = var[('H', t, lev, idx)]
            h_lo, h_hi = bounds[h_id]
            ideal_at = {}
            for cut in boundaries:
                if cut == 0:
                    ideal_at[cut] = new(('variancePortIdeal', t, lev, idx, cut),
                                        (0, 0))
                    continue
                if h_hi <= cut:
                    ideal_at[cut] = h_id
                elif h_lo >= cut:
                    ideal_at[cut] = new(
                        ('variancePortIdeal', t, lev, idx, cut), (cut, cut))
                else:
                    ideal_id = new(('variancePortIdeal', t, lev, idx, cut),
                                   (0, cut))
                    choose_h = new(('variancePortIdealSign', t, lev, idx, cut),
                                   (0, 1), integral=True)
                    big_m = max(a, cut)
                    ub({ideal_id: 1, h_id: -1}, 0)
                    ub({ideal_id: 1}, cut)
                    ub({ideal_id: -1, h_id: 1, choose_h: big_m}, big_m)
                    ub({ideal_id: -1, choose_h: -big_m}, -cut)
                    ideal_at[cut] = ideal_id
            l1_terms = {}
            for left, right in zip(boundaries, boundaries[1:]):
                delta = {}
                for ident, coefficient in (
                        (y_at[right], 1), (y_at[left], -1),
                        (ideal_at[right], -1), (ideal_at[left], 1)):
                    delta[ident] = delta.get(ident, 0) + coefficient
                delta = {ident: coefficient for ident, coefficient in delta.items()
                         if coefficient}
                abs_id = new(('variancePortAbs', t, lev, idx, left, right),
                             (0, right - left))
                ub({**delta, abs_id: -1}, 0)
                ub({**{v: -coef for v, coef in delta.items()}, abs_id: -1}, 0)
                l1_terms[abs_id] = 1
            if variance_port_l1_residue:
                h_lo, h_hi = bounds[h_id]
                quotient = new(('variancePortQuotient', t, lev, idx),
                               (h_lo // columns, h_hi // columns),
                               integral=True)
                residue_sum_terms = {}
                residue_selectors = []
                for residue in range(columns):
                    selector = new(('variancePortResidue', t, lev, idx,
                                    residue), (0, 1), integral=True)
                    residue_selectors.append(selector)
                    residue_sum_terms[selector] = 1
                    l1_terms[selector] = -float(
                        F(2 * residue * (columns - residue), columns))
                eq(residue_sum_terms, 1)
                residue_eq = {h_id: 1, quotient: -columns}
                for residue, selector in enumerate(residue_selectors):
                    if residue:
                        residue_eq[selector] = -residue
                eq(residue_eq, 0)
                # For rank boundary b=kn+s and H=qn+r, the uniform
                # per-column profile differs from min(H,b) only in row q;
                # its cumulative discrepancy has total variation exactly
                # 2*r*(1-r/columns). Summing port-boundary increments is
                # therefore bounded by this residue-specific value.
            ub(l1_terms, float(variance_port_l1_factor * columns))
            variance_port_l1_constraints += 1

    def hvar(t, key):
        return var[('H', t, *key)]

    def zvar(t, cut):
        return zkeys[(t, cut)]

    def moment_enclosure(t, upper):
        """Linear one-sided bound for M_s using monotonicity of prefix defect.

        F(r)=min(q,r)-Z(r) is nondecreasing on [0,q] and nonincreasing on
        [q,N]. Between retained cuts, omitted F values are bounded by the
        appropriate endpoint. Distance-moment weights telescope over each
        gap, so the enclosure is linear in the retained Z variables.
        """
        cuts = sorted(cut_data[2][t])
        assert cuts and cuts[0] == 0 and cuts[-1] == N and q in cuts
        constant = 0.0
        terms = {}

        def add_f(cut, coefficient):
            nonlocal constant
            if not coefficient:
                return
            constant += coefficient * min(q, cut)
            if 0 < cut < N:
                ident = zvar(t, cut)
                terms[ident] = terms.get(ident, 0.0) - coefficient

        for cut in cuts:
            if 0 < cut < N:
                add_f(cut, distance_moment_weight(
                    cut, q, inversion_moment_order))
        for left, right in zip(cuts, cuts[1:]):
            if right - left <= 1:
                continue
            assert right <= q or left >= q, (left, right, q)
            if right <= q:
                omitted_weight = ((q - left) ** inversion_moment_order
                                  - (q - right + 1) ** inversion_moment_order)
                anchor = right if upper else left
            else:
                omitted_weight = ((right - 1 - q) ** inversion_moment_order
                                  - (left - q) ** inversion_moment_order)
                anchor = left if upper else right
            add_f(anchor, omitted_weight)
        # Scale by the largest weight, N^(s-1), so objective coefficients stay
        # order one for the LP solver. This positive scaling preserves drift sign.
        normalizer = N ** (inversion_moment_order - 1)
        return (constant / normalizer,
                {ident: coefficient / normalizer
                 for ident, coefficient in terms.items()})

    def moment_enclosure_value(solution, t, upper):
        constant, terms = moment_enclosure(t, upper)
        return constant + sum(coefficient * solution[ident]
                              for ident, coefficient in terms.items())

    if inversion_drift_stage is not None and inversion_prev_floor:
        t0 = inversion_drift_stage
        cuts = range(1, N)
        total_ideal = sum(distance_moment_weight(r, q, inversion_moment_order) *
                          min(q, r) for r in cuts)
        floor_terms = {
            zvar(t0, r): distance_moment_weight(r, q, inversion_moment_order)
            for r in cuts
        }
        ub(floor_terms, total_ideal - inversion_prev_floor)

    if root_inversion_cap is not None:
        # For F(r)=min(q,r)-Z(r), sum_{r<N} F(r) is the exact binary
        # inversion count.  The inversion localization lemma puts every
        # possible defect inside [q-I,q+I+1), so only that band needs all cuts.
        left = max(0, q - root_inversion_cap)
        right = min(N, q + root_inversion_cap + 1)
        area_cuts = range(left, right)
        ideal_area = sum(min(q, cut) for cut in area_cuts)
        ub({zvar(0, cut): -1 for cut in area_cuts},
           root_inversion_cap - ideal_area)
        if root_inversion_floor:
            ub({zvar(0, cut): 1 for cut in area_cuts},
               ideal_area - root_inversion_floor)

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

    def bag_rank_prefix_expr(t, key, rank):
        """Global-profile expression for zeros in a bag's first `rank` wires."""
        lev, idx = key
        terms = {}
        remaining = rank
        for lo, hi in flow.bag_intervals(flow.lookup(t, lev, idx), idx):
            take = min(hi - lo, remaining)
            if take > 0:
                terms[zvar(t, lo + take)] = terms.get(zvar(t, lo + take), 0) + 1
                terms[zvar(t, lo)] = terms.get(zvar(t, lo), 0) - 1
                remaining -= take
            if remaining == 0:
                break
        if remaining != 0:
            raise ValueError('bag prefix rank exceeds its allocation')
        return terms

    exact_core_tiles = 0
    if exact_slope_core:
        # Exact reduced model of one tile: first column-sort the incoming
        # Boolean profile, apply slope 35 and sort, then slope 25 and sort.
        # Global prefix variables give each physical input bit by differences
        # of local ranked prefixes. The final sorted row-major profile is
        # wired directly to the sender's Y variables.
        m = row_count
        tile_width = 64 * m

        def add_scaled(dst, src, factor):
            for ident, coeff in src.items():
                dst[ident] = dst.get(ident, 0) + factor * coeff

        def add_pair_sort_hull(a, b, hi, lo):
            # Convex hull of (a,b) in {0,1}^2 mapped to
            # (max(a,b), min(a,b)); the sum equality is added by the caller.
            ub({a: 1, hi: -1}, 0)
            ub({b: 1, hi: -1}, 0)
            ub({lo: 1, a: -1}, 0)
            ub({lo: 1, b: -1}, 0)
            ub({hi: 1, a: -1, b: -1}, 0)
            ub({a: 1, b: 1, lo: -1}, 1)

        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            allocation = flow.allocation(node)
            if allocation % tile_width:
                raise ValueError(
                    f'exact core requires whole tiles: stage={t}, '
                    f'bag=({lev},{idx}), allocation={allocation}, '
                    f'tile_width={tile_width}')
            tiles = allocation // tile_width
            if not tiles:
                continue
            y_at = dict(zip(cuts, yids))
            if m == 1:
                # At row height one both column sorts are identities. The
                # slope-35 stage maps d=c, and the slope-25 stage maps
                # e=35*c mod 64. Encode the resulting permutation directly;
                # allocating X/U/Q binaries here only restates each input bit
                # three times and makes deeper exact-core gates needlessly
                # large.
                input_bits = {}
                for tile in range(tiles):
                    for c in range(64):
                        pos = tile * tile_width + c
                        bit_expr = bag_rank_prefix_expr(
                            t, (lev, idx), pos + 1)
                        add_scaled(bit_expr, bag_rank_prefix_expr(
                            t, (lev, idx), pos), -1)
                        bit_id = new(
                            ('exactCoreBit', t, lev, idx, tile, c),
                            (0, 1), integral=exact_core_boolean)
                        bit_expr[bit_id] = bit_expr.get(bit_id, 0) - 1
                        eq(bit_expr, 0)
                        input_bits[(tile, c)] = {bit_id: 1}
                for cut, y_id in zip(cuts, yids):
                    whole_tiles, rem = divmod(cut, tile_width)
                    terms = {y_id: 1}
                    for tile in range(whole_tiles):
                        for c in range(64):
                            add_scaled(terms, input_bits[(tile, c)], -1)
                    for c in range(64):
                        if (35 * c) % 64 < rem:
                            add_scaled(terms, input_bits[(whole_tiles, c)], -1)
                    eq(terms, 0)
                exact_core_tiles += tiles
                continue
            if m == 2 and exact_core_boolean:
                # A sorted two-bit column is represented by its pair
                # (high, low). After a shuffle, the next sorted column is
                # exactly (a OR b, a AND b). Keep one binary OR variable per
                # output column and express the AND as a+b-OR. This preserves
                # the exact Boolean map while halving intermediate binaries.
                X2, output_profiles = {}, {}
                for tile in range(tiles):
                    for c in range(64):
                        column_input = {}
                        for r in range(2):
                            pos = tile * tile_width + 64 * r + c
                            add_scaled(column_input,
                                       bag_rank_prefix_expr(t, (lev, idx), pos + 1), 1)
                            add_scaled(column_input,
                                       bag_rank_prefix_expr(t, (lev, idx), pos), -1)
                            X2[(tile, c, r)] = new(
                                ('exactCoreX2', t, lev, idx, tile, c, r),
                                (0, 1), integral=True)
                        # The first column sort outputs a prefix of ones.
                        ub({X2[(tile, c, 1)]: 1,
                            X2[(tile, c, 0)]: -1}, 0)
                        terms = {X2[(tile, c, 0)]: 1,
                                 X2[(tile, c, 1)]: 1}
                        add_scaled(terms, column_input, -1)
                        eq(terms, 0)

                    # First shuffle and column sort. For m=2 each destination
                    # receives exactly two bits.
                    first_profile = {}
                    for d in range(64):
                        src = [(c, r) for c in range(64) for r in range(2)
                               if (c + 35 * r) % 64 == d]
                        if len(src) != 2:
                            raise AssertionError('slope-35 m=2 column arity')
                        a = {X2[(tile, c, r)]: 1 for c, r in src[:1]}
                        b = {X2[(tile, c, r)]: 1 for c, r in src[1:]}
                        u0 = new(('exactCoreU2', t, lev, idx, tile, d),
                                 (0, 1), integral=True)
                        ub({**a, u0: -1}, 0)
                        ub({**b, u0: -1}, 0)
                        or_terms = {u0: 1}
                        add_scaled(or_terms, a, -1)
                        add_scaled(or_terms, b, -1)
                        ub(or_terms, 0)
                        u1 = dict(a)
                        add_scaled(u1, b, 1)
                        u1[u0] = u1.get(u0, 0) - 1
                        first_profile[(d, 0)] = {u0: 1}
                        first_profile[(d, 1)] = u1

                    # Second shuffle and final column sort, encoded by the
                    # same OR/AND identity.
                    output_profile = {}
                    for e in range(64):
                        src = [(d, r) for d in range(64) for r in range(2)
                               if (35 * d + 25 * r) % 64 == e]
                        if len(src) != 2:
                            raise AssertionError('slope-25 m=2 column arity')
                        a = first_profile[src[0]]
                        b = first_profile[src[1]]
                        q0 = new(('exactCoreQ2', t, lev, idx, tile, e),
                                 (0, 1), integral=True)
                        ub({**a, q0: -1}, 0)
                        ub({**b, q0: -1}, 0)
                        or_terms = {q0: 1}
                        add_scaled(or_terms, a, -1)
                        add_scaled(or_terms, b, -1)
                        ub(or_terms, 0)
                        q1 = dict(a)
                        add_scaled(q1, b, 1)
                        q1[q0] = q1.get(q0, 0) - 1
                        output_profile[(e, 0)] = {q0: 1}
                        output_profile[(e, 1)] = q1
                    output_profiles[tile] = output_profile

                # Each represented row-major output prefix is tied to the
                # exact transformed bits, across whole and partial tiles.
                for cut, y_id in zip(cuts, yids):
                    whole_tiles, rem = divmod(cut, tile_width)
                    terms = {y_id: 1}
                    for old_tile in range(whole_tiles):
                        for c in range(64):
                            for r in range(2):
                                terms[X2[(old_tile, c, r)]] = -1
                    if rem:
                        full_rows, columns = divmod(rem, 64)
                        for r in range(full_rows):
                            for e in range(64):
                                add_scaled(terms,
                                           output_profiles[whole_tiles][(e, r)], -1)
                        if columns and full_rows < 2:
                            for e in range(columns):
                                add_scaled(terms,
                                           output_profiles[whole_tiles][(e, full_rows)], -1)
                    eq(terms, 0)
                exact_core_tiles += tiles
                continue
            X, U, Q, V, W = {}, {}, {}, {}, {}
            for tile in range(tiles):
                # X[c,r] is the initial column-sorted zero prefix.
                input_prefixes = {}
                for c in range(64):
                    bit_sum = {}
                    for r in range(m):
                        pos = tile * tile_width + r * 64 + c
                        right = bag_rank_prefix_expr(t, (lev, idx), pos + 1)
                        left = bag_rank_prefix_expr(t, (lev, idx), pos)
                        add_scaled(bit_sum, right, 1)
                        add_scaled(bit_sum, left, -1)
                    input_prefixes[c] = bit_sum
                    for r in range(m):
                        X[(tile, c, r)] = new(
                            ('exactCoreX', t, lev, idx, tile, c, r),
                            (0, 1), integral=exact_core_boolean)
                        if r:
                            ub({X[(tile, c, r)]: 1,
                                X[(tile, c, r - 1)]: -1}, 0)
                    xsum = {X[(tile, c, r)]: 1 for r in range(m)}
                    for ident, coeff in input_prefixes[c].items():
                        xsum[ident] = xsum.get(ident, 0) - coeff
                    eq(xsum, 0)

                # First physical shuffle, followed by a column sort.
                for d in range(64):
                    V[(tile, d)] = new(
                        ('exactCoreV', t, lev, idx, tile, d), (0, m))
                    terms = {V[(tile, d)]: 1}
                    for c in range(64):
                        for r in range(m):
                            if (c + 35 * r) % 64 == d:
                                terms[X[(tile, c, r)]] = -1
                    eq(terms, 0)
                    for r in range(m):
                        U[(tile, d, r)] = new(
                            ('exactCoreU', t, lev, idx, tile, d, r),
                            (0, 1), integral=exact_core_boolean)
                        if r:
                            ub({U[(tile, d, r)]: 1,
                                U[(tile, d, r - 1)]: -1}, 0)
                    eq({**{U[(tile, d, r)]: 1 for r in range(m)},
                        V[(tile, d)]: -1}, 0)
                    if pairwise_core_hull:
                        src = [(c, r) for c in range(64) for r in range(2)
                               if (c + 35 * r) % 64 == d]
                        if len(src) != 2:
                            raise AssertionError('slope-35 m=2 column arity')
                        add_pair_sort_hull(
                            X[(tile, *src[0])], X[(tile, *src[1])],
                            U[(tile, d, 0)], U[(tile, d, 1)])

                # Second physical shuffle, followed by the output column sort.
                for e in range(64):
                    W[(tile, e)] = new(
                        ('exactCoreW', t, lev, idx, tile, e), (0, m))
                    terms = {W[(tile, e)]: 1}
                    for d in range(64):
                        for r in range(m):
                            if (35 * d + 25 * r) % 64 == e:
                                terms[U[(tile, d, r)]] = -1
                    eq(terms, 0)
                    for r in range(m):
                        Q[(tile, e, r)] = new(
                            ('exactCoreQ', t, lev, idx, tile, e, r),
                            (0, 1), integral=exact_core_boolean)
                        if r:
                            ub({Q[(tile, e, r)]: 1,
                                Q[(tile, e, r - 1)]: -1}, 0)
                    eq({**{Q[(tile, e, r)]: 1 for r in range(m)},
                        W[(tile, e)]: -1}, 0)
                    if pairwise_core_hull:
                        src = [(d, r) for d in range(64) for r in range(2)
                               if (35 * d + 25 * r) % 64 == e]
                        if len(src) != 2:
                            raise AssertionError('slope-25 m=2 column arity')
                        add_pair_sort_hull(
                            U[(tile, *src[0])], U[(tile, *src[1])],
                            Q[(tile, e, 0)], Q[(tile, e, 1)])

                exact_core_tiles += 1

            # Enforce every currently represented output prefix; the reduced
            # gate uses all global cuts, so this is the complete tile profile.
            for cut, y_id in zip(cuts, yids):
                whole_tiles, rem = divmod(cut, tile_width)
                terms = {y_id: 1}
                for tile in range(whole_tiles):
                    for e in range(64):
                        for r in range(m):
                            terms[Q[(tile, e, r)]] = -1
                if rem:
                    full_rows, columns = divmod(rem, 64)
                    for tile in [whole_tiles]:
                        if full_rows:
                            for e in range(64):
                                for r in range(full_rows):
                                    terms[Q[(tile, e, r)]] = -1
                        if columns and full_rows < m:
                            for e in range(columns):
                                terms[Q[(tile, e, full_rows)]] = -1
                eq(terms, 0)

    def port_expr(t, lev, idx, left, right):
        if left == right:
            return {}
        cuts, yids = ykeys[(t, lev, idx)]
        li, ri = cuts.index(left), cuts.index(right)
        return {yids[ri]: 1, yids[li]: -1}

    aggregate_defect_constraints = 0
    local_cut_defect_constraints = history_local_cut_constraints
    seam_defect_constraints = 0
    if (aggregate_defect_fraction is not None
            or ((local_cut_defect_fraction is not None
                 or local_cut_defect_absolute is not None)
                and not local_cut_history_relaxation)):
        # Exact piecewise-linear encoding of the full-row area
        # A = sum_k (min(H, k*n) - Y(k*n)). The segment selector is binary;
        # all count/profile variables remain continuous unless --integer is
        # separately requested.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            h_id = hvar(t, (lev, idx))
            columns = a // row_count
            Hlo, Hhi = bounds[h_id]
            row_cuts = list(range(columns, a, columns))
            y_at = dict(zip(cuts, yids))
            if not set(row_cuts).issubset(y_at):
                raise ValueError('aggregate budget requires every full-row cut')
            segments = []
            for j in range(row_count):
                lo = j * columns
                hi = min((j + 1) * columns, a)
                if max(lo, Hlo) <= min(hi, Hhi):
                    segments.append((j, lo, hi))
            if not segments:
                raise ValueError('sender mass interval has no row segment')
            selector_ids = []
            area_terms = {y_at[cut]: -1 for cut in row_cuts}
            segment_terms = []
            for j, lo, hi in segments:
                b = new(('Aseg', t, lev, idx, j), (0, 1), integral=True)
                v = new(('Aprod', t, lev, idx, j), (0, max(0, Hhi)))
                selector_ids.append(b)
                segment_terms.append((j, lo, hi, b, v))
                # Select the unique H-interval, using M=a for inactive rows.
                ub({h_id: -1, b: a}, a - lo)
                ub({h_id: 1, b: a}, hi + a)
                # v = b*H, with H in [Hlo,Hhi].
                ub({v: 1, b: -Hhi}, 0)
                ub({v: -1, b: Hlo}, 0)
                ub({v: 1, h_id: -1, b: -Hlo}, -Hlo)
                ub({v: -1, h_id: 1, b: Hhi}, Hhi)
                # In this segment, Q(H)=sum_{k=1}^{m-1}min(H,k*n)
                # is affine with the displayed intercept and slope.
                intercept = columns * j * (j + 1) // 2
                slope = row_count - 1 - j
                area_terms[b] = area_terms.get(b, 0) + intercept
                if slope:
                    area_terms[v] = area_terms.get(v, 0) + slope
            eq({**{b: 1 for b in selector_ids}}, 1)
            if aggregate_defect_fraction is not None:
                ub(area_terms, float(aggregate_defect_fraction * a))
                aggregate_defect_constraints += 1
            if (local_cut_defect_fraction is not None
                    or local_cut_defect_absolute is not None):
                by_row = {j: (b, v) for j, _, _, b, v in segment_terms}
                suffix = {}
                for j in range(row_count + 1):
                    suffix[j] = new(('AsegSuffix', t, lev, idx, j), (0, 1))
                eq({suffix[row_count]: 1}, 0)
                for j in range(row_count - 1, -1, -1):
                    terms = {suffix[j]: 1, suffix[j + 1]: -1}
                    if j in by_row:
                        terms[by_row[j][0]] = -1
                    eq(terms, 0)
                previous_min = None
                for j in range(1, row_count + 1):
                    qid = new(('Amin', t, lev, idx, j),
                              (0, min(a, j * columns)))
                    terms = {qid: 1, suffix[j]: -columns}
                    if previous_min is not None:
                        terms[previous_min] = -1
                    if j - 1 in by_row:
                        b, v = by_row[j - 1]
                        terms[v] = -1
                        terms[b] = terms.get(b, 0) + (j - 1) * columns
                    eq(terms, 0)
                    cut = j * columns
                    if cut in y_at:
                        ub({qid: 1, y_at[cut]: -1},
                           float(local_cut_cap(a)))
                        local_cut_defect_constraints += 1
                    previous_min = qid

    distance_tail_constraints = 0
    if distance_tail_profile:
        # If the entire reachable H interval lies on one side of a local
        # prefix cut s, then d(s)=min(H,s)-Y(s) is a one-sided crossing count.
        # A certified margin-r tail therefore caps it by T(r)*a whenever
        # every allowed H is at least r rows away.  History intervals make
        # these necessary constraints unconditional, without indicator vars.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            columns = a // row_count
            h_id = hvar(t, (lev, idx))
            Hlo, Hhi = history[t].get((lev, idx), (0, 0))
            for cut, yid in zip(cuts, yids):
                if cut == 0 or cut == a or cut % columns:
                    continue
                if Hhi < cut:
                    # d=H-Y; distance is measured in full rows, rounded down.
                    distance_rows = int((cut - Hhi) // columns)
                    defect = {h_id: 1, yid: -1}
                elif Hlo > cut:
                    # d=cut-Y.
                    distance_rows = int((Hlo - cut) // columns)
                    defect = {yid: -1}
                else:
                    continue
                eligible = [(r, cap) for r, cap in distance_tail_profile
                            if r <= distance_rows]
                if eligible:
                    _, cap = eligible[-1]
                    ub(defect, float(cap * a))
                    distance_tail_constraints += 1

    mass_mean_constraints = 0
    if mass_sensitive_mean:
        # Optimistic screen only: impose the profile-uniform random-core mean
        # bound E[A] <= sqrt((n-1)*h*(1-h/a)/8), maximized over each possible
        # sender-mass segment. This is not a fixed-provider tail guarantee.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            h_id = hvar(t, (lev, idx))
            Hlo, Hhi = bounds[h_id]
            columns = a // row_count
            row_cuts = list(range(columns, a, columns))
            y_at = dict(zip(cuts, yids))
            if not set(row_cuts).issubset(y_at):
                raise ValueError('mass-sensitive screen requires every full-row cut')
            segments = []
            for j in range(row_count):
                lo, hi = j * columns, min((j + 1) * columns, a)
                if max(lo, Hlo) <= min(hi, Hhi):
                    segments.append((j, lo, hi))
            selector_ids = []
            for j, lo, hi in segments:
                b = new(('Mseg', t, lev, idx, j), (0, 1), integral=True)
                selector_ids.append(b)
                ub({h_id: -1, b: a}, a - lo)
                ub({h_id: 1, b: a}, hi + a)
                h_left, h_right = max(lo, Hlo), min(hi, Hhi)
                if h_left <= a / 2 <= h_right:
                    h_max = a / 2
                elif h_right < a / 2:
                    h_max = h_right
                else:
                    h_max = a - h_left
                cap = sqrt(max(0.0, (columns - 1) * h_max *
                               (1 - h_max / a) / 8))
                intercept = columns * j * (j + 1) // 2
                slope = row_count - 1 - j
                # If this segment is selected, the affine area formula is
                # exact. 2*a*m safely deactivates all other segment rows.
                big_m = 2 * a * row_count
                terms = {h_id: slope, b: big_m}
                for cut in row_cuts:
                    terms[y_at[cut]] = terms.get(y_at[cut], 0) - 1
                ub(terms, cap + big_m - intercept)
                mass_mean_constraints += 1
            eq({b: 1 for b in selector_ids}, 1)

    propagated_tail_constraints = 0
    propagated_tail_binaries = 0
    if propagated_tail_gap:
        gap = propagated_tail_gap

        def add_profile_tail(name, t, key, a, columns, cut, yid,
                             x_coeffs, x_constant, output_kind):
            """Discretize by whole row-gap mass classes and apply Phi."""
            nonlocal propagated_tail_binaries
            x_id = new(('Ctail', *name), (0, a))
            equation = {x_id: 1}
            for variable_id, coefficient in x_coeffs.items():
                equation[variable_id] = equation.get(variable_id, 0) - coefficient
            eq(equation, x_constant)
            selector_ids = []
            mass_bins = (row_count + gap - 1) // gap
            for j in range(mass_bins + 1):
                if j == 0:
                    lo = hi = 0
                else:
                    lo = (j - 1) * gap * columns
                    hi = min(j * gap * columns, a)
                b = new(('CtailSeg', *name, j), (0, 1), integral=True)
                selector_ids.append(b)
                ub({x_id: -1, b: a}, a - lo)
                ub({x_id: 1, b: a}, hi + a)
                # A whole mass class is charged at its upper endpoint. Take
                # the running maximum so floating/rational rounding in the
                # tail evaluator cannot make the cap decrease with mass.
                escape = max(profile_tail(k * gap * columns, gap,
                                          columns, row_count)
                             for k in range(j + 1))
                out_terms = {yid: -1, b: a}
                rhs = escape + a
                if output_kind == 'zeros':
                    out_terms[hvar(t, key)] = 1
                else:
                    rhs -= cut
                ub(out_terms, rhs)
                propagated_tail_binaries += 1
            eq({b: 1 for b in selector_ids}, 1)

        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            if a == 0 or a % row_count:
                continue
            columns = a // row_count
            y_at = dict(zip(cuts, yids))
            h_id = hvar(t, (lev, idx))
            for cut_rows in range(gap, row_count - gap + 1, gap):
                out_cut = cut_rows * columns
                if out_cut not in y_at:
                    continue
                # Zeros escaping below the cut are bounded from the input
                # suffix after the baseline cut-gap.
                zero_baseline = (cut_rows - gap) * columns
                zero_prefix = bag_rank_prefix_expr(t, (lev, idx), zero_baseline)
                zero_coeffs = {h_id: 1}
                for variable_id, coefficient in zero_prefix.items():
                    zero_coeffs[variable_id] = zero_coeffs.get(variable_id, 0) - coefficient
                add_profile_tail(('zero', t, lev, idx, cut_rows), t,
                                 (lev, idx), a, columns, out_cut, y_at[out_cut],
                                 zero_coeffs, 0, 'zeros')
                # Reflect holes: bound missing zeros before cut_rows using
                # the input holes in the first cut_rows+gap rows.
                hole_rank = (cut_rows + gap) * columns
                hole_prefix = bag_rank_prefix_expr(t, (lev, idx), hole_rank)
                hole_coeffs = {v: -c for v, c in hole_prefix.items()}
                add_profile_tail(('holes', t, lev, idx, cut_rows), t,
                                 (lev, idx), a, columns, out_cut, y_at[out_cut],
                                 hole_coeffs, hole_rank, 'holes')
                propagated_tail_constraints += 2

    if seam_defect_fraction is not None:
        # Retain the pointwise outsider cap only at D2 port boundaries. The
        # minority mass has an interval from the scalar history; use its
        # maximum on that interval, so the imposed cap is a necessary (weak)
        # consequence of d(cut) <= epsilon * min(H, a-H).
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a, pi, blocks = flow.rows[t][node]
            if a == 0 or pi == a:
                continue
            Hlo, Hhi = history[t].get((lev, idx), (0, 0))
            minority_hi = max(min(Hlo, a - Hlo), min(Hhi, a - Hhi),
                              a / 2 if Hlo <= a / 2 <= Hhi else 0)
            base_cuts = {0, a, pi // 2}
            pos = pi // 2
            for width in blocks:
                pos += width
                base_cuts.add(pos)
            base_cuts = {cut for cut in base_cuts if 0 < cut < a}
            y_at = dict(zip(cuts, yids))
            for cut in sorted(base_cuts & y_at.keys()):
                terms = {y_at[cut]: -1}
                constant = 0
                if cut <= Hlo:
                    constant = cut
                elif Hhi <= cut:
                    terms[hvar(t, (lev, idx))] = 1
                else:
                    continue
                ub(terms, float(seam_defect_fraction * minority_hi - constant))
                seam_defect_constraints += 1

    if ordered_prefix:
        global_cuts = cut_data[2]

        def concave_column_profile(name, ks, n, a, hlo, hhi, total_terms=None,
                                   total_value=None):
            """Shared row-prefix profile of one first-column sort."""
            ks = sorted(set(ks) | {0, row_count})
            wids = {}
            for k in ks:
                lower = max(0, hlo - (a - k * n))
                upper = min(hhi, k * n)
                wids[k] = new(('W', *name, k), (lower, upper))
            eq({wids[0]: 1}, 0)
            if total_terms is not None:
                terms = {wids[row_count]: 1}
                for v, coeff in total_terms.items():
                    terms[v] = terms.get(v, 0) - coeff
                eq(terms, 0)
            else:
                eq({wids[row_count]: 1}, total_value)
            for left, right in zip(ks, ks[1:]):
                ub({wids[left]: 1, wids[right]: -1}, 0)
                ub({wids[right]: 1, wids[left]: -1}, n * (right - left))
            for left, mid, right in zip(ks, ks[1:], ks[2:]):
                d1, d2 = mid - left, right - mid
                # Average row gains are nonincreasing: the profile is concave.
                ub({wids[left]: d2, wids[mid]: -(d1 + d2),
                    wids[right]: d1}, 0)
            return wids

        # Keep one common first-column witness across all selected root cuts.
        if transition_source_stage is None and N % row_count == 0:
            root_columns = N // row_count
            root_ks = {min(row_count, cut // root_columns)
                       for cut in global_cuts[0]}
            root_w = concave_column_profile(
                ('root',), root_ks, root_columns, N, q, q, total_value=q
            )
            for cut in global_cuts[0]:
                k = min(row_count, cut // root_columns)
                ub({root_w[k]: 1, zvar(0, cut): -1}, 0)

        # A single concave row-count profile witnesses the first-column output
        # below every selected prefix of each active local 3-sort.
        for (t, lev, idx), (cuts, yids) in ykeys.items():
            node = flow.lookup(t, lev, idx)
            a, pi, _ = flow.rows[t][node]
            if pi == a or a == 0 or a % row_count:
                continue
            n = a // row_count
            hlo, hhi = history[t].get((lev, idx), (0, 0))
            ks = {min(row_count, cut // n) for cut in cuts}
            wids = concave_column_profile(
                ('local', t, lev, idx), ks, n, a, hlo, hhi,
                total_terms={hvar(t, (lev, idx)): 1}
            )
            for cut, yid in zip(cuts, yids):
                k = min(row_count, cut // n)
                ub({wids[k]: 1, yid: -1}, 0)

            # Optional finite test of the profile-conditioned whole-tail
            # contract at the root. The exact first-column lower bound gives
            # T_first(b) <= H - minFirst(H,b*n), then Phi bounds escape over
            # the next `gap` rows. This uses the actual threshold mass q and
            # arbitrary initial root profile; no sorted-root assumption.
            if conditioned_tail_gap and t == 0:
                gap = conditioned_tail_gap
                assert lev == 0 and idx == 0
                yid_at_cut = {cut: yid for cut, yid in zip(cuts, yids)}
                for baseline in range(0, row_count - gap + 1, gap):
                    output_row = baseline + gap
                    output_cut = output_row * n
                    assert output_cut in yid_at_cut, (output_row, n, cuts)
                    first_sort_zeros = minimum_rectangular_prefix_zeros(
                        a, q, baseline * n, rows=row_count
                    )
                    tail_cap = q - first_sort_zeros
                    escape = profile_tail(tail_cap, gap, n, row_count)
                    ub({yid_at_cut[output_cut]: -1}, escape - q)
                    conditioned_tail_constraints += 1

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
                      and active_level(t, lev)]
            ordered_cuts = sorted(global_cuts[t + 1])
            effects = {}
            # A source contributes a nontrivial local-prefix equation only
            # for global cuts strictly inside its occupied wire span. Index
            # those incidences once instead of scanning every source at every
            # global cut (the latter dominates depth-7 model construction).
            for key in active:
                node = flow.lookup(t, *key)
                a, pi, _ = row[node]
                if pi == a or a == 0:
                    continue
                wires = flow.bag_intervals(node, key[1])
                first_wire, last_wire = wires[0][0], wires[-1][1]
                lo = bisect_right(ordered_cuts, first_wire)
                hi = bisect_left(ordered_cuts, last_wire)
                for wire_cut in ordered_cuts[lo:hi]:
                    cut = rank_before(wires, wire_cut)
                    if 0 < cut < a:
                        effects.setdefault(wire_cut, []).append((key, cut))
            for wire_cut in ordered_cuts:
                terms = {zvar(t + 1, wire_cut): 1, zvar(t, wire_cut): -1}
                for key, cut in effects.get(wire_cut, ()):
                    yid = var[('Y', t, *key, cut)]
                    terms[yid] = terms.get(yid, 0) - 1
                    for v, coeff in bag_prefix_expr(t, key, wire_cut).items():
                        terms[v] = terms.get(v, 0) + coeff
                eq(terms, 0)

    # Every active node has one shared cumulative output profile, not
    # independent intervals for each port.
    for t, row in enumerate(flow.rows):
        for (stage, lev, idx), (cuts, yids) in ykeys.items():
            if stage != t:
                continue
            key = (lev, idx)
            node = flow.lookup(t, lev, idx)
            a, pi, _ = row[node]
            h = pi // 2
            eq({yids[0]: 1}, 0)
            eq({yids[-1]: 1, hvar(t, key): -1}, 0)
            for j in range(len(cuts) - 1):
                width = cuts[j + 1] - cuts[j]
                ub({yids[j]: 1, yids[j + 1]: -1}, 0)
                ub({yids[j + 1]: 1, yids[j]: -1}, width)

    exact_refresh_constraints = 0
    if refresh_stages:
        # Optimistic refresh diagnostic: at each selected stage, make every
        # represented local output prefix equal a perfectly sorted bag,
        # Y(s)=min(H,s). This is a cut-level relaxation, not a priced network.
        for t in sorted(refresh_stages):
            for (stage, lev, idx), (cuts, yids) in ykeys.items():
                if stage != t:
                    continue
                a = flow.allocation(flow.lookup(t, lev, idx))
                h_id = hvar(t, (lev, idx))
                for cut, yid in zip(cuts, yids):
                    if cut == 0 or cut == a:
                        continue
                    selector = new(('refreshMin', t, lev, idx, cut), (0, 1),
                                   integral=True)
                    big_m = a
                    # selector=1 selects H<=cut, hence Y=H; selector=0
                    # selects H>=cut, hence Y=cut. Together with monotonicity,
                    # these enforce Y=min(H,cut).
                    ub({h_id: 1, selector: big_m}, cut + big_m)
                    ub({h_id: -1, selector: -big_m}, -cut)
                    ub({h_id: 1, selector: big_m, yid: -1}, big_m)
                    ub({yid: -1, selector: -big_m}, -cut)
                    exact_refresh_constraints += 1

    refresh_alignment_constraints = 0
    if refresh_alignment_cap is not None:
        # At the snapshot immediately after the selected refresh, cap the
        # threshold-cut alignment A=q-sum_B min(H_B,P_B), where P_B is the
        # number of static wires of bag B below q.  Variables M_B <= H_B,P_B
        # plus sum M_B >= q-cap are an exact feasibility encoding of A<=cap:
        # such M_B exist iff the actual sum of minima reaches the target.
        t = exact_refresh_stage + 1
        min_terms = {}
        for key in bag_keys:
            lev, idx = key
            wires = flow.bag_intervals(flow.lookup(t, lev, idx), idx)
            ideal_mass = rank_before(wires, q)
            if ideal_mass <= 0:
                continue
            m_id = new(('refreshAlignmentMin', t, lev, idx),
                       (0, ideal_mass))
            ub({m_id: 1, hvar(t, key): -1}, 0)
            min_terms[m_id] = -1
            refresh_alignment_constraints += 1
        ub(min_terms, -(q - float(refresh_alignment_cap)))
        refresh_alignment_constraints += 1

    # Each next-stage bag is exactly the union of its routed input ports and,
    # when inactive, its retained old contents.
    for t, row in enumerate(flow.rows):
        active_set = {(lev, idx) for lev, idx in bag_keys
                      if active_level(t, lev)}
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
                    # Fully emptied children need no H variable: sparse
                    # bag_keys intentionally contain only addresses with
                    # positive allocation at some stage.  In particular an
                    # active zero-width child has pi == a == 0, but its
                    # contribution to the parent transfer is exactly zero.
                    if a == 0:
                        expr = {}
                    elif pi == a:
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

    # Optional adversary: maximize V_{t+s} - rho*V_t, where
    # V_t = sum_level weight^level * sum_bag |H_b-rank_before(b)|.
    # Absolute values are exact epigraphs because the objective pushes the
    # next-state terms up and the previous-state terms down.
    alignment_abs = {}
    alignment_min = {}
    rank_profile_source_terms = {}
    rank_profile_destination_terms = {}
    rank_profile_exact_terms = {}
    if alignment_drift_stage is not None:
        t0 = alignment_drift_stage
        t1 = t0 + alignment_drift_span
        for t in (t0, t1):
            for key in bag_keys:
                node = flow.lookup(t, *key)
                wires = flow.bag_intervals(node, key[1])
                ideal = rank_before(wires, q)
                h_id = hvar(t, key)
                h_lo, h_hi = bounds[h_id]
                max_abs = max(abs(h_lo - ideal), abs(h_hi - ideal))
                abs_id = new(('alignmentAbs', t, *key), (0, max_abs))
                alignment_abs[(t, key)] = abs_id
                if h_hi <= ideal:
                    eq({abs_id: 1, h_id: 1}, ideal)
                elif h_lo >= ideal:
                    eq({abs_id: 1, h_id: -1}, -ideal)
                else:
                    sign_id = new(('alignmentSign', t, *key), (0, 1),
                                  integral=True)
                    # Exact absolute value: lower epigraph bounds plus big-M
                    # upper bounds selected by the sign bit.
                    ub({h_id: 1, abs_id: -1}, ideal)
                    ub({h_id: -1, abs_id: -1}, -ideal)
                    ub({abs_id: 1, h_id: -1, sign_id: max_abs},
                       max_abs - ideal)
                    ub({abs_id: 1, h_id: 1, sign_id: -max_abs}, ideal)
        if alignment_local_error_weight or alignment_error_weight:
            for t in (t0, t1):
                if t == t1 and not alignment_error_weight:
                    continue
                assert (t, q) in zkeys, "alignment-error objective requires threshold cuts"
                for key in bag_keys:
                    node = flow.lookup(t, *key)
                    wires = flow.bag_intervals(node, key[1])
                    ideal = rank_before(wires, q)
                    if ideal == 0:
                        continue
                    h_id = hvar(t, key)
                    if ideal == flow.allocation(node):
                        alignment_min[(t, key)] = h_id
                        continue
                    h_lo, h_hi = bounds[h_id]
                    big_m = max(abs(h_lo - ideal), abs(h_hi - ideal), ideal)
                    if h_hi <= ideal:
                        m_id = new(('alignmentMin', t, *key), (h_lo, h_hi))
                        eq({m_id: 1, h_id: -1}, 0)
                        alignment_min[(t, key)] = m_id
                        continue
                    if h_lo >= ideal:
                        m_id = new(('alignmentMin', t, *key), (ideal, ideal))
                        alignment_min[(t, key)] = m_id
                        continue
                    m_id = new(('alignmentMin', t, *key), (0, ideal))
                    choose_h = new(('alignmentMinSign', t, *key), (0, 1),
                                   integral=True)
                    alignment_min[(t, key)] = m_id
                    # Exact min(H, ideal), choosing H on sign=1 and ideal on 0.
                    ub({m_id: 1, h_id: -1}, 0)
                    ub({m_id: 1}, ideal)
                    ub({m_id: -1, h_id: 1, choose_h: big_m}, big_m)
                    ub({m_id: -1, choose_h: -big_m}, -ideal)

        if rank_profile_weight:
            assert rank_profile_weight > 0
            for (t, lev, idx), (cuts, yids) in ykeys.items():
                if t not in (t0, t1):
                    continue
                node = flow.lookup(t, lev, idx)
                if node not in flow.rows[t]:
                    continue
                a, pi, blocks = flow.rows[t][node]
                if pi == a:
                    continue
                base_cuts = {0, a}
                h = pi // 2
                base_cuts.add(h)
                pos = h
                for width in blocks:
                    pos += width
                    base_cuts.add(pos)
                h_id = hvar(t, (lev, idx))
                h_lo, h_hi = history[t].get((lev, idx), (0, 0))
                for cut, y_id in zip(cuts, yids):
                    if (cut == 0 or cut == a or
                            (not rank_profile_all_cuts and cut not in base_cuts)):
                        continue
                    if rank_profile_exact:
                        if h_hi <= cut:
                            min_id = h_id
                        elif h_lo >= cut:
                            min_id = new(('rankProfileMin', t, lev, idx, cut),
                                         (cut, cut))
                        else:
                            min_id = new(('rankProfileMin', t, lev, idx, cut),
                                         (0, cut))
                            choose_h = new(('rankProfileMinSign', t, lev, idx, cut),
                                           (0, 1), integral=True)
                            big_m = max(a, cut)
                            ub({min_id: 1, h_id: -1}, 0)
                            ub({min_id: 1}, cut)
                            ub({min_id: -1, h_id: 1, choose_h: big_m}, big_m)
                            ub({min_id: -1, choose_h: -big_m}, -cut)
                        rank_profile_exact_terms[(t, lev, idx, cut)] = (min_id, y_id)
                    elif t == t0:
                        # A lower bound on the true defect, used with the
                        # subtractive source potential: d >= max(0,min(Hlo,s)-Y).
                        lower_ideal = min(h_lo, cut)
                        defect_id = new(('rankProfileSourceLower', t, lev, idx, cut),
                                        (0, lower_ideal))
                        ub({y_id: -1, defect_id: -1}, -lower_ideal)
                        rank_profile_source_terms[(lev, idx, cut)] = defect_id
                    else:
                        # An upper bound on the true defect, used with the
                        # additive destination potential: d <= min(Hhi,s)-Y.
                        upper_ideal = min(h_hi, cut)
                        ideal_id = new(('rankProfileDestinationUpper', t, lev, idx, cut),
                                       (upper_ideal, upper_ideal))
                        rank_profile_destination_terms[(lev, idx, cut)] = (ideal_id, y_id)

    nvars = len(bounds)
    report_progress(f'constraints assembled; variables={nvars}, '
                    f'equalities={len(eq_rows)}, inequalities={len(ub_rows)}')

    def matrix(rows):
        rr, cc, dd = [], [], []
        for i, terms in enumerate(rows):
            for j, value in terms.items():
                if value:
                    rr.append(i); cc.append(j); dd.append(float(value))
            if progress_enabled and i and i % 100000 == 0:
                report_progress(f'sparse conversion rows={i}/{len(rows)}; '
                                f'nonzeros={len(dd)}')
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
                  and active_level(t, lev)]
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
                refresh_key = ('refreshMin', t, lev, idx, cut)
                if refresh_key in var:
                    witness[var[refresh_key]] = int(mass <= cut)
            if variance_port_l1_gamma is not None and a % row_count == 0:
                boundaries = {0, a, pi // 2}
                pos = pi // 2
                for width in blocks:
                    pos += width
                    boundaries.add(pos)
                boundaries = sorted(boundaries)
                for cut in boundaries:
                    ideal_key = ('variancePortIdeal', t, lev, idx, cut)
                    if ideal_key in var:
                        witness[var[ideal_key]] = min(mass, cut)
                    selector_key = ('variancePortIdealSign', t, lev, idx, cut)
                    if selector_key in var:
                        witness[var[selector_key]] = int(mass <= cut)
                for left, right in zip(boundaries, boundaries[1:]):
                    abs_key = ('variancePortAbs', t, lev, idx, left, right)
                    if abs_key in var:
                        witness[var[abs_key]] = 0
            if propagated_tail_gap and a % row_count == 0:
                columns = a // row_count
                mass_bins = (row_count + propagated_tail_gap - 1) // propagated_tail_gap
                wires = flow.bag_intervals(node, idx)
                ideal_mass = rank_before(wires, q)
                for cut_rows in range(propagated_tail_gap,
                                      row_count - propagated_tail_gap + 1,
                                      propagated_tail_gap):
                    for kind in ('zero', 'holes'):
                        key = ('Ctail', kind, t, lev, idx, cut_rows)
                        if key not in var:
                            continue
                        rank = ((cut_rows - propagated_tail_gap) * columns
                                if kind == 'zero' else
                                (cut_rows + propagated_tail_gap) * columns)
                        tail_mass = (max(0, mass - min(ideal_mass, rank))
                                     if kind == 'zero' else
                                     rank - min(ideal_mass, rank))
                        witness[var[key]] = tail_mass
                        segment = (0 if tail_mass == 0 else
                                   min(mass_bins,
                                       (tail_mass + propagated_tail_gap * columns - 1)
                                       // (propagated_tail_gap * columns)))
                        for j in range(mass_bins + 1):
                            seg_key = ('CtailSeg', kind, t, lev, idx,
                                       cut_rows, j)
                            if seg_key in var:
                                witness[var[seg_key]] = int(j == segment)
            if ((aggregate_defect_fraction is not None
                 or local_cut_defect_fraction is not None
                 or local_cut_defect_absolute is not None)
                    and a % row_count == 0):
                columns = a // row_count
                segment = min(row_count - 1, mass // columns)
                for j in range(row_count):
                    seg_key = ('Aseg', t, lev, idx, j)
                    prod_key = ('Aprod', t, lev, idx, j)
                    if seg_key in var:
                        witness[var[seg_key]] = int(j == segment)
                        witness[var[prod_key]] = mass if j == segment else 0
                if (local_cut_defect_fraction is not None
                        or local_cut_defect_absolute is not None):
                    selected = int(segment)
                    for j in range(row_count + 1):
                        suffix_key = ('AsegSuffix', t, lev, idx, j)
                        if suffix_key in var:
                            witness[var[suffix_key]] = int(selected >= j)
                    for j in range(1, row_count + 1):
                        min_key = ('Amin', t, lev, idx, j)
                        if min_key in var:
                            witness[var[min_key]] = min(mass, j * columns)
            if mass_sensitive_mean and a % row_count == 0:
                columns = a // row_count
                segment = min(row_count - 1, mass // columns)
                for j in range(row_count):
                    seg_key = ('Mseg', t, lev, idx, j)
                    if seg_key in var:
                        witness[var[seg_key]] = int(j == segment)
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
        if (refresh_alignment_cap is not None
                and t + 1 == exact_refresh_stage + 1):
            for key in bag_keys:
                variable_key = ('refreshAlignmentMin', t + 1, *key)
                if variable_key in var:
                    wires = flow.bag_intervals(
                        flow.lookup(t + 1, *key), key[1])
                    ideal_mass = rank_before(wires, q)
                    witness[var[variable_key]] = min(W.get(key, 0), ideal_mass)
    for key in bag_keys:
        witness[hvar(T, key)] = W.get(key, 0)
    for (t, key), abs_id in alignment_abs.items():
        node = flow.lookup(t, *key)
        ideal = rank_before(flow.bag_intervals(node, key[1]), q)
        witness[abs_id] = abs(witness[hvar(t, key)] - ideal)
    for variable_key, variable_id in var.items():
        if variable_key[0] not in ('alignmentMin', 'alignmentMinSign'):
            continue
        _, t, lev, idx = variable_key
        node = flow.lookup(t, lev, idx)
        ideal = rank_before(flow.bag_intervals(node, idx), q)
        mass = witness[hvar(t, (lev, idx))]
        if variable_key[0] == 'alignmentMin':
            witness[variable_id] = min(mass, ideal)
        else:
            witness[variable_id] = int(mass <= ideal)
    for variable_key, variable_id in var.items():
        if variable_key[0] != 'W':
            continue
        if variable_key[1] == 'root':
            k = variable_key[-1]
            columns = N // row_count
            witness[variable_id] = min(q, k * columns)
        else:
            _, _, t, lev, idx, k = variable_key
            node = flow.lookup(t, lev, idx)
            a = flow.allocation(node)
            n = a // row_count
            witness[variable_id] = min(witness[hvar(t, (lev, idx))], k * n)

    # Default objective: maximize total wrong mass outside the one
    # threshold-straddling terminal native interval. All other wholly
    # one-colored blocks must be pure.
    c = np.zeros(nvars)
    constant = 0
    bad = 0
    alignment_floor_row = None
    if alignment_drift_stage is None and inversion_drift_stage is None:
        for lev, idx in bag_keys:
            if terminal_error_level is not None and lev != terminal_error_level:
                continue
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
    elif alignment_drift_stage is not None:
        t0 = alignment_drift_stage
        t1 = t0 + alignment_drift_span
        def level_weight(level, next_phase=False, key=None):
            weights = (alignment_next_level_weights
                       if next_phase and alignment_next_level_weights is not None
                       else alignment_level_weights)
            if weights is None:
                return float(alignment_weight) ** level
            if len(weights) == 2 * (depth + 1):
                assert key is not None
                size = flow.native(level)
                is_spine = key[1] * size < q < (key[1] + 1) * size
                offset = 0 if is_spine else depth + 1
                return float(weights[offset + level])
            return float(weights[level]) if level < len(weights) else 0.0
        for key in bag_keys:
            level = key[0]
            c[alignment_abs[(t0, key)]] += (float(alignment_drift_rho) *
                                             level_weight(level, key=key))
            c[alignment_abs[(t1, key)]] -= level_weight(level, next_phase=True, key=key)
        if rank_profile_exact:
            for (t, _lev, _idx, _cut), (min_id, y_id) in rank_profile_exact_terms.items():
                coeff = (float(alignment_drift_rho) * float(rank_profile_weight)
                         if t == t0 else -float(rank_profile_weight))
                c[min_id] += coeff
                c[y_id] -= coeff
        else:
            for defect_id in rank_profile_source_terms.values():
                c[defect_id] += float(alignment_drift_rho) * float(rank_profile_weight)
            for ideal_id, y_id in rank_profile_destination_terms.values():
                c[ideal_id] -= float(rank_profile_weight)
                c[y_id] += float(rank_profile_weight)
        if alignment_prev_floor:
            floor_terms = {
                alignment_abs[(t0, key)]:
                    (-1.0 if alignment_prev_floor_unweighted
                     else -level_weight(key[0], key=key))
                for key in bag_keys
            }
            alignment_floor_row = len(ub_rows)
            ub(floor_terms, -float(alignment_prev_floor))
        error_coefficients = {
            t0: (float(alignment_drift_rho) * float(alignment_error_weight)
                 + float(alignment_local_error_weight)),
            t1: -float(alignment_error_weight),
        }
        for t, coeff in error_coefficients.items():
            if coeff:
                for key, min_id in alignment_min.items():
                    if key[0] == t:
                        c[min_id] += coeff
                c[zvar(t, q)] -= coeff
    elif inversion_sparse_enclosure:
        t0 = inversion_drift_stage
        _, source_lower = moment_enclosure(t0, upper=False)
        _, destination_upper = moment_enclosure(
            t0 + inversion_drift_span, upper=True)
        for ident, coefficient in source_lower.items():
            c[ident] += float(inversion_drift_rho) * coefficient
        for ident, coefficient in destination_upper.items():
            c[ident] -= coefficient
    else:
        t0 = inversion_drift_stage
        for r in range(1, N):
            weight = distance_moment_weight(r, q, inversion_moment_order)
            c[zvar(t0, r)] -= float(inversion_drift_rho) * weight
            c[zvar(t0 + inversion_drift_span, r)] += weight

    report_progress('starting inequality sparse conversion')
    A_ub = matrix(ub_rows)
    report_progress(f'inequality sparse conversion complete; nnz={A_ub.nnz}')
    A_eq = matrix(eq_rows)
    report_progress(f'equality sparse conversion complete; nnz={A_eq.nnz}')
    eq_residual = A_eq @ witness - np.asarray(eq_rhs)
    witness_eq_error = float(np.max(np.abs(eq_residual)))
    worst_eq = int(np.argmax(np.abs(eq_residual)))
    var_by_id = {v: k for k, v in var.items()}
    witness_ub_error = float(max(0, np.max(A_ub @ witness - np.asarray(ub_rhs))))
    witness_bound_error = max(max(lo - value, value - hi, 0)
                              for value, (lo, hi) in zip(witness, bounds))
    witness_integrality_error = float(np.max(np.abs(witness - np.rint(witness))))
    use_milp = integer or bool(integer_ids)
    if use_milp:
        report_progress('starting HiGHS MILP solve')
        integrality = np.ones(nvars, dtype=np.int8) if integer else np.zeros(nvars, dtype=np.int8)
        if integer and continuous_aux_ids:
            integrality[list(continuous_aux_ids)] = 0
        if not integer:
            integrality[list(integer_ids)] = 1
        mip_options = {'time_limit': time_limit, 'mip_rel_gap': 0.0}
        if mip_presolve is not None:
            mip_options['presolve'] = bool(mip_presolve)
        result = milp(
            c, integrality=integrality,
            bounds=Bounds(np.asarray([lo for lo, _ in bounds]),
                          np.asarray([hi for _, hi in bounds])),
            constraints=[
                LinearConstraint(A_ub, -np.inf, np.asarray(ub_rhs)),
                LinearConstraint(A_eq, np.asarray(eq_rhs), np.asarray(eq_rhs)),
            ],
            options=mip_options,
        )
    else:
        report_progress('starting HiGHS LP solve')
        lp_options = {'time_limit': time_limit}
        if lp_presolve is not None:
            lp_options['presolve'] = bool(lp_presolve)
        if simplex_edge_strategy is not None:
            lp_options['simplex_dual_edge_weight_strategy'] = simplex_edge_strategy
        if raw_highspy:
            import highspy
            from scipy.sparse import vstack
            solver = highspy.Highs()
            solver.setOptionValue('output_flag', False)
            solver.setOptionValue('time_limit', float(time_limit))
            solver.setOptionValue('presolve', 'off' if lp_presolve is False else 'on')
            if lp_method == 'highs-ipm':
                solver.setOptionValue('solver', 'ipm')
            else:
                solver.setOptionValue('solver', 'simplex')
            if simplex_edge_strategy is not None:
                solver.setOptionValue('simplex_dual_edge_weight_strategy',
                                      simplex_edge_strategy)
            lower = np.asarray([lo for lo, _ in bounds], dtype=np.float64)
            upper = np.asarray([hi for _, hi in bounds], dtype=np.float64)
            solver.addCols(nvars, np.asarray(c, dtype=np.float64), lower, upper,
                           0, np.zeros(0, dtype=np.int32),
                           np.zeros(0, dtype=np.int32), np.zeros(0, dtype=np.float64))
            rows = vstack([A_ub, A_eq], format='csr')
            row_lower = np.concatenate([
                np.full(len(ub_rhs), -highspy.kHighsInf, dtype=np.float64),
                np.asarray(eq_rhs, dtype=np.float64)])
            row_upper = np.concatenate([np.asarray(ub_rhs, dtype=np.float64),
                                         np.asarray(eq_rhs, dtype=np.float64)])
            solver.addRows(rows.shape[0], row_lower, row_upper, rows.nnz,
                           rows.indptr[:-1].astype(np.int32),
                           rows.indices.astype(np.int32),
                           rows.data.astype(np.float64))
            solver.run()
            model_status = solver.getModelStatus()
            solution = solver.getSolution()
            info = solver.getInfo()
            x = np.asarray(solution.col_value, dtype=np.float64) if solution.value_valid else None
            result = SimpleNamespace(
                x=x,
                success=(model_status == highspy.HighsModelStatus.kOptimal),
                message=f'raw highspy: {model_status}',
                status=0 if model_status == highspy.HighsModelStatus.kOptimal else 4,
                fun=(float(info.objective_function_value) if info.valid else None),
                mip_dual_bound=None, mip_node_count=None)
        else:
            result = linprog(c, A_ub=A_ub, b_ub=np.asarray(ub_rhs),
                             A_eq=A_eq, b_eq=np.asarray(eq_rhs),
                             bounds=bounds, method=lp_method,
                             options=lp_options)
    if result.x is None:
        worst_terms = eq_rows[worst_eq]
        worst_term_items = list(worst_terms.items())
        return dict(depth=depth, stages=T, success=False, message=result.message,
                    solver_fun=getattr(result, 'fun', None),
                    mip_dual_bound=getattr(result, 'mip_dual_bound', None),
                    mip_gap=getattr(result, 'mip_gap', None),
                    variables=nvars, equalities=len(eq_rows), inequalities=len(ub_rows),
                    exact_slope_core=exact_slope_core,
                    exact_core_boolean=exact_core_boolean,
                    pairwise_core_hull=pairwise_core_hull,
                    exact_core_tiles=exact_core_tiles,
                    integer_variable_count=len(integer_ids),
                    sorted_witness_eq_error=witness_eq_error,
                    worst_eq_index=worst_eq,
                    worst_eq_term_count=len(worst_term_items),
                    worst_eq_terms={var_by_id[v]: c for v, c in worst_term_items[:20]},
                    sorted_witness_ub_error=witness_ub_error,
                    sorted_witness_bound_error=witness_bound_error,
                    sorted_witness_integrality_error=witness_integrality_error,
                    integer=integer, lp_method=lp_method)
    solution_eq_error = float(np.max(np.abs(A_eq @ result.x - np.asarray(eq_rhs))))
    solution_ub_error = float(max(0, np.max(A_ub @ result.x - np.asarray(ub_rhs))))
    solution_bound_error = max(max(lo - value, value - hi, 0)
                               for value, (lo, hi) in zip(result.x, bounds))
    if integer:
        solution_integrality_error = float(np.max(np.abs(result.x - np.rint(result.x))))
    elif integer_ids:
        solution_integrality_error = float(np.max(np.abs(
            result.x[list(integer_ids)] - np.rint(result.x[list(integer_ids)])
        )))
    else:
        solution_integrality_error = 0.0
    rounded = np.rint(result.x)
    rounded_eq_error = float(np.max(np.abs(A_eq @ rounded - np.asarray(eq_rhs))))
    rounded_ub_error = float(max(0, np.max(A_ub @ rounded - np.asarray(ub_rhs))))
    rounded_bound_error = max(max(lo - value, value - hi, 0)
                              for value, (lo, hi) in zip(rounded, bounds))
    terminal_wrong = []
    terminal_wrong_mass = 0.0
    for lev, idx in bag_keys:
        if terminal_error_level is not None and lev != terminal_error_level:
            continue
        node = flow.lookup(T, lev, idx)
        a = flow.allocation(node)
        if not a:
            continue
        wires = flow.bag_intervals(node, idx)
        before = sum(max(0, min(hi, q) - lo) for lo, hi in wires)
        after = a - before
        if before == a:
            terminal_wrong.append((lev, idx, a - int(rounded[hvar(T, (lev, idx))])))
            terminal_wrong_mass += a - float(result.x[hvar(T, (lev, idx))])
        elif after == a:
            terminal_wrong.append((lev, idx, int(rounded[hvar(T, (lev, idx))])))
            terminal_wrong_mass += float(result.x[hvar(T, (lev, idx))])
    root_defects = []
    if ordered_prefix:
        for (t, cut), z_id in zkeys.items():
            if t == 0:
                defect = min(q, cut) - int(rounded[z_id])
                if defect:
                    root_defects.append((cut, defect))
    global_profile_deviation = []
    if ordered_prefix:
        for t in range(T + 1):
            stage_cuts = [(cut, z_id) for (stage, cut), z_id in zkeys.items()
                          if stage == t]
            if stage_cuts:
                cut, z_id = max(
                    stage_cuts,
                    key=lambda item: abs(result.x[item[1]] - min(q, item[0]))
                )
                global_profile_deviation.append({
                    'stage': t,
                    'max_abs_deviation': float(abs(result.x[z_id] - min(q, cut))),
                    'worst_cut': cut,
                    'represented_cuts': len(stage_cuts),
                })
    threshold_flux_trace = []
    alignment_partition_trace = []
    if ordered_prefix:
        for t in range(T + 1):
            if (t, q) not in zkeys:
                continue
            alignment = 0.0
            alignment_distance = 0.0
            local_defect = 0.0
            cuts_available = True
            spine_abs = 0.0
            off_spine_abs = 0.0
            off_spine_nonzero = 0
            spine_rows = []
            level_l1 = {}
            spine_level_l1 = {}
            off_spine_level_l1 = {}
            for key in bag_keys:
                node = flow.lookup(t, *key)
                wires = flow.bag_intervals(node, key[1])
                H = result.x[hvar(t, key)]
                P = rank_before(wires, q)
                delta = H - P
                lev, idx = key
                level_l1[lev] = level_l1.get(lev, 0.0) + abs(delta)
                native_size = flow.native(lev)
                native_lo = idx * native_size
                is_spine = native_lo < q < native_lo + native_size
                if is_spine:
                    spine_abs += abs(delta)
                    spine_level_l1[lev] = spine_level_l1.get(lev, 0.0) + abs(delta)
                    if abs(delta) > 1e-6:
                        spine_rows.append((lev, idx, float(delta)))
                else:
                    off_spine_abs += abs(delta)
                    off_spine_level_l1[lev] = (off_spine_level_l1.get(lev, 0.0)
                                               + abs(delta))
                    off_spine_nonzero += int(abs(delta) > 1e-6)
                alignment_distance += bag_alignment_distance_proxy(wires, H, q)
                local_zeros = 0.0
                for lo, hi in wires:
                    right = min(hi, q)
                    if lo < right:
                        if (t, lo) not in zkeys or (t, right) not in zkeys:
                            cuts_available = False
                            continue
                        local_zeros += (result.x[zvar(t, right)] -
                                        result.x[zvar(t, lo)])
                alignment += min(H, P)
                local_defect += min(H, P) - local_zeros
            flux = q - result.x[zvar(t, q)]
            threshold_flux_trace.append({
                'stage': t,
                'global_prefix_defect': float(flux),
                'cross_bag_alignment': float(q - alignment),
                'bag_sorted_inversion_proxy': float(alignment_distance),
                'within_bag_defect': float(local_defect),
                'identity_residual': float(flux - (q - alignment) - local_defect),
                'all_interval_cuts_available': cuts_available,
            })
            alignment_partition_trace.append({
                'stage': t,
                'spine_l1': float(spine_abs),
                'off_spine_l1': float(off_spine_abs),
                'off_spine_nonzero_bags': off_spine_nonzero,
                'spine_bag_mismatches': spine_rows,
                'level_l1': [(int(lev), float(value))
                             for lev, value in sorted(level_l1.items())],
                'spine_level_l1': [(int(lev), float(value))
                                   for lev, value in sorted(spine_level_l1.items())],
                'off_spine_level_l1': [(int(lev), float(value))
                                       for lev, value in sorted(off_spine_level_l1.items())],
            })
    sampled_inversion_bounds = []
    if ordered_prefix and integer:
        for t, cuts in enumerate(cut_data[2]):
            zero_prefix = {cut: int(rounded[zvar(t, cut)]) for cut in cuts}
            area = inversion_area_interval(cuts, zero_prefix, q)
            if area is not None:
                sampled_inversion_bounds.append({
                    'stage': t,
                    'min_inv': area[0],
                    'max_inv': area[1],
                    'cut_count': len(cuts),
                })
    inversion_values = None
    inversion_drift_value = None
    if inversion_drift_stage is not None:
        t0 = inversion_drift_stage
        if inversion_sparse_enclosure:
            source_lower = moment_enclosure_value(result.x, t0, upper=False)
            destination_upper = moment_enclosure_value(
                result.x, t0 + inversion_drift_span, upper=True)
            inversion_values = [source_lower, destination_upper]
            inversion_drift_value = (destination_upper -
                                     float(inversion_drift_rho) * source_lower)
        else:
            inversion_values = [
                float(sum(distance_moment_weight(r, q, inversion_moment_order) *
                          (min(q, r) - result.x[zvar(t, r)])
                          for r in range(1, N)))
                for t in (t0, t0 + inversion_drift_span)
            ]
            inversion_drift_value = (inversion_values[1] -
                                      float(inversion_drift_rho) * inversion_values[0])
    if global_profile_path:
        if not (ordered_prefix and all_global_cuts):
            raise ValueError("saving the exact global profile requires --all-global-cuts")
        profile = {
            "N": N,
            "q": q,
            "stages": {
                str(t): [
                    float(min(q, r) - result.x[zvar(t, r)])
                    for r in range(N + 1)
                ]
                for t in range(T + 1)
            },
        }
        Path(global_profile_path).write_text(json.dumps(profile), encoding="utf-8")
    rank_profile_values = None
    rank_profile_drift = None
    if alignment_drift_stage is not None and rank_profile_weight:
        t0 = alignment_drift_stage
        t1 = t0 + alignment_drift_span
        if rank_profile_exact:
            rank_profile_values = {
                t: float(sum(result.x[min_id] - result.x[y_id]
                             for (stage, _lev, _idx, _cut), (min_id, y_id)
                             in rank_profile_exact_terms.items() if stage == t))
                for t in (t0, t1)
            }
        else:
            rank_profile_values = {
                t0: float(sum(result.x[defect_id]
                              for defect_id in rank_profile_source_terms.values())),
                t1: float(sum(result.x[ideal_id] - result.x[y_id]
                              for ideal_id, y_id
                              in rank_profile_destination_terms.values())),
            }
        rank_profile_drift = (rank_profile_values[t1]
                              - float(alignment_drift_rho) * rank_profile_values[t0])
    alignment_weight_subgradient = None
    if alignment_drift_stage is not None:
        by_stage = {entry['stage']: dict(entry['level_l1'])
                    for entry in alignment_partition_trace}
        t0 = alignment_drift_stage
        t1 = t0 + alignment_drift_span
        source = by_stage.get(t0, {})
        destination = by_stage.get(t1, {})
        def alignment_features(entry, weights):
            if weights is not None and len(weights) == 2 * (depth + 1):
                spine = dict(entry.get('spine_level_l1', []))
                off = dict(entry.get('off_spine_level_l1', []))
                return [spine.get(lev, 0.0) for lev in range(depth + 1)] + [
                    off.get(lev, 0.0) for lev in range(depth + 1)]
            level = dict(entry.get('level_l1', []))
            return [level.get(lev, 0.0) for lev in range(depth + 1)]
        src_weights = alignment_level_weights
        dst_weights = (alignment_next_level_weights
                       if alignment_next_level_weights is not None else src_weights)
        source_values = alignment_features(source, src_weights)
        destination_values = alignment_features(destination, dst_weights)
        if alignment_floor_row is None or alignment_prev_floor_unweighted:
            alignment_weight_subgradient = {
                'source': [(lev, -float(alignment_drift_rho)
                            * source_values[lev]) for lev in range(len(source_values))],
                'destination': [(lev, destination_values[lev])
                                for lev in range(len(destination_values))],
                'floor_marginal': None,
            }
        elif not use_milp:
            floor_marginal = float(result.ineqlin.marginals[alignment_floor_row])
            alignment_weight_subgradient = {
                'source': [(lev, -(float(alignment_drift_rho) + floor_marginal)
                            * source_values[lev]) for lev in range(len(source_values))],
                'destination': [(lev, destination_values[lev])
                                for lev in range(len(destination_values))],
                'floor_marginal': floor_marginal,
            }
    return dict(depth=depth, stages=T, success=bool(result.success),
                solver_status=getattr(result, 'status', None),
                solver_message=result.message,
                solver_fun=getattr(result, 'fun', None),
                mip_dual_bound=getattr(result, 'mip_dual_bound', None),
                mip_node_count=getattr(result, 'mip_node_count', None),
                objective=('inversion_drift' if inversion_drift_stage is not None
                           else 'alignment_drift' if alignment_drift_stage is not None
                           else 'terminal_wrong_mass'),
                terminal_error_level=terminal_error_level,
                inversion_drift_stage=inversion_drift_stage,
                inversion_drift_rho=(str(inversion_drift_rho)
                                     if inversion_drift_stage is not None else None),
                inversion_moment_order=(inversion_moment_order
                                        if inversion_drift_stage is not None else None),
                inversion_drift_span=(inversion_drift_span
                                      if inversion_drift_stage is not None else None),
                inversion_prev_floor=(float(inversion_prev_floor)
                                      if inversion_drift_stage is not None else None),
                inversion_sparse_enclosure=(bool(inversion_sparse_enclosure)
                                            if inversion_drift_stage is not None else None),
                inversion_moment_normalized=(bool(inversion_sparse_enclosure)
                                             if inversion_drift_stage is not None else None),
                inversion_values=inversion_values,
                max_inversion_drift=inversion_drift_value,
                alignment_drift_stage=alignment_drift_stage,
                alignment_weight=(str(alignment_weight)
                                  if alignment_drift_stage is not None else None),
                alignment_drift_rho=(str(alignment_drift_rho)
                                     if alignment_drift_stage is not None else None),
                alignment_level_weights=(None if alignment_level_weights is None
                                         else tuple(map(str, alignment_level_weights))),
                alignment_next_level_weights=(None if alignment_next_level_weights is None
                                              else tuple(map(str, alignment_next_level_weights))),
                alignment_prev_floor=(float(alignment_prev_floor)
                                      if alignment_drift_stage is not None else None),
                alignment_local_error_weight=(str(alignment_local_error_weight)
                                              if alignment_drift_stage is not None else None),
                alignment_drift_span=(alignment_drift_span
                                      if alignment_drift_stage is not None else None),
                alignment_error_weight=(str(alignment_error_weight)
                                        if alignment_drift_stage is not None else None),
                max_alignment_drift=(float(-result.fun)
                                     if alignment_drift_stage is not None else None),
                rank_profile_weight=(str(rank_profile_weight)
                                     if alignment_drift_stage is not None else None),
                rank_profile_exact=rank_profile_exact,
                rank_profile_all_cuts=rank_profile_all_cuts,
                exact_slope_core=exact_slope_core,
                exact_core_boolean=exact_core_boolean,
                pairwise_core_hull=pairwise_core_hull,
                exact_core_tiles=exact_core_tiles,
                mip_gap=getattr(result, 'mip_gap', None),
                variables=nvars, integer=integer, lp_method=lp_method,
                piecewise_binary_count=len(integer_ids),
                used_milp=use_milp,
                ordered_prefix=ordered_prefix, root_error=root_error,
                root_tail=root_tail, all_row_dominance=all_row_dominance,
                row_stride=row_stride,
                dominance_only_extra_cuts=dominance_only_extra_cuts,
                conditioned_tail_gap=conditioned_tail_gap,
                conditioned_tail_constraints=conditioned_tail_constraints,
                aggregate_defect_fraction=(None if aggregate_defect_fraction is None
                                           else str(aggregate_defect_fraction)),
                aggregate_defect_constraints=aggregate_defect_constraints,
                local_cut_defect_fraction=(None if local_cut_defect_fraction is None
                                           else str(local_cut_defect_fraction)),
                local_cut_defect_absolute=(None if local_cut_defect_absolute is None
                                           else str(local_cut_defect_absolute)),
                local_cut_defect_constraints=local_cut_defect_constraints,
                column_profile_monotone=column_profile_monotone,
                column_profile_constraints=column_profile_constraints,
                variance_prefix_area_gamma=(None if variance_prefix_area_gamma is None
                                            else str(variance_prefix_area_gamma)),
                variance_prefix_area_constraints=variance_prefix_area_constraints,
                variance_port_l1_constraints=variance_port_l1_constraints,
                variance_port_l1_gamma=(None if variance_port_l1_gamma is None
                                        else str(variance_port_l1_gamma)),
                cardinality_prefix_relaxation=cardinality_prefix_relaxation,
                local_cut_history_relaxation=local_cut_history_relaxation,
                mass_sensitive_mean=mass_sensitive_mean,
                mass_mean_constraints=mass_mean_constraints,
                propagated_tail_gap=propagated_tail_gap,
                propagated_tail_constraints=propagated_tail_constraints,
                propagated_tail_binaries=propagated_tail_binaries,
                exact_refresh_stage=exact_refresh_stage,
                exact_refresh_stages=sorted(refresh_stages),
                exact_refresh_constraints=exact_refresh_constraints,
                refresh_alignment_cap=(None if refresh_alignment_cap is None
                                       else float(refresh_alignment_cap)),
                refresh_alignment_stage=(None if refresh_alignment_cap is None
                                        else exact_refresh_stage + 1),
                refresh_alignment_constraints=refresh_alignment_constraints,
                  distance_tail_profile=[(r, str(cap))
                                         for r, cap in distance_tail_profile],
                  distance_tail_constraints=distance_tail_constraints,
                seam_defect_fraction=(None if seam_defect_fraction is None
                                      else str(seam_defect_fraction)),
                seam_defect_constraints=seam_defect_constraints,
                equalities=len(eq_rows), inequalities=len(ub_rows),
                sorted_witness_eq_error=witness_eq_error,
                sorted_witness_ub_error=witness_ub_error,
                sorted_witness_bound_error=witness_bound_error,
                sorted_witness_integrality_error=witness_integrality_error,
                solution_eq_error=solution_eq_error,
                solution_ub_error=solution_ub_error,
                solution_bound_error=solution_bound_error,
                solution_integrality_error=solution_integrality_error,
                terminal_noncrossing_blocks=(bad if alignment_drift_stage is None
                                             else None),
                max_total_wrong=(int(round(constant - result.fun))
                                 if alignment_drift_stage is None
                                 and np.max(np.abs(result.x - rounded)) < 1e-6
                                 else (float(constant - result.fun)
                                       if alignment_drift_stage is None else None)),
                terminal_wrong_mass_at_solution=float(terminal_wrong_mass),
                integral_solution=bool(np.max(np.abs(result.x - np.round(result.x))) < 1e-6),
                rounded_solution_valid=(rounded_eq_error == 0 and rounded_ub_error == 0
                                        and rounded_bound_error == 0),
                max_single_terminal_wrong=max((x[2] for x in terminal_wrong), default=0),
                terminal_wrong_sample=terminal_wrong[:8],
                root_prefix_defect_sample=root_defects[:12],
                global_profile_deviation=global_profile_deviation,
                threshold_flux_trace=threshold_flux_trace,
                sampled_inversion_bounds=sampled_inversion_bounds,
                alignment_partition_trace=alignment_partition_trace,
                alignment_weight_subgradient=alignment_weight_subgradient,
                rank_profile_values=rank_profile_values,
                rank_profile_drift=rank_profile_drift,
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
                    help='initialize with the rank-tail envelope at selected root cuts')
    ap.add_argument('--all-row-dominance', action='store_true',
                    help='add every active node full-row boundary to the cut closure')
    ap.add_argument('--row-stride', type=int, default=1,
                    help='sample every this many row boundaries (must divide 2**row_bits)')
    ap.add_argument('--dominance-only-extra-cuts', action='store_true',
                    help='use only combinatorial bounds at added row cuts; retain tail bounds at port cuts')
    ap.add_argument('--params', nargs=3, type=int, default=(2, 3, 2),
                    metavar=('X', 'Y', 'Z'))
    ap.add_argument('--row-bits', type=int, default=12)
    ap.add_argument('--integer', action='store_true',
                    help='require integral global counts and local output profiles (MILP)')
    ap.add_argument('--time-limit', type=float, default=120,
                    help='LP/MILP solver time limit in seconds (default: 120)')
    ap.add_argument('--lp-method', choices=('highs', 'highs-ds', 'highs-ipm'),
                    default='highs', help='SciPy HiGHS LP algorithm')
    ap.add_argument('--no-presolve', action='store_true',
                    help='disable HiGHS presolve for numerical diagnostics')
    ap.add_argument('--simplex-edge-strategy',
                    choices=('dantzig', 'devex', 'steepest', 'steepest-devex'),
                    default=None, help='HiGHS dual-simplex edge-weight strategy')
    ap.add_argument('--raw-highspy', action='store_true',
                    help='use highspy directly for LP status/solve diagnostics')
    ap.add_argument('--transition-source-stage', type=int, default=None,
                    help='start a drift gate from any profile within this stage\'s scalar history bounds')
    ap.add_argument('--transition-source-span', type=int, default=1,
                    help='number of actual schedule transitions in a shifted-source gate')
    ap.add_argument('--conditioned-tail-gap', type=int, default=0,
                    help='add root whole-tail constraints at this row-gap (requires sampled row cuts)')
    ap.add_argument('--aggregate-defect-fraction', default=None,
                    help='impose a necessary relaxation of full-row aggregate defects <= fraction * bag size; requires all row cuts')
    ap.add_argument('--local-cut-defect-fraction', default=None,
                    help='bound each full-row local prefix defect by fraction * bag size; requires all row cuts')
    ap.add_argument('--local-cut-defect-absolute', default=None,
                    help='bound each full-row local prefix defect by an absolute wire count; requires all row cuts')
    ap.add_argument('--cardinality-prefix-relaxation', action='store_true',
                    help='with the local B2 cut cap, replace other profile-tail bounds by cardinality bounds')
    ap.add_argument('--local-cut-history-relaxation', action='store_true',
                    help='replace exact min(H,cut) B2 linearization by its history lower-bound consequence')
    ap.add_argument('--column-profile-monotone', action='store_true',
                    help='require sampled row-band occupancies to decrease after the final column sort')
    ap.add_argument('--variance-prefix-area-gamma', default=None,
                    help='impose disjoint local area cones implied by A_w <= gamma * columns')
    ap.add_argument('--variance-port-l1-gamma', default=None,
                    help='impose aggregate sender port error l1 <= sqrt(2*gamma) * columns')
    ap.add_argument('--variance-port-l1-residue', action='store_true',
                    help='replace the uniform half-column rank-map correction by its exact H mod columns value (adds integer residue selectors)')
    ap.add_argument('--terminal-error-level', type=int, default=None,
                    help='optimize terminal address error only at this tree level (models a grouped merge frontier)')
    ap.add_argument('--seam-defect-fraction', default=None,
                    help='impose necessary pointwise defect caps at D2 port cuts, relative to sender minority mass')
    ap.add_argument('--mass-sensitive-mean', action='store_true',
                    help='optimistic screen using the random-core profile-uniform expected-area bound (not a fixed-provider guarantee)')
    ap.add_argument('--propagated-tail-gap', type=int, default=0,
                    help='apply mass-conditioned whole-tail bounds at active-sender row cuts separated by this gap (gap must align with --row-stride; stride 1 uses every row cut)')
    ap.add_argument('--distance-tail-profile', default='',
                    help='certified row-margin caps, e.g. 512=3/1000,1024=1/1000; applies where H history is separated from cut')
    ap.add_argument('--all-global-cuts', action='store_true',
                    help='retain every static-wire prefix cut (small-instance exact potential diagnostic)')
    ap.add_argument('--exact-slope-core', action='store_true',
                    help='encode the slope-35/slope-25 two-shuffle core on reduced whole tiles with Boolean occupancies (requires all global cuts)')
    ap.add_argument('--continuous-slope-core', action='store_true',
                    help='also enable the tile core but relax its Boolean occupancies to [0,1] for an LP upper-bound gate')
    ap.add_argument('--pairwise-slope-core-hull', action='store_true',
                    help='add exact two-input sorting convex-hull constraints for the row-height-two continuous core')
    ap.add_argument('--all-root-cuts', action='store_true',
                    help='retain every initial wire prefix, for exact root inversion accounting')
    ap.add_argument('--root-inversion-cap', type=int, default=None,
                    help='bound exact root inversion count using the q±I localized cut band')
    ap.add_argument('--root-inversion-floor', type=int, default=0,
                    help='require at least this many root inversions (requires --root-inversion-cap)')
    ap.add_argument('--exact-refresh-stage', type=int, default=None,
                    help='optimistically force all represented local output prefixes at this stage to be perfectly sorted')
    ap.add_argument('--exact-refresh-stages', default='',
                    help='comma-separated transition indices to optimistically sort at every selected phase')
    ap.add_argument('--refresh-alignment-cap', default=None,
                    help='also cap A=q-sum_B min(H_B,P_B) after the selected refresh (absolute wire count)')
    ap.add_argument('--alignment-drift-stage', type=int, default=None,
                    help='maximize V[t+span]-rho*V[t] for the level-weighted bag-alignment potential')
    ap.add_argument('--alignment-drift-span', type=int, default=1,
                    help='number of D2 transitions in the alignment drift gate')
    ap.add_argument('--alignment-weight', default='1/4',
                    help='geometric level weight in V, as a rational (default 1/4)')
    ap.add_argument('--alignment-level-weights', default='',
                    help='optional comma-separated source-phase weights by level')
    ap.add_argument('--alignment-next-level-weights', default='',
                    help='optional comma-separated destination-phase weights by level')
    ap.add_argument('--alignment-drift-rho', default='1',
                    help='rho in the adversarial drift objective V[t+1]-rho*V[t]')
    ap.add_argument('--alignment-prev-floor', type=float, default=0,
                    help='require V[t] to be at least this many weighted wires in the drift gate')
    ap.add_argument('--alignment-prev-floor-unweighted', action='store_true',
                    help='interpret alignment-prev-floor as a floor on total bag L1')
    ap.add_argument('--rank-profile-weight', default='0',
                    help='weight on the sum of local prefix defects over retained port cuts')
    ap.add_argument('--rank-profile-exact', action='store_true',
                    help='encode exact min(H,s) at retained profile cuts with binary selectors')
    ap.add_argument('--rank-profile-all-cuts', action='store_true',
                    help='include every retained local profile cut, not just sender port boundaries')
    ap.add_argument('--alignment-local-error-weight', default='0',
                    help='C in the drift objective V[t+span]-rho*V[t]-C*localDefect[t]')
    ap.add_argument('--alignment-error-weight', default='0',
                    help='lambda in the coupled potential V+lambda*localDefect')
    ap.add_argument('--inversion-drift-stage', type=int, default=None,
                    help='maximize exact M_s[t+span]-rho*M_s[t]; requires --all-global-cuts')
    ap.add_argument('--inversion-drift-rho', default='1',
                    help='rho in the exact inversion drift objective (default: 1)')
    ap.add_argument('--inversion-prev-floor', type=int, default=0,
                    help='require at least this much order-s moment before the tested transition')
    ap.add_argument('--inversion-moment-order', type=int, default=1,
                    help='distance-moment order for exact all-cut drift (default: 1, inversions)')
    ap.add_argument('--inversion-drift-span', type=int, default=1,
                    help='number of D2 transitions spanned by the exact moment drift')
    ap.add_argument('--inversion-sparse-enclosure', action='store_true',
                    help='bound omitted moment cuts by monotonicity of prefix defect; permits sparse global cuts')
    ap.add_argument('--save-global-profile', default='',
                    help='write exact all-cut prefix defects by stage to JSON')
    args = ap.parse_args()
    print('GLOBAL COUPLED LP/MILP ADVERSARY; not a sorting proof')
    print(solve(args.depth, args.scale, F(args.threshold), args.ordered_prefix,
                args.root_error, args.root_tail, args.all_row_dominance,
                args.row_stride, args.dominance_only_extra_cuts,
                args.integer, args.time_limit, tuple(args.params),
                1 << args.row_bits,
                (args.exact_slope_core or args.continuous_slope_core
                 or args.pairwise_slope_core_hull),
                args.conditioned_tail_gap,
                None if args.aggregate_defect_fraction is None
                else F(args.aggregate_defect_fraction),
                None if args.seam_defect_fraction is None
                else F(args.seam_defect_fraction),
                None if args.local_cut_defect_fraction is None
                else F(args.local_cut_defect_fraction),
                args.mass_sensitive_mean, args.propagated_tail_gap,
                args.all_global_cuts, args.root_inversion_cap,
                 args.all_root_cuts,
                 tuple((int(entry.split('=')[0]), entry.split('=')[1])
                       for entry in args.distance_tail_profile.split(',')
                       if entry),
                 args.root_inversion_floor, args.lp_method,
                 args.exact_refresh_stage,
                 None if args.refresh_alignment_cap is None
                 else F(args.refresh_alignment_cap),
                 tuple(int(t) for t in args.exact_refresh_stages.split(',')
                       if t.strip()),
                 args.alignment_drift_stage, F(args.alignment_weight),
                 F(args.alignment_drift_rho), args.alignment_prev_floor,
                 F(args.alignment_local_error_weight),
                 args.alignment_drift_span, F(args.alignment_error_weight),
                 args.inversion_drift_stage, F(args.inversion_drift_rho),
                 args.inversion_prev_floor, args.inversion_moment_order,
                 args.inversion_drift_span,
                 tuple(F(w) for w in args.alignment_level_weights.split(',') if w.strip()) or None,
                 tuple(F(w) for w in args.alignment_next_level_weights.split(',') if w.strip()) or None,
                 args.alignment_prev_floor_unweighted,
                 F(args.rank_profile_weight),
                 args.rank_profile_exact,
                 args.save_global_profile or None,
                 args.rank_profile_all_cuts,
                 args.inversion_sparse_enclosure,
                 False if args.no_presolve else None,
                 args.simplex_edge_strategy,
                 args.raw_highspy,
                 args.transition_source_stage,
                 args.transition_source_span,
                 args.cardinality_prefix_relaxation,
                 args.local_cut_history_relaxation,
                 args.column_profile_monotone,
                 None if args.variance_prefix_area_gamma is None
                 else F(args.variance_prefix_area_gamma),
                 None,
                 None if args.variance_port_l1_gamma is None
                 else F(args.variance_port_l1_gamma),
                 args.terminal_error_level,
                 args.variance_port_l1_residue,
                 not (args.continuous_slope_core or args.pairwise_slope_core_hull),
                  args.pairwise_slope_core_hull,
                  None if args.local_cut_defect_absolute is None
                  else F(args.local_cut_defect_absolute)))
