#!/usr/bin/env python3
"""Exhaustive sparse-edge gate for 64-column row-sort/permutation layers.

After a column sort, top-row one counts and bottom-row zero counts are
nonincreasing sequences. This checks integer partitions for fixed rotations
or row-specific packed permutations. It certifies only the finite local
sparse-load statement; it says nothing about bulk error or global rank
transfer.
"""
from functools import lru_cache
import argparse


N = 64
ROW_STEP = 41
ROW_COUNT = 4096
PACKED_28_OFFSETS = (
    0, 27, 42, 52, 58, 23, 38, 49, 20, 62, 18, 36,
    16, 47, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
)
PACKED_40_OFFSETS = PACKED_28_OFFSETS + tuple(range(28, 40))


def packing_offsets(support):
    """Return the fixed cyclic start for each repaired edge row."""
    if support == 28:
        # Exact pairwise-disjoint schedule for every nonincreasing 28-row
        # profile of total mass at most 28. See sparse_mass_gate below.
        return list(PACKED_28_OFFSETS)
    if support == 40:
        # Appending starts 28,...,39 keeps the maximum load at two through
        # total mass 40 while retaining zero collisions through mass 28.
        return list(PACKED_40_OFFSETS)
    if support == 24:
        return list(PACKED_28_OFFSETS[:24])
    if support == 0:
        return []
    offsets = [0]
    cursor = 0
    for row in range(1, support):
        cursor += (support - 1) // row
        offsets.append(cursor)
    return offsets


@lru_cache(None)
def partitions(total, maximum):
    """All nonincreasing positive integer sequences summing to total."""
    if total == 0:
        return ((),)
    return tuple(
        (first,) + tail
        for first in range(min(total, maximum), 0, -1)
        for tail in partitions(total - first, first)
    )


def top_one_load(parts, columns=N, row_step=ROW_STEP, packing=False,
                 support=None):
    """Column loads of prefix intervals for sparse ones at the top."""
    loads = [0] * columns
    for row, width in enumerate(parts):
        start = (packing_offsets(support)[row] if packing else
                 row_step * row % columns)
        for offset in range(width):
            loads[(start + offset) % columns] += 1
    return loads


def bottom_zero_load(parts, columns=N, row_step=ROW_STEP,
                     row_count=ROW_COUNT, packing=False, support=None):
    """Column loads of suffix intervals for sparse zeros at the bottom."""
    loads = [0] * columns
    for from_bottom, width in enumerate(parts):
        if packing:
            start = packing_offsets(support)[from_bottom]
            for offset in range(width):
                loads[(start + offset) % columns] += 1
        else:
            row = row_count - 1 - from_bottom
            exclusive_end = row_step * row % columns
            for offset in range(width):
                loads[(exclusive_end - offset - 1) % columns] += 1
    return loads


def first_failure(support, columns, row_step, row_count, max_load,
                  packing=False):
    checked = 0
    maxima = {"top": (0, ()), "bottom": (0, ())}
    for mass in range(support + 1):
        for profile in partitions(mass, mass):
            checked += 1
            loads_by_side = (
                ("top", top_one_load(profile, columns, row_step,
                                      packing, support)),
                ("bottom", bottom_zero_load(profile, columns, row_step,
                                             row_count, packing, support)),
            )
            for side, loads in loads_by_side:
                peak = max(loads)
                if peak > maxima[side][0]:
                    maxima[side] = (peak, profile)
                if peak > max_load:
                    return {"mass": mass, "boundary": side, "load": peak,
                            "profile": profile, "checked": checked,
                            "maxima_so_far": maxima}
    return {"mass": None, "checked": checked, "maxima": maxima}


def two_pass_failure(support, columns, first_step, second_step, row_count,
                     max_load=1, ascending_sort=False):
    """Exhaust sparse top/bottom profiles through two shuffle-sort rounds.

    By default the intermediate load vector is sorted descending, matching
    the historical screen. ``ascending_sort`` checks a standard ascending
    comparator sort instead.
    """
    checked = 0
    for mass in range(support + 1):
        for profile in partitions(mass, mass):
            top_first = top_one_load(profile, columns, first_step)
            top_second = top_one_load(
                tuple(sorted(top_first, reverse=not ascending_sort)),
                columns, second_step)
            bottom_first = bottom_zero_load(
                profile, columns, first_step, row_count)
            bottom_second = bottom_zero_load(
                tuple(sorted(bottom_first, reverse=not ascending_sort)), columns,
                second_step, row_count)
            checked += 1
            peak_top, peak_bottom = max(top_second), max(bottom_second)
            if peak_top > max_load or peak_bottom > max_load:
                return {"mass": mass, "profile": profile,
                        "top_peak": peak_top, "bottom_peak": peak_bottom,
                        "checked": checked}
    return {"mass": None, "checked": checked,
            "top_peak": max_load, "bottom_peak": max_load}


def triple_mass_gate(columns=N, row_step=25):
    """Minimum mass forcing three monotone row intervals to hit one cell.

    Translation removes the first row index. For gaps d,e and target x, the
    least nonincreasing profile hitting x in rows 0,d,d+e has mass
      max(a,b,c) + d*max(b,c) + e*c,
    where a,b,c are the forward interval lengths needed at those rows.
    """
    best = (10**9, None)
    checked = 0
    target_reduction_failures = 0
    for d in range(1, columns):
        for e in range(1, columns - d):
            starts = (0, row_step * d % columns,
                      row_step * (d + e) % columns)
            pair_best = 10**9
            start_best = 10**9
            for target in range(columns):
                a, b, c = ((target - start) % columns + 1
                           for start in starts)
                mass = max(a, b, c) + d * max(b, c) + e * c
                checked += 1
                pair_best = min(pair_best, mass)
                if target in starts:
                    start_best = min(start_best, mass)
                if mass < best[0]:
                    best = (mass, (d, e, target, starts, (a, b, c)))
            target_reduction_failures += start_best != pair_best
    return {"minimum_mass_for_triple_hit": best[0],
            "witness": best[1], "cases": checked,
            "target_reduction_failures": target_reduction_failures}


def sparse_mass_gate(edge_rows=24, mass_cap=28, columns=N):
    """Exhaust all sorted edge profiles up to mass_cap on packed rows.

    Profiles may have more active rows than edge_rows; only the sorted edge
    rows are repaired, so truncate each profile before measuring their load.
    """
    offsets = packing_offsets(edge_rows)
    pair_cases = 0
    pairwise_valid = True
    min_forward_slack = columns
    min_reverse_slack = columns
    for i in range(edge_rows):
        for j in range(i + 1, edge_rows):
            distance = (offsets[j] - offsets[i]) % columns
            max_i_width = max_j_width = 0
            for wi in range(1, mass_cap + 1):
                for wj in range(1, wi + 1):
                    # This is exactly the minimum mass of a nonincreasing
                    # profile with widths wi and wj at rows i and j.
                    if (i + 1) * wi + (j - i) * wj > mass_cap:
                        continue
                    pair_cases += 1
                    max_i_width = max(max_i_width, wi)
                    max_j_width = max(max_j_width, wj)
                    pairwise_valid &= (distance >= wi and
                                       columns - distance >= wj)
            if max_i_width:
                min_forward_slack = min(min_forward_slack,
                                        distance - max_i_width)
                min_reverse_slack = min(min_reverse_slack,
                                        columns - distance - max_j_width)
    checked = 0
    for mass in range(mass_cap + 1):
        for profile in partitions(mass, mass):
            loads = [0] * columns
            for row, width in enumerate(profile[:edge_rows]):
                start = offsets[row]
                for offset in range(width):
                    loads[(start + offset) % columns] += 1
            checked += 1
            peak = max(loads)
            if peak > 1:
                return {"edge_rows": edge_rows, "mass_cap": mass_cap,
                        "first_failure_mass": mass, "profile": profile,
                        "peak_load": peak, "checked": checked,
                        "pair_cases": pair_cases,
                        "pairwise_valid": pairwise_valid,
                        "min_forward_slack": min_forward_slack,
                        "min_reverse_slack": min_reverse_slack}
    assert pairwise_valid, "a no-collision profile screen must pass its pairwise certificate"
    return {"edge_rows": edge_rows, "mass_cap": mass_cap,
            "first_failure_mass": None, "peak_load": 1,
            "checked": checked, "pair_cases": pair_cases,
            "pairwise_valid": pairwise_valid,
            "min_forward_slack": min_forward_slack,
            "min_reverse_slack": min_reverse_slack}


def run(support=18, columns=N, row_step=ROW_STEP, row_count=ROW_COUNT,
        max_load=2, search=False, all_steps=False, packing=False,
        mass_cap=None, second_step=None, ascending_sort=False):
    if second_step is not None:
        print({"support_cap": support, "columns": columns,
               "first_step": row_step, "second_step": second_step,
               "row_count": row_count, **two_pass_failure(
                   support, columns, row_step, second_step, row_count,
                   max_load, ascending_sort)}, flush=True)
        return
    if mass_cap is not None:
        if not packing:
            raise ValueError("--mass-cap requires --packing")
        print(sparse_mass_gate(support, mass_cap, columns), flush=True)
        return
    if packing and all_steps:
        raise ValueError("--packing uses row-specific shifts, not a stride search")
    if all_steps:
        results = []
        for step in range(columns):
            result = first_failure(support, columns, step, row_count,
                                   max_load)
            safe = support if result["mass"] is None else result["mass"] - 1
            results.append((safe, step, result))
        results.sort(reverse=True)
        for safe, step, result in results:
            print({"largest_safe_support_through": safe,
                   "tested_through": support, "max_load": max_load,
                   "row_step": step,
                   "first_failure": result}, flush=True)
        return
    if search:
        # The property is monotone in the cap, so the first failing cap gives
        # the exact largest safe support for this fixed rotation schedule.
        for cap in range(support + 1):
            result = first_failure(cap, columns, row_step, row_count,
                                   max_load, packing)
            if result["mass"] is not None:
                print({"largest_safe_support": cap - 1,
                       "first_failure": result, "columns": columns,
                       "max_load": max_load,
                       "row_step": None if packing else row_step,
                       "row_count": row_count},
                      flush=True)
                return
    result = first_failure(support, columns, row_step, row_count,
                           max_load, packing)
    print({"columns": columns, "support_cap": support,
           "max_load": max_load,
           "row_step": None if packing else row_step,
           "row_count": row_count, "packing": packing, **result}, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--support", type=int, default=18)
    parser.add_argument("--columns", type=int, default=N)
    parser.add_argument("--row-step", type=int, default=ROW_STEP)
    parser.add_argument("--second-step", type=int,
                        help="exhaust a two-round top/bottom sparse gate")
    parser.add_argument("--ascending-sort", action="store_true",
                        help="sort intermediate loads in standard ascending order")
    parser.add_argument("--triple-mass-gate", action="store_true",
                        help="minimize the mass needed for a 3-way first-pass hit")
    parser.add_argument("--row-count", type=int, default=ROW_COUNT)
    parser.add_argument("--max-load", type=int, default=2)
    parser.add_argument("--packing", action="store_true",
                        help="use row-specific disjoint intervals and bottom reflection")
    parser.add_argument("--mass-cap", type=int,
                        help="exhaust packed profiles through this total mass")
    parser.add_argument("--search", action="store_true",
                        help="find the first support cap failing the load-2 gate")
    parser.add_argument("--all-steps", action="store_true",
                        help="compare every rotation stride modulo columns")
    args = parser.parse_args()
    if args.triple_mass_gate:
        print(triple_mass_gate(args.columns, args.row_step), flush=True)
        raise SystemExit(0)
    run(args.support, args.columns, args.row_step, args.row_count,
        args.max_load, args.search, args.all_steps, args.packing,
        args.mass_cap, args.second_step, args.ascending_sort)
