#!/usr/bin/env python3
"""Construct a concrete adversarial spill profile for a seeded AKS row core.

This is a finite witness generator, not a universal tail certifier. It freezes
one row-permutation vector with NumPy's PCG64 generator, greedily chooses a set
of output columns whose required input heights have low total mass, pads that
profile to the requested rank, and reports exact spill counts at every row
cut. A found profile is a genuine counterexample to any proposed tail bound
below its observed Q; failure to find one proves nothing.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np


def make_core(k: int, columns: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return np.stack([rng.permutation(columns) for _ in range(k)]).astype(np.uint16)


def greedy_tail_rank_scan(sigma: np.ndarray, k: int, columns: int,
                          p: int, width: int) -> list[dict[str, int]]:
    """Find greedy feasible tail witnesses at all lower-half child ranks."""
    bin_rows = k // p
    child_capacity = bin_rows * columns
    source_columns = np.arange(columns)
    report: list[dict[str, int]] = []
    for rank_bins in range(1, p // 2 + 1):
        cut = rank_bins * bin_rows
        target_mass = rank_bins * child_capacity
        required_ones = k - cut + width
        selected_rows = np.arange(k - required_ones, k)
        single_heights = np.zeros((columns, columns), dtype=np.int16)
        for row in selected_rows:
            single_heights[sigma[row], source_columns] = np.maximum(
                single_heights[sigma[row], source_columns], k - row
            )
        heights = np.zeros(columns, dtype=np.int16)
        available = np.ones(columns, dtype=bool)
        count = 0
        while available.any():
            costs = (
                np.maximum(single_heights, heights[None, :]).sum(axis=1, dtype=np.int64)
                - int(heights.sum())
            )
            costs[~available] = np.iinfo(np.int64).max
            destination = int(np.argmin(costs))
            candidate = np.maximum(heights, single_heights[destination])
            if int(candidate.sum()) > target_mass:
                break
            heights = candidate
            available[destination] = False
            count += 1
        report.append({
            "rank_bins": rank_bins,
            "row_cut": cut,
            "rank_mass": target_mass,
            "greedy_feasible_Q_at_width": count,
            "base_mass_for_last_feasible_Q": int(heights.sum()),
        })
    return report


def build_attack(k: int, columns: int, seed: int, cut: int, width: int,
                 exceptional_columns: int, p: int) -> dict[str, object]:
    if not (0 < cut < k and 0 < width <= k - cut):
        raise ValueError("require 0 < cut < k and 0 < width <= k-cut")
    if p < 2 or k % p:
        raise ValueError("p must be at least two and divide k")
    if exceptional_columns > columns:
        raise ValueError("exceptional column count exceeds matrix width")

    sigma = make_core(k, columns, seed)
    source_columns = np.arange(columns)
    # To spill width rows above `cut`, force ones into the bottom `cut+width`
    # output rows. A source height h contains row r (0-based) iff h >= k-r.
    required_rows = np.arange(k - cut - width, k)
    single_column_heights = np.zeros((columns, columns), dtype=np.int16)
    for row in required_rows:
        single_column_heights[sigma[row], source_columns] = np.maximum(
            single_column_heights[sigma[row], source_columns], k - row
        )

    heights = np.zeros(columns, dtype=np.int16)
    available = np.ones(columns, dtype=bool)
    selected: list[int] = []
    for _ in range(exceptional_columns):
        # Greedily minimize the extra mass needed to force one more output
        # column to contain all required rows. This is a heuristic set search.
        costs = (
            np.maximum(single_column_heights, heights[None, :]).sum(axis=1, dtype=np.int64)
            - int(heights.sum())
        )
        costs[~available] = np.iinfo(np.int64).max
        destination = int(np.argmin(costs))
        heights = np.maximum(heights, single_column_heights[destination])
        available[destination] = False
        selected.append(destination)

    base_mass = int(heights.sum())
    target_mass = k * columns // 2
    if base_mass > target_mass:
        raise ValueError(f"greedy witness needs {base_mass} ones, above target {target_mass}")

    # Padding only adds ones, so it preserves every selected output column.
    remaining = target_mass - base_mass
    for source in range(columns):
        addition = min(remaining, k - int(heights[source]))
        heights[source] += addition
        remaining -= addition
        if remaining == 0:
            break
    if remaining:
        raise AssertionError("failed to pad to the target mass")

    output_ones = np.zeros(columns, dtype=np.int32)
    for row in range(k):
        output_ones[sigma[row]] += heights >= k - row

    minimum_selected_ones = int(output_ones[selected].min())
    threshold = k - cut + width
    if minimum_selected_ones < threshold:
        raise AssertionError("constructed selected column missed its target occupancy")

    # For each rank/cut use the minority orientation that can fit on one side.
    cut_rows = np.arange(1, k)
    leak_by_cut: list[int] = []
    q_widths = sorted(w for w in set((1, max(1, width // 2), width - 1, width,
                                      width + 1, 2 * width, 3 * width, 4 * width)) if w > 0)
    q_by_width: dict[int, list[int]] = {w: [] for w in q_widths}
    middle_spill: np.ndarray | None = None
    for row_cut in cut_rows:
        bottom_capacity = k - int(row_cut)
        if target_mass <= bottom_capacity * columns:
            spill = np.maximum(0, output_ones - bottom_capacity)
        else:
            spill = np.maximum(0, bottom_capacity - output_ones)
        if int(row_cut) == cut:
            middle_spill = spill
        leak_by_cut.append(int(spill.sum()))
        for w, values in q_by_width.items():
            values.append(int(np.count_nonzero(spill >= w)))

    best_cuts = {
        str(w): {
            "max_Q": max(values),
            "cuts_attaining_max": (
                [int(cut_rows[i]) for i, q in enumerate(values) if q == max(values)]
                if max(values) > 0 else []
            ),
        }
        for w, values in q_by_width.items()
    }
    assert middle_spill is not None
    bin_rows = k // p
    long_spill = {
        str(ell): int(np.maximum(0, middle_spill - ell * bin_rows).sum())
        for ell in range(5)
    }
    core_bytes = sigma.astype("<u2", copy=False).tobytes()
    input_bytes = heights.astype("<u2", copy=False).tobytes()
    return {
        "parameters": {
            "k": k, "columns": columns, "p": p,
            "seed": seed, "numpy": np.__version__, "generator": "PCG64",
            "middle_cut": cut, "spill_width": width,
            "selected_output_columns": exceptional_columns,
            "target_rank_mass": target_mass,
        },
        "witness": {
            "base_mass_before_padding": base_mass,
            "padding_ones": target_mass - base_mass,
            "minimum_selected_output_ones": minimum_selected_ones,
            "spill_threshold": threshold,
            "selected_destinations": selected,
            "input_heights": heights.astype(int).tolist(),
        },
        "observed_profile": {
            "max_leakage_over_all_row_cuts": max(leak_by_cut),
            "cuts_attaining_max_leakage": [int(cut_rows[i]) for i, x in enumerate(leak_by_cut) if x == max(leak_by_cut)],
            "max_leakage_fraction_of_rank": max(leak_by_cut) / target_mass,
            "Q_by_width_over_all_row_cuts": best_cuts,
            "middle_cut_long_spill_mass_by_bins": long_spill,
        },
        "greedy_rank_scan_at_bin_boundaries": greedy_tail_rank_scan(
            sigma, k, columns, p, width
        ),
        "sha256": {
            "core_u16_little_endian": hashlib.sha256(core_bytes).hexdigest(),
            "input_heights_u16_little_endian": hashlib.sha256(input_bytes).hexdigest(),
        },
        "status": "witness only; this does not certify a universal spill-tail bound or the core's all-input E guarantee",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, default=1024)
    parser.add_argument("--columns", type=int, default=1024)
    parser.add_argument("--seed", type=int, default=20261014)
    parser.add_argument("--p", type=int, default=32)
    parser.add_argument("--cut", type=int, default=512)
    parser.add_argument("--width", type=int, default=32)
    parser.add_argument("--exceptional-columns", type=int, default=42)
    parser.add_argument("--save", type=Path, help="write full JSON witness, including input heights")
    parser.add_argument("--save-core", type=Path, help="write exact row permutations as compressed NPZ")
    args = parser.parse_args()
    result = build_attack(args.k, args.columns, args.seed, args.cut,
                          args.width, args.exceptional_columns, args.p)
    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        args.save.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    if args.save_core:
        args.save_core.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.save_core, sigma=make_core(args.k, args.columns, args.seed))
    print(json.dumps({k: v for k, v in result.items() if k != "witness"}, indent=2))
    print(json.dumps({k: v for k, v in result["witness"].items() if k != "input_heights"}, indent=2))


if __name__ == "__main__":
    main()
