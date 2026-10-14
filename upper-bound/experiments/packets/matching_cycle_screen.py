#!/usr/bin/env python3
"""Finite spectral screen for rounded merge-and-deal matching cycles.

Each matching matrix averages the two packet coordinates on every edge.
The script samples cycles of perfect matchings and measures the largest
singular value of their product on the zero-sum subspace. This is numerical
exploration only: it neither certifies the floating-point norm nor gives an
unbounded explicit family.
"""

from __future__ import annotations

import argparse
import json

import numpy as np


def cycle_matrix(packet_count: int, rounds: int, seed: int) -> tuple[np.ndarray, list[list[list[int]]]]:
    rng = np.random.default_rng(seed)
    product = np.eye(packet_count)
    matching_data: list[list[list[int]]] = []
    for _ in range(rounds):
        permutation = rng.permutation(packet_count)
        matching = [
            [int(permutation[j]), int(permutation[j + 1])]
            for j in range(0, packet_count, 2)
        ]
        matching_data.append(matching)
        averaging = np.zeros((packet_count, packet_count), dtype=np.float64)
        for left, right in matching:
            averaging[left, left] = averaging[left, right] = 0.5
            averaging[right, left] = averaging[right, right] = 0.5
        product = averaging @ product
    return product, matching_data


def spectral_radius(product: np.ndarray) -> float:
    c = product.shape[0]
    centered = product - np.full_like(product, 1.0 / c)
    return float(np.linalg.svd(centered, compute_uv=False)[0])


def screen(packet_counts: list[int], round_counts: list[int], trials: int) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for rounds in round_counts:
        for c in packet_counts:
            values = []
            for trial in range(trials):
                seed = 25_000 + rounds * 1_000 + c * 10 + trial
                product, _ = cycle_matrix(c, rounds, seed)
                values.append(spectral_radius(product))
            fixed_seed = 25_000 + rounds * 1_000 + c
            product, _ = cycle_matrix(c, rounds, fixed_seed)
            rows.append({
                "rounds": rounds,
                "packet_count": c,
                "packet_sort_depth": 13,
                "trials": trials,
                "sampled_rho_min": min(values),
                "sampled_rho_median": float(np.median(values)),
                "sampled_rho_max": max(values),
                "fixed_seed": fixed_seed,
                "fixed_seed_rho": spectral_radius(product),
            })
    return {
        "status": "floating-point finite screen only; not a spectral certificate or unbounded family",
        "numpy": np.__version__,
        "results": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+", default=[16, 32, 64, 128, 256, 512, 1024])
    parser.add_argument("--rounds", type=int, nargs="+", default=[26, 30])
    parser.add_argument("--trials", type=int, default=10)
    parser.add_argument("--save", help="optional JSON output path")
    args = parser.parse_args()
    result = screen(args.packets, args.rounds, args.trials)
    if args.save:
        with open(args.save, "w", encoding="utf-8") as out:
            json.dump(result, out, indent=2)
            out.write("\n")
    for row in result["results"]:
        assert isinstance(row, dict)
        print(
            f"rounds={row['rounds']} packets={row['packet_count']} "
            f"rho_median={row['sampled_rho_median']:.7g} "
            f"rho_max={row['sampled_rho_max']:.7g} "
            f"fixed_seed_rho={row['fixed_seed_rho']:.7g}"
        )


if __name__ == "__main__":
    main()
