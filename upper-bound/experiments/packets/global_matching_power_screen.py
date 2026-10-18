#!/usr/bin/env python3
"""Scalable floating-point screen for global matching cycles.

Uses sparse pair updates and power iteration instead of constructing the dense
cycle matrix. It estimates the centered operator norm and separately tracks a
centered indicator on 1/64 of packet IDs (a toy subtree mode). Exploratory
only: schedules are sampled independently at each size and no norm is
certified.
"""

from __future__ import annotations

import argparse
import json

import numpy as np


def matching_cycle(n: int, rounds: int, seed: int):
    rng = np.random.default_rng(seed)
    result = []
    for _ in range(rounds):
        order = rng.permutation(n)
        result.append((order[::2], order[1::2]))
    return result


def apply(vector: np.ndarray, matchings, reverse: bool = False) -> np.ndarray:
    result = vector.copy()
    sequence = reversed(matchings) if reverse else matchings
    for left, right in sequence:
        mean = (result[left] + result[right]) * 0.5
        result[left] = mean
        result[right] = mean
    return result


def centered_unit(vector: np.ndarray) -> np.ndarray:
    result = vector - vector.mean()
    return result / np.linalg.norm(result)


def estimate_norm(n: int, matchings, seed: int, iterations: int) -> float:
    rng = np.random.default_rng(seed)
    x = centered_unit(rng.standard_normal(n))
    for _ in range(iterations):
        y = apply(apply(x, matchings), matchings, reverse=True)
        x = centered_unit(y)
    tx = apply(apply(x, matchings), matchings, reverse=True)
    return float(np.sqrt(max(0.0, np.dot(x, tx))))


def subtree_ratio(n: int, matchings, subtree_packets: int) -> float:
    initial = np.zeros(n, dtype=np.float64)
    initial[:subtree_packets] = 1.0
    initial = centered_unit(initial)
    output = apply(initial, matchings)
    output -= output.mean()
    return float(np.linalg.norm(output))


def rank_target_drift(n: int, matchings) -> float:
    """Average W1 displacement of packet labels under the matching product.

    For singleton-key packets in rank order, this equals aggregate L1 error
    over all key cuts, normalized by n*(n-1). A matching averaging matrix is
    also the transition matrix of a walk that stays or crosses its matched
    edge with probability 1/2. The row distributions of the column product
    use the matchings in reverse order.
    """
    partner_maps = []
    for left, right in matchings:
        partner = np.arange(n, dtype=np.int32)
        partner[left] = right
        partner[right] = left
        partner_maps.append(partner)

    positions = np.arange(n, dtype=np.int32)[:, None]
    weights = np.ones((n, 1), dtype=np.float32)
    for partner in reversed(partner_maps):
        # Each path either stays at its current label or crosses the matched
        # edge. Probabilities are dyadic and exact in float32 for these rounds.
        positions = np.concatenate((positions, partner[positions]), axis=1)
        weights = np.repeat(weights * np.float32(0.5), 2, axis=1)

    starts = np.arange(n, dtype=np.int32)[:, None]
    row_displacements = (np.abs(positions - starts) * weights).sum(axis=1)
    return float(row_displacements.sum() / (n * (n - 1)))


def direct_rank_target_drift(n: int, matchings) -> float:
    """Dense reference calculation, used only to check small instances."""
    product = np.eye(n, dtype=np.float64)
    for left, right in matchings:
        mean = (product[left] + product[right]) * 0.5
        product[left] = mean
        product[right] = mean
    steps = np.arange(n)[:, None] > np.arange(n - 1)[None, :]
    return float(np.abs(steps - product @ steps).sum() / (n * (n - 1)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packets", type=int, nargs="+", default=[256, 1024, 4096, 16384, 65536])
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--iterations", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20261018)
    parser.add_argument(
        "--subtree-fraction", type=float, default=1 / 64,
        help="fraction of packet IDs in the indicator mode",
    )
    args = parser.parse_args()
    rows = []
    for n in args.packets:
        if n % 2:
            raise ValueError("packet counts must be even")
        subtree_packets = max(1, min(n, int(n * args.subtree_fraction)))
        matchings = matching_cycle(n, args.rounds, args.seed + n)
        drift = rank_target_drift(n, matchings)
        if n <= 256:
            assert abs(drift - direct_rank_target_drift(n, matchings)) < 1e-6
        rows.append({
            "packets": n,
            "rounds": args.rounds,
            "estimated_centered_operator_norm": estimate_norm(
                n, matchings, args.seed + 2 * n, args.iterations
            ),
            "rank_target_drift_before_reassembly": drift,
            "subtree_packets": subtree_packets,
            "centered_subtree_indicator_ratio": subtree_ratio(
                n, matchings, subtree_packets
            ),
        })
    print(json.dumps({
        "status": "floating-point sampled screen only; not a uniform family or certificate",
        "iterations": args.iterations,
        "seed": args.seed,
        "results": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
