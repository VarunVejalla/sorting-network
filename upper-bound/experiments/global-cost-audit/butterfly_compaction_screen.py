"""Exact iid-state analysis of a within-row butterfly compactor.

Each position starts in one of three states: high-only, hole-only, or clean.
Each butterfly layer compares paired positions within both boundary rows,
directing high defects toward low wire indices and holes toward low indices.
The final cross-row comparator repairs positions where both flags coincide.

This computes exact one-wire state distributions. Pair independence at each
butterfly step follows because the current dimension pairs disjoint input
cones. It is a local iid model, not the scheduler's full repair theorem.
"""

from __future__ import annotations

import argparse
import itertools

import numpy as np


# State code: 2*high_flag + hole_flag. Initial states are clean, hole-only,
# high-only, and both; the last state has probability zero initially.
HIGH_ONLY = 2
HOLE_ONLY = 1
BOTH = 3


def combine_pair(p: np.ndarray, q: np.ndarray):
    """Distributions after sending coordinatewise OR low and AND high."""
    low = np.zeros_like(p)
    high = np.zeros_like(p)
    for a in range(4):
        ah, al = (a >> 1) & 1, a & 1
        for b in range(4):
            bh, bl = (b >> 1) & 1, b & 1
            mass = p[..., a] * q[..., b]
            low[..., ((ah | bh) << 1) | (al | bl)] += mass
            high[..., ((ah & bh) << 1) | (al & bl)] += mass
    return low, high


def exact_residual(log2_block: int) -> tuple[float, float, float]:
    wires = 1 << log2_block
    dist = np.zeros((wires, 4), dtype=np.float64)
    dist[:, 0] = 0.5  # clean
    dist[:, HOLE_ONLY] = 0.25
    dist[:, HIGH_ONLY] = 0.25

    for dimension in range(log2_block):
        stride = 1 << dimension
        grouped = dist.reshape(wires // (2 * stride), 2, stride, 4)
        low, high = combine_pair(grouped[:, 0, :, :], grouped[:, 1, :, :])
        grouped[:, 0, :, :] = low
        grouped[:, 1, :, :] = high

    # The last cross-row layer removes the both-defect state. High-only is
    # precisely the residual upper error after that layer.
    return (
        float(dist[:, HIGH_ONLY].mean()),
        float(dist[:, BOTH].mean()),
        float(dist[:, HOLE_ONLY].mean()),
    )


def scheduled_residual(log2_block: int, cross_after: set[int]) -> float:
    """High leakage when cross-row cancellation is inserted between C layers.

    `cross_after` contains gaps 0..r: gap t is after t butterfly dimensions.
    A cross layer deletes state BOTH; the following unused butterfly
    dimensions still pair independent input cones, so this marginal recurrence
    remains exact for the iid model.
    """
    r = log2_block
    wires = 1 << r
    dist = np.zeros((wires, 4), dtype=np.float64)
    dist[:, 0], dist[:, HOLE_ONLY], dist[:, HIGH_ONLY] = 0.5, 0.25, 0.25

    def cross(p: np.ndarray) -> np.ndarray:
        q = p.copy()
        q[:, 0] += q[:, BOTH]
        q[:, BOTH] = 0.0
        return q

    if 0 in cross_after:
        dist = cross(dist)
    for t in range(r):
        stride = 1 << t
        grouped = dist.reshape(wires // (2 * stride), 2, stride, 4)
        low, high = combine_pair(grouped[:, 0, :, :], grouped[:, 1, :, :])
        grouped[:, 0, :, :] = low
        grouped[:, 1, :, :] = high
        if t + 1 in cross_after:
            dist = cross(dist)
    return float(dist[:, HIGH_ONLY].mean())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log2-block", type=int, nargs="+", default=[8, 12, 16, 17])
    parser.add_argument("--search-17", action="store_true", help="exhaust all distinct cross-layer gap placements")
    args = parser.parse_args()
    for r in args.log2_block:
        residual, repaired, hole_residual = exact_residual(r)
        print(
            f"block=2^{r}={1 << r}; compaction_layers={r}; total_with_cross={r + 1}; "
            f"high_residual={residual:.10f}; both_repaired={repaired:.10f}; "
            f"hole_residual={hole_residual:.10f}"
        )
    print("\nSelected 17-layer schedules (C = one butterfly dimension, X = cross-row cancellation):")
    for r in range(8, min(12, max(args.log2_block)) + 1):
        x = 17 - r
        gaps = r + 1
        candidates = {
            "X then C block": set(range(min(x, gaps))),
            "evenly spaced X": {round(i * r / max(1, x - 1)) for i in range(x)},
            "C block then X": {r},
        }
        vals = {name: scheduled_residual(r, pos) for name, pos in candidates.items()}
        print(f"2^{r}: " + "; ".join(f"{name}={value:.8f}" for name, value in vals.items()))
    if args.search_17:
        print("\nExhaustive best schedule for each block size:")
        for r in range(8, 17):
            x = 17 - r
            best = min(
                (scheduled_residual(r, set(gaps)), gaps)
                for gaps in itertools.combinations(range(r + 1), x)
            )
            print(f"2^{r}: leakage={best[0]:.10f}; cross_gaps={best[1]}")


if __name__ == "__main__":
    main()
