#!/usr/bin/env python3
"""Heuristic adversarial search for a fixed two-scramble binary core.

The core is two layers of independent per-row column permutations, each
followed by column sorting. This searches initial column heights x_j and
measures half the squared deviation of the final heights from their mean.
Any large value is a concrete counterexample for this seeded core; failure to
find one is not a uniform bound.
"""
from __future__ import annotations

import argparse
import numpy as np


def inverse_row_permutations(rng: np.random.Generator, rows: int,
                             cols: int) -> np.ndarray:
    # Each row maps source column to destination. Store destination-to-source
    # indices so a row's active bit vector can be gathered after the shuffle.
    order = np.argsort(rng.random((rows, cols)), axis=1)
    inv = np.empty_like(order)
    inv[np.arange(rows)[:, None], order] = np.arange(cols, dtype=order.dtype)
    return inv


def apply_round(heights: np.ndarray, inv: np.ndarray) -> np.ndarray:
    rows = inv.shape[0]
    thresholds = np.arange(1, rows + 1, dtype=np.int32)[:, None]
    active = heights[None, :] >= thresholds
    moved = np.take_along_axis(active, inv, axis=1)
    return moved.sum(axis=0, dtype=np.int32)


def score(x: np.ndarray, first: np.ndarray, second: np.ndarray) -> tuple[float, np.ndarray]:
    y = apply_round(x, first)
    z = apply_round(y, second)
    centered = z.astype(np.float64) - z.mean()
    return 0.5 * float(centered @ centered), z


class IncrementalCore:
    """Maintain both round outputs under a one-wire input-height change."""

    def __init__(self, x: np.ndarray, first: np.ndarray, second: np.ndarray):
        self.x = x.copy()
        self.first_dest = np.argsort(first, axis=1)
        self.second_dest = np.argsort(second, axis=1)
        self.y = apply_round(self.x, first)
        self.z = apply_round(self.y, second)
        self.sum_z = int(self.z.sum())
        self.sum_z2 = int(self.z @ self.z)
        self.rows, self.cols = first.shape

    def value(self) -> float:
        return 0.5 * (self.sum_z2 - self.sum_z * self.sum_z / self.cols)

    def change(self, j: int, direction: int) -> None:
        """Increment/decrement x[j], updating only the affected wires."""
        if direction > 0:
            row1 = int(self.x[j])
            d = int(self.first_dest[row1, j])
            row2 = int(self.y[d])
            self.y[d] += 1
            e = int(self.second_dest[row2, d])
            old_z = int(self.z[e])
            self.z[e] += 1
            self.sum_z += 1
            self.sum_z2 += 2 * old_z + 1
            self.x[j] += 1
        else:
            row1 = int(self.x[j]) - 1
            d = int(self.first_dest[row1, j])
            self.y[d] -= 1
            row2 = int(self.y[d])
            e = int(self.second_dest[row2, d])
            old_z = int(self.z[e])
            self.z[e] -= 1
            self.sum_z -= 1
            self.sum_z2 += -2 * old_z + 1
            self.x[j] -= 1


def optimize(first: np.ndarray, second: np.ndarray, rows: int, cols: int,
             rng: np.random.Generator, restarts: int, steps: int):
    best = (-1.0, None, None)
    for restart in range(restarts):
        if restart == 0:
            x = np.linspace(rows, 0, cols, dtype=np.int32)
        elif restart == 1:
            x = np.full(cols, rows // 2, dtype=np.int32)
        else:
            x = rng.integers(0, rows + 1, size=cols, dtype=np.int32)
        state = IncrementalCore(x, first, second)
        value = state.value()
        local = (value, state.x.copy(), state.z.copy())
        temperature = 8.0
        for it in range(steps):
            j = int(rng.integers(cols))
            direction = 1 if rng.random() < 0.5 else -1
            if (direction > 0 and state.x[j] == rows) or (direction < 0 and state.x[j] == 0):
                continue
            state.change(j, direction)
            candidate = state.value()
            if candidate >= value or rng.random() < np.exp((candidate - value) / temperature):
                value = candidate
                temperature = max(0.1, temperature * 0.999)
                if value > local[0]:
                    local = (value, state.x.copy(), state.z.copy())
            else:
                state.change(j, -direction)
        if local[0] > best[0]:
            best = local
        interval = max(1, restarts // 16)
        if (restart + 1) % interval == 0:
            print(f"restart={restart + 1}/{restarts} "
                  f"best_Aw={best[0]:.6f}", flush=True)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", type=int, default=8192)
    ap.add_argument("--cols", type=int, default=64)
    ap.add_argument("--core-seed", type=int, default=20261025)
    ap.add_argument("--search-seed", type=int, default=20261026)
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=10000)
    ap.add_argument("--cap-per-column", type=float, default=48.0)
    args = ap.parse_args()

    core_rng = np.random.default_rng(args.core_seed)
    search_rng = np.random.default_rng(args.search_seed)
    first = inverse_row_permutations(core_rng, args.rows, args.cols)
    second = inverse_row_permutations(core_rng, args.rows, args.cols)
    value, x, z = optimize(first, second, args.rows, args.cols,
                           search_rng, args.restarts, args.steps)
    print(f"core_seed={args.core_seed} search_seed={args.search_seed}")
    total_cap = args.cap_per_column * args.cols
    print(f"Aw={value:.9f} Aw_per_column={value / args.cols:.9f} "
          f"cap_per_column={args.cap_per_column:g} "
          f"exceeds_cap={value > total_cap}")
    print(f"input_heights={x.tolist()}")
    print(f"output_heights={z.tolist()}")


if __name__ == "__main__":
    main()
