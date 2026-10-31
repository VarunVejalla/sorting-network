#!/usr/bin/env python3
"""Search fixed cyclic shuffle/sort rounds for the 4096x64 D2 core.

The input is a 64-column height vector after the initial column sort. Each
round applies row-dependent cyclic column wiring and sorts the columns again.
The incremental adversary updates one affected wire per round exactly.
"""
import argparse
from contextlib import redirect_stdout
from io import StringIO
from math import gcd

import numpy as np


def inverse_cyclic(rows, cols, slope, offset=0):
    destination = np.arange(cols, dtype=np.int32)
    shifts = (slope * np.arange(rows, dtype=np.int32) + offset) % cols
    return (destination[None, :] - shifts[:, None]) % cols


class MultiRound:
    def __init__(self, heights, inverse_rounds):
        self.h = [heights.copy()]
        self.dest = [np.argsort(inv, axis=1) for inv in inverse_rounds]
        for inv in inverse_rounds:
            rows = inv.shape[0]
            active = self.h[-1][None, :] >= np.arange(1, rows + 1)[:, None]
            self.h.append(np.take_along_axis(active, inv, axis=1).sum(
                axis=0, dtype=np.int32))
        self.rows = inverse_rounds[0].shape[0]
        self.cols = len(heights)
        self.sum_z = int(self.h[-1].sum())
        self.sum_z2 = int(self.h[-1] @ self.h[-1])

    def value(self):
        return 0.5 * (self.sum_z2 - self.sum_z * self.sum_z / self.cols)

    def change(self, column, direction):
        for stage, destmap in enumerate(self.dest):
            old = int(self.h[stage][column])
            row = old if direction > 0 else old - 1
            destination = int(destmap[row, column])
            self.h[stage][column] += direction
            if stage + 1 == len(self.dest):
                old_z = int(self.h[stage + 1][destination])
                self.h[stage + 1][destination] += direction
                self.sum_z += direction
                self.sum_z2 += 2 * direction * old_z + 1
            else:
                column = destination


def optimize(inverse_rounds, rng, restarts, steps):
    rows, cols = inverse_rounds[0].shape
    best = (-1.0, None, None)
    for restart in range(restarts):
        if restart == 0:
            x = np.linspace(rows, 0, cols, dtype=np.int32)
        elif restart == 1:
            x = np.full(cols, rows // 2, dtype=np.int32)
        else:
            x = rng.integers(0, rows + 1, size=cols, dtype=np.int32)
        state = MultiRound(x, inverse_rounds)
        value = state.value()
        local = (value, state.h[0].copy(), state.h[-1].copy())
        temperature = 8.0
        for _ in range(steps):
            j = int(rng.integers(cols))
            direction = 1 if rng.random() < 0.5 else -1
            if (direction > 0 and state.h[0][j] == rows) or (
                    direction < 0 and state.h[0][j] == 0):
                continue
            state.change(j, direction)
            candidate = state.value()
            if candidate >= value or rng.random() < np.exp(
                    (candidate - value) / temperature):
                value = candidate
                temperature = max(0.1, temperature * 0.999)
                if value > local[0]:
                    local = (value, state.h[0].copy(), state.h[-1].copy())
            else:
                state.change(j, -direction)
        if local[0] > best[0]:
            best = local
    return best


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rows", type=int, default=512)
    ap.add_argument("--columns", type=int, default=64)
    ap.add_argument("--slopes", type=int, nargs="+", default=(1, 35, 17))
    ap.add_argument("--search-seed", type=int, default=20261026)
    ap.add_argument("--restarts", type=int, default=64)
    ap.add_argument("--steps", type=int, default=20000)
    ap.add_argument("--show-witness", action="store_true")
    args = ap.parse_args()
    if args.rows % args.columns:
        ap.error("rows must be a multiple of columns")
    if any(gcd(slope, args.columns) != 1 for slope in args.slopes):
        ap.error("all slopes must be coprime to the column count")
    rounds = [inverse_cyclic(args.rows, args.columns, slope)
              for slope in args.slopes]
    rng = np.random.default_rng(args.search_seed)
    with redirect_stdout(StringIO()):
        value, heights, output = optimize(rounds, rng,
                                          args.restarts, args.steps)
    result = {"rows": args.rows, "columns": args.columns,
              "slopes": args.slopes, "search_seed": args.search_seed,
              "restarts": args.restarts, "steps": args.steps,
              "rounds": len(rounds), "Aw": value,
              "Aw_per_column": value / args.columns,
              "output_range": int(output.max() - output.min())}
    if args.show_witness:
        result["input_heights"] = heights.tolist()
        result["output_heights"] = output.tolist()
    print(result, flush=True)


if __name__ == "__main__":
    main()
