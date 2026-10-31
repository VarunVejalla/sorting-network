#!/usr/bin/env python3
"""Adversarial search for four cyclic rounds with the packed final repair.

The first three rounds are row-cyclic shifts followed by column sorts. In the
fourth round, rows at the top and bottom are sorted and packed with the exact
support-28 schedule; middle rows use the selected cyclic slope. This is a
heuristic search, not a uniform provider proof.
"""
import argparse
import json
import math
import numpy as np

from d2_cyclic_multiround_screen import inverse_cyclic
from d2_sparse_row_spread_gate import packing_offsets


class PackedCore:
    def __init__(self, heights, rows, slopes=(1, 5, 25), final_slope=61,
                 edge_rows=28):
        self.rows = rows
        self.cols = len(heights)
        self.edge = edge_rows
        self.slopes = tuple(slopes)
        self.final_slope = final_slope
        self.offsets = packing_offsets(edge_rows)
        if len(self.offsets) != edge_rows:
            raise ValueError("edge schedule length mismatch")
        inverse = [inverse_cyclic(rows, self.cols, a) for a in self.slopes]
        self.dest = [np.argsort(inv, axis=1) for inv in inverse]
        self.h = [np.asarray(heights, dtype=np.int32).copy()]
        for inv in inverse:
            active = self.h[-1][None, :] >= np.arange(1, rows + 1)[:, None]
            self.h.append(np.take_along_axis(active, inv, axis=1).sum(
                axis=0, dtype=np.int32))
        self.h.append(self._packed_round(self.h[-1]))
        self.sum_z = int(self.h[-1].sum())
        self.sum_z2 = int(self.h[-1] @ self.h[-1])

    def _packed_round(self, heights):
        after = np.zeros(self.cols, dtype=np.int32)
        for row in range(self.rows):
            width = int(np.count_nonzero(heights > row))
            if row < self.edge:
                start = self.offsets[row]
                for j in range(width):
                    after[(start + j) % self.cols] += 1
            elif row >= self.rows - self.edge:
                from_bottom = self.rows - 1 - row
                # The fixed reflection packs the sorted zero suffix at
                # `start`; the one prefix occupies its complementary cyclic
                # interval, which begins at start + 64 - width.
                start = (self.offsets[from_bottom] + self.cols - width) % self.cols
                for j in range(width):
                    after[(start + j) % self.cols] += 1
            else:
                shift = self.final_slope * row % self.cols
                for source in range(self.cols):
                    if heights[source] > row:
                        after[(source + shift) % self.cols] += 1
        return after

    def recompute(self, heights):
        profile = np.asarray(heights, dtype=np.int32).copy()
        for slope in self.slopes:
            inv = inverse_cyclic(self.rows, self.cols, slope)
            active = profile[None, :] >= np.arange(1, self.rows + 1)[:, None]
            profile = np.take_along_axis(active, inv, axis=1).sum(
                axis=0, dtype=np.int32)
        return self._packed_round(profile)

    def value(self):
        return 0.5 * (self.sum_z2 - self.sum_z * self.sum_z / self.cols)

    def change(self, column, direction):
        # Propagate the changed cell through the three ordinary cyclic rounds.
        for stage, destmap in enumerate(self.dest):
            old = int(self.h[stage][column])
            row = old if direction > 0 else old - 1
            dest = int(destmap[row, column])
            self.h[stage][column] += direction
            column = dest

        # In the packed layer, row sorting makes the changed cell the next
        # packed interval endpoint. Count the row before applying the change.
        source = column
        old = int(self.h[-2][source])
        row = old if direction > 0 else old - 1
        width = int(np.count_nonzero(self.h[-2] > row))
        if row < self.edge:
            start = self.offsets[row]
            dest = (start + (width if direction > 0 else width - 1)) % self.cols
        elif row >= self.rows - self.edge:
            from_bottom = self.rows - 1 - row
            start = self.offsets[from_bottom]
            # Increasing the number of ones shifts the complementary one
            # interval left by one; decreasing it removes its first wire.
            dest = (start + self.cols - width -
                    (1 if direction > 0 else 0)) % self.cols
        else:
            dest = (source + self.final_slope * row) % self.cols

        self.h[-2][source] += direction
        old_z = int(self.h[-1][dest])
        self.h[-1][dest] += direction
        self.sum_z += direction
        self.sum_z2 += 2 * direction * old_z + 1


def optimize(rows, cols, slopes, final_slope, edge_rows, rng, restarts, steps):
    best = (-1.0, None, None)
    for restart in range(restarts):
        if restart == 0:
            heights = np.linspace(rows, 0, cols, dtype=np.int32)
        elif restart == 1:
            heights = np.full(cols, rows // 2, dtype=np.int32)
        else:
            heights = rng.integers(0, rows + 1, size=cols, dtype=np.int32)
        state = PackedCore(heights, rows, slopes, final_slope, edge_rows)
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
            if candidate >= value or rng.random() < math.exp(
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int, default=2048)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--slopes", type=int, nargs="+", default=(1, 5, 25))
    parser.add_argument("--final-slope", type=int, default=61)
    parser.add_argument("--edge-rows", type=int, default=28)
    parser.add_argument("--seed", type=int, default=20261032)
    parser.add_argument("--restarts", type=int, default=24)
    parser.add_argument("--steps", type=int, default=20000)
    parser.add_argument("--show-profile", action="store_true")
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    value, heights, output = optimize(
        args.rows, args.columns, args.slopes, args.final_slope,
        args.edge_rows, rng, args.restarts, args.steps)
    report = {"rows": args.rows, "columns": args.columns,
              "slopes": args.slopes, "final_slope": args.final_slope,
              "edge_rows": args.edge_rows, "seed": args.seed,
              "restarts": args.restarts, "steps": args.steps,
              "Aw": value, "Aw_per_column": value / args.columns,
              "output_range": int(output.max() - output.min())}
    if args.show_profile:
        report["input_heights"] = heights.tolist()
        report["output_heights"] = output.tolist()
    print(json.dumps(report, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
