#!/usr/bin/env python3
"""Adversarial screen for the actual low-fringe packed row transition.

Profiles h are arbitrary 64-column height vectors in [0,103] satisfying the
one-sided slope-35 gradient. Edge rows are horizontally sorted and packed;
middle rows preserve the actual active-column set under slope49. This is a
heuristic search over the invariant class, not a proof or fixed-core trace.
"""
import argparse
import json
import math

import numpy as np

N = 64
EDGE = 40
CAP = 103
OFFSETS = (0, 27, 42, 52, 58, 23, 38, 49, 20, 62, 18, 36, 16, 47,
           14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
           28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39)


class Profile:
    def __init__(self, heights):
        self.h = np.asarray(heights, dtype=np.int32).copy()
        self.out = np.zeros(N, dtype=np.int32)
        for r in range(EDGE):
            width = int(np.count_nonzero(self.h > r))
            for k in range(width):
                self.out[(OFFSETS[r] + k) % N] += 1
        for c, height in enumerate(self.h):
            for r in range(EDGE, int(height)):
                self.out[(35 * c + 49 * r) % N] += 1
        self.mass = int(self.h.sum())
        self.squares = int(self.out @ self.out)

    def area(self):
        return 0.5 * (self.squares - self.mass * self.mass / N)

    def valid_change(self, c, delta):
        value = int(self.h[c]) + delta
        if value < 0 or value > CAP:
            return False
        prev, nxt = (c - 1) % N, (c + 1) % N
        return (value <= int(self.h[prev]) + 1 and
                int(self.h[nxt]) <= value + 1)

    def change(self, c, delta):
        old = int(self.h[c])
        row = old if delta > 0 else old - 1
        if row < EDGE:
            width = int(np.count_nonzero(self.h > row))
            dest = (OFFSETS[row] + (width if delta > 0 else width - 1)) % N
        else:
            dest = (35 * c + 49 * row) % N
        old_out = int(self.out[dest])
        self.out[dest] += delta
        self.squares += 2 * delta * old_out + 1
        self.mass += delta
        self.h[c] += delta


def initial_profiles():
    yield np.full(N, 50, dtype=np.int32)
    for shift in range(N):
        yield np.asarray([(i + shift) % N for i in range(N)], dtype=np.int32)
    for peak in (16, 32, 48, 64, 80, 96, 103):
        for shift in range(N):
            yield np.asarray([min(peak, (i + shift) % N)
                              for i in range(N)], dtype=np.int32)


def search(seed, restarts, steps):
    rng = np.random.default_rng(seed)
    best = (-1.0, None, None)
    starts = list(initial_profiles())
    for restart in range(restarts):
        if restart < len(starts):
            heights = starts[restart]
        elif restart % 2:
            heights = np.full(N, int(rng.integers(0, CAP + 1)),
                              dtype=np.int32)
        else:
            state = Profile(np.full(N, 50, dtype=np.int32))
            # Build a random valid state by accepted local moves.
            for _ in range(5000):
                c = int(rng.integers(N))
                d = 1 if rng.random() < 0.5 else -1
                if state.valid_change(c, d):
                    state.change(c, d)
            heights = state.h.copy()
        state = Profile(heights)
        value = state.area()
        local = (value, state.h.copy(), state.out.copy())
        temperature = 4.0
        for _ in range(steps):
            c = int(rng.integers(N))
            delta = 1 if rng.random() < 0.5 else -1
            if not state.valid_change(c, delta):
                continue
            state.change(c, delta)
            candidate = state.area()
            if candidate >= value or rng.random() < math.exp(
                    (candidate - value) / temperature):
                value = candidate
                temperature = max(0.1, temperature * 0.9995)
                if value > local[0]:
                    local = (value, state.h.copy(), state.out.copy())
            else:
                state.change(c, -delta)
        if local[0] > best[0]:
            best = local
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261027)
    parser.add_argument("--restarts", type=int, default=64)
    parser.add_argument("--steps", type=int, default=100000)
    args = parser.parse_args()
    area, heights, output = search(args.seed, args.restarts, args.steps)
    report = {"seed": args.seed, "restarts": args.restarts,
              "steps": args.steps, "Aw": area,
              "output_range": int(output.max() - output.min()),
              "gradient_valid": all(int(heights[c]) <=
                                    int(heights[(c - 1) % N]) + 1
                                    for c in range(N)),
              "heights": heights.tolist(), "output": output.tolist()}
    print(json.dumps(report, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
