#!/usr/bin/env python3
"""Search for inputs that break fringe capture under sampled random scrambles.

Stage: column sort, row permutations S1, column sort, row permutations S2, column
sort. A Boolean input with sorted columns is a height vector h. A cell (r,c) is
filled when r < h[c], and it lands in column S[r,c].

Every result is measured by exact simulation of the heights, so a reported escape
is a real lower bound for that scramble pair. The search is greedy from a flat base
of height b: price each missing cell backward through both rounds, then build the
cheapest target column. It then frees keys that do not reach an escaping column
and rebuilds.

    python d2_capture_attack.py --columns 4000 --mass 8.85 --fringe 13
"""
import argparse

import numpy as np


class Stage:
    def __init__(self, columns, rows, seed):
        rng = np.random.default_rng(seed)
        self.n, self.rows = columns, rows
        self.s1 = np.stack([rng.permutation(columns) for _ in range(rows)])
        self.s2 = np.stack([rng.permutation(columns) for _ in range(rows)])
        self.inv1 = np.argsort(self.s1, axis=1)
        self.inv2 = np.argsort(self.s2, axis=1)
        self.row_index = np.arange(rows)[:, None]

    def advance(self, heights, perm):
        filled = self.row_index < heights[None, :]
        return np.bincount(perm[filled], minlength=self.n)

    def run(self, h):
        middle = self.advance(h, self.s1)
        return middle, self.advance(middle, self.s2)


def cheapest_build(stage, h, middle, final, fringe):
    """Return the target column and its input additions, cheapest per excess."""
    rows, n = stage.rows, stage.n
    # Round 1: keys needed to fill cell (q,s) of the middle layer.
    source1 = stage.inv1
    need1 = np.maximum(stage.row_index + 1 - h[source1], 0)
    filled1 = need1 == 0
    order1 = np.argsort(np.where(filled1, 10 ** 9, need1), axis=0)
    sorted1 = np.take_along_axis(need1, order1, axis=0)
    sorted1 = np.where(np.take_along_axis(filled1, order1, axis=0), 10 ** 9,
                       sorted1)
    prefix1 = np.vstack([np.zeros(n, dtype=np.int64),
                         np.cumsum(np.minimum(sorted1, 10 ** 6), axis=0)])
    # Round 2: keys needed to fill cell (r,t) of the final layer.
    source2 = stage.inv2
    gap = np.maximum(stage.row_index + 1 - middle[source2], 0)
    cost2 = prefix1[np.minimum(gap, rows), source2]
    filled2 = gap == 0
    cost2 = np.where(filled2, 10 ** 9, cost2)
    cost_sorted = np.sort(cost2, axis=0)
    wanted = np.maximum(fringe + 1 - final, 1)
    cumulative = np.cumsum(np.minimum(cost_sorted, 10 ** 7), axis=0)
    total = cumulative[np.minimum(wanted - 1, rows - 1), np.arange(n)]
    target = int(np.argmin(total))
    return target, int(total[target]), int(wanted[target]), order1, sorted1, cost2


def apply_build(stage, h, middle, target, wanted, order1, sorted1, cost2):
    """Raise the input so the target gains its cheapest missing final cells."""
    new = h.copy()
    picks = np.argsort(cost2[:, target])[:wanted]
    for r in picks:
        s = stage.inv2[r, target]
        for k in range(max(0, r + 1 - middle[s])):
            q = order1[k, s]
            u = stage.inv1[q, s]
            new[u] = max(new[u], q + 1)
    return new


def prune(stage, h, fringe):
    """Remove input keys whose exact path ends in a column at or below the fringe."""
    h = h.copy()
    columns = np.arange(stage.n)
    while True:
        middle, final = stage.run(h)
        live = columns[h > 0]
        v = stage.s1[h[live] - 1, live]
        w = stage.s2[middle[v] - 1, v]
        free = final[w] <= fringe
        live, v, w = live[free], v[free], w[free]
        if len(live) == 0:
            return h
        _, first_v = np.unique(v, return_index=True)
        live, w = live[first_v], w[first_v]
        _, first_w = np.unique(w, return_index=True)
        h[live[first_w]] -= 1


def grow(stage, h, budget, fringe):
    best, best_h = 0, h
    while True:
        middle, final = stage.run(h)
        value = int(np.maximum(final - fringe, 0).sum())
        if value >= best:
            best, best_h = value, h
        target, cost, wanted, order1, sorted1, cost2 = cheapest_build(
            stage, h, middle, final, fringe)
        if h.sum() + cost > budget or cost >= 10 ** 6:
            return best, best_h
        new = apply_build(stage, h, middle, target, wanted, order1, sorted1,
                          cost2)
        if (new == h).all():
            return best, best_h
        h = new


def attack(stage, base, mass_rows, fringe, passes=6):
    budget = int(mass_rows * stage.n)
    best, h = grow(stage, np.full(stage.n, base, dtype=np.int64), budget, fringe)
    for _ in range(passes):
        value, candidate = grow(stage, prune(stage, h, fringe), budget, fringe)
        if value <= best:
            break
        best, h = value, candidate
    assert h.sum() <= budget
    final = stage.run(h)[1]
    assert int(np.maximum(final - fringe, 0).sum()) == best
    return best, int(h.sum())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--columns', type=int, default=4000)
    ap.add_argument('--mass', type=float, default=8.85)
    ap.add_argument('--fringe', type=int, default=13)
    ap.add_argument('--bases', type=int, nargs='+', default=[4, 5, 6, 7, 8])
    ap.add_argument('--seeds', type=int, nargs='+', default=[0])
    ap.add_argument('--rows', type=int, default=40)
    args = ap.parse_args()
    need = args.mass * args.columns / 128
    print(f'n={args.columns} mass={args.mass} f={args.fringe}: '
          f'gate breaks above {need:.0f} escapes (E/a > 1/128)', flush=True)
    for seed in args.seeds:
        stage = Stage(args.columns, args.rows, seed)
        for base in args.bases:
            escapes, used = attack(stage, base, args.mass, args.fringe)
            print(f'seed {seed} base {base}: escapes {escapes}, '
                  f'E/a {escapes / (args.mass * args.columns):.5f}, '
                  f'used {used / args.columns:.2f} rows', flush=True)


if __name__ == '__main__':
    main()
