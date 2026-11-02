#!/usr/bin/env python3
"""Search for inputs with large bulk leak under sampled random scrambles.

Stage as in d2_capture_attack.py, at mass m/2. The leak is the wrong-side mass

    B_rows = sum_c max(final[c] - mean, 0) / n,

so `B = B_rows / m` is the quantity bounded by na_precision.py. Every reported value
comes from an exact run of the heights, so it is a lower bound on the worst case for
that scramble pair.

Two-level attack (default). Fix a final half T. Middle column v then has a walk
W2_v, and the final excess on T is exactly sum_v W2_v(middle_v). Put v in a middle
set S when its walk rises across a gap around m/2. Round 1 prices cells +1 into S
and -1 elsewhere, and every input column climbs its full walk, which moves S up and
the rest down by about 72 rows. T is then reset to the top half of the final, and
the steps repeat. `--anneal` then flips S members one at a time, scored by the
exact leak. `--local` runs the older single-window search, which is much weaker.

Mass may drift; the leak is measured against the actual mean, so this only moves
the threshold.

    python d2_bulk_attack.py --columns 1000 --rows 8192
    python d2_bulk_attack.py --columns 1000 --anneal 8000
"""
import argparse
import math

import numpy as np

from d2_sender_tail_gate import round_step


class Stage:
    def __init__(self, columns, rows, seed):
        rng = np.random.default_rng(seed)
        self.n, self.rows = columns, rows
        self.s1 = np.stack([rng.permutation(columns) for _ in range(rows)]).astype(np.int32)
        self.s2 = np.stack([rng.permutation(columns) for _ in range(rows)]).astype(np.int32)
        self.row_index = np.arange(rows)[:, None]

    def advance(self, heights, perm):
        filled = self.row_index < heights[None, :]
        return np.bincount(perm[filled], minlength=self.n)

    def run(self, h):
        middle = self.advance(h, self.s1)
        return middle, self.advance(middle, self.s2)


def leak(final):
    return float(np.maximum(final - final.mean(), 0).sum()) / len(final)


def majorant_slopes(gain, radius, centre):
    """Slopes of the least concave majorant of each column's walk near the centre."""
    rows, n = gain.shape
    lo = centre - radius
    slopes = np.empty((rows, n))
    slopes[:lo] = 0.5
    slopes[lo + 2 * radius:] = -0.5
    walk = np.vstack([np.zeros(n), np.cumsum(gain[lo:lo + 2 * radius], axis=0)])
    for c in range(n):
        y = walk[:, c]
        hull = [0]
        for x in range(1, len(y)):
            while len(hull) >= 2:
                x0, x1 = hull[-2], hull[-1]
                if (y[x1] - y[x0]) * (x - x0) <= (y[x] - y[x0]) * (x1 - x0):
                    hull.pop()
                else:
                    break
            hull.append(x)
        for x0, x1 in zip(hull, hull[1:]):
            slopes[lo + x0:lo + x1, c] = (y[x1] - y[x0]) / (x1 - x0)
    return slopes


def sweep(stage, h, middle, slopes, order, window):
    """Each input column re-picks its height for the exact middle state."""
    m = stage.rows
    moved = 0
    for u in order:
        cur = h[u]
        top = min(cur + window, m)
        c_add = stage.s1[cur:top, u]
        add = slopes[np.minimum(middle[c_add], m - 1), c_add]
        low = max(cur - window, 0)
        c_del = stage.s1[low:cur, u][::-1]
        rem = -slopes[np.maximum(middle[c_del] - 1, 0), c_del]
        gain_add = np.cumsum(add)
        gain_rem = np.cumsum(rem)
        best_add = int(np.argmax(gain_add)) if len(add) else -1
        best_rem = int(np.argmax(gain_rem)) if len(rem) else -1
        a = gain_add[best_add] if len(add) else 0
        r = gain_rem[best_rem] if len(rem) else 0
        if a > 1e-9 and a >= r:
            np.add.at(middle, c_add[:best_add + 1], 1)
            h[u] = cur + best_add + 1
            moved += 1
        elif r > 1e-9:
            np.add.at(middle, c_del[:best_rem + 1], -1)
            h[u] = cur - best_rem - 1
            moved += 1
    return moved


def attack(stage, sweeps, seed, window=256, spread=0, radius=64):
    """Ascent on keys in a fixed half S, valued by concave majorants."""
    rng = np.random.default_rng(seed + 1000)
    n, m = stage.n, stage.rows
    value = np.where(rng.permutation(n) < n // 2, 0.5, -0.5)
    slopes = majorant_slopes(value[stage.s2], radius, m // 2)
    h = np.full(n, m // 2, dtype=np.int64)
    if spread:
        h = rng.integers(m // 2 - spread, m // 2 + spread, n)
    middle = stage.advance(h, stage.s1)
    history = []
    for step in range(sweeps):
        moved = sweep(stage, h, middle, slopes, rng.permutation(n), window)
        history.append(leak(stage.run(h)[1]))
        if moved == 0:
            break
    check, final = stage.run(h)
    assert (check == middle).all()
    return max(history), history


def climb(stage, price):
    """Every input column takes the best height on its full walk of cell prices."""
    walk = np.vstack([np.zeros(stage.n), np.cumsum(price[stage.s1], axis=0)])
    return np.argmax(walk, axis=0)


def two_level(stage, seed, gap=128, alternations=4):
    rng = np.random.default_rng(seed + 7)
    n, m = stage.n, stage.rows
    i = m // 2
    member = rng.permutation(n) < n // 2
    best, best_up = 0.0, None
    for _ in range(alternations):
        target = np.where(member, 0.5, -0.5)
        walk2 = np.vstack([np.zeros(n), np.cumsum(target[stage.s2], axis=0)])
        inc = walk2[i + gap] - walk2[i - gap]
        up = inc > np.median(inc)
        middle, final = stage.run(climb(stage, np.where(up, 1.0, -1.0)))
        if leak(final) > best:
            best, best_up = leak(final), up.copy()
        member = final > np.median(final)
    return best, best_up


def anneal(stage, up, flips, seed, start_temp=0.05):
    rng = np.random.default_rng(seed + 11)
    score = leak(stage.run(climb(stage, np.where(up, 1.0, -1.0)))[1])
    best, best_up = score, up.copy()
    for k in range(flips):
        temp = start_temp * (1 - k / flips) + 1e-4
        c = rng.integers(stage.n)
        up[c] = ~up[c]
        trial = leak(stage.run(climb(stage, np.where(up, 1.0, -1.0)))[1])
        if trial >= score or rng.random() < np.exp((trial - score) / temp):
            score = trial
            if score > best:
                best, best_up = score, up.copy()
        else:
            up[c] = ~up[c]
    check = leak(stage.run(climb(stage, np.where(best_up, 1.0, -1.0)))[1])
    assert abs(check - best) < 1e-9
    return best


def first_moment_limit(rows):
    """Heuristic leak below which a union over inputs and column sets is vacuous.

    Inputs: heights uniform on a window, with entropy g per column. A fixed half of
    the columns is treated as independent with the mean-field final variance, so an
    excess of L rows per column costs L^2/sd^2 per column against g + ln 2.
    """
    print('half-window, entropy, final sd, limit in rows')
    for half in (128, 512, 1024, 2048, rows // 2):
        dist = np.zeros(rows + 1)
        dist[rows // 2 - half:rows // 2 + half + 1] = 1 / (2 * half + 1)
        g = math.log(2 * half + 1)
        dist = round_step(round_step(dist))
        heights = np.arange(rows + 1)
        mean = (dist * heights).sum()
        sd = math.sqrt((dist * (heights - mean) ** 2).sum())
        print(half, round(g, 2), round(sd, 2), round(sd * math.sqrt(g + math.log(2)), 2))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--columns', type=int, default=1000)
    ap.add_argument('--rows', type=int, default=8192)
    ap.add_argument('--seeds', type=int, nargs='+', default=[0])
    ap.add_argument('--sweeps', type=int, default=30)
    ap.add_argument('--window', type=int, default=256)
    ap.add_argument('--spread', type=int, default=0)
    ap.add_argument('--radius', type=int, default=64)
    ap.add_argument('--limit', action='store_true', help='print the first-moment limit')
    ap.add_argument('--local', action='store_true', help='older single-window search')
    ap.add_argument('--anneal', type=int, default=0, help='flips after the two-level start')
    args = ap.parse_args()
    if args.limit:
        first_moment_limit(args.rows)
        return
    for seed in args.seeds:
        stage = Stage(args.columns, args.rows, seed)
        flat = np.random.default_rng(seed).integers(0, args.rows, args.columns)
        if not args.local:
            value, up = two_level(stage, seed)
            line = f'two-level leak {value:.2f} rows'
            if args.anneal:
                line += f', annealed {anneal(stage, up, args.anneal, seed):.2f} rows'
            print(f'n={args.columns} m={args.rows} seed {seed}: {line}; random input '
                  f'{leak(stage.run(flat)[1]):.2f} rows', flush=True)
            continue
        value, history = attack(stage, args.sweeps, seed, args.window, args.spread,
                                args.radius)
        typical = leak(stage.run(flat)[1])
        print(f'n={args.columns} m={args.rows} seed {seed}: attack leak {value:.2f} rows '
              f'(B={value / args.rows:.5f}), random input {typical:.2f} rows, by sweep '
              f'{[round(x, 2) for x in history[:12]]}', flush=True)


if __name__ == '__main__':
    main()
