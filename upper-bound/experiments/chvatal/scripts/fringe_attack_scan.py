#!/usr/bin/env python3
"""Attack-level Property F constant eps_F(u, f) for sort-scramble-sort separators.

Uses the exact capture attack from the sub300 worktree (d2_capture_attack.py):
j = u f n extreme keys, fringe of f rows; eps_F = best escape / j. Each value is an
exact run, so a lower bound on the true worst case for that scramble.

    python fringe_attack_scan.py --d2 <path to prefix-flux>
"""
import argparse
import sys
from multiprocessing import Pool

FS = [4, 8, 16, 32, 64]
US = [0.25, 0.5, 0.75, 1.0]


def job(task):
    path, f, u, seed, cols = task
    sys.path.insert(0, path)
    from d2_capture_attack import Stage, attack
    stage = Stage(cols, max(48, 3 * f), seed)
    i = u * f
    top = max(0, int(i) - 1)
    bases = {0, 1, 2, top // 3, top // 2, 2 * top // 3, 3 * top // 4, max(0, top - 1), top}
    best = max((attack(stage, b, i, f)[0] for b in sorted(bases) if b < i), default=0)
    return f, u, best / (i * cols)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d2', required=True)
    ap.add_argument('--columns', type=int, default=1000)
    ap.add_argument('--seeds', type=int, default=2)
    a = ap.parse_args()
    tasks = [(a.d2, f, u, s, a.columns) for f in FS for u in US for s in range(a.seeds)]
    res = {}
    with Pool() as pool:
        for f, u, e in pool.imap_unordered(job, tasks):
            res[(f, u)] = max(res.get((f, u), 0.0), e)
    print('eps_F (attack) by fringe rows f (rows) and u = j/(f n) (columns)')
    print('f    ' + ''.join(f'{u:>9}' for u in US))
    for f in FS:
        print(f'{f:<5}' + ''.join(f'{res[(f, u)]:9.4f}' for u in US))


if __name__ == '__main__':
    main()
