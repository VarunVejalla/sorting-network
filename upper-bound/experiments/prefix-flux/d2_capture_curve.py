#!/usr/bin/env python3
"""Attack curve E(i, f) in rows, as JSON, for d2_exact_closure.py --attack.

Best exact escape over seeds and flat bases (d2_capture_attack.py), per mass and
fringe, plus the steady closing bulk

    B* = max_i (i - 16 E(i, f)) / feed,   feed = 0.507,

which is the fixed point of i = feed*B + 16 E(i, f).

    python d2_capture_curve.py --out curve.json
"""
import argparse
import json
from multiprocessing import Pool

from d2_capture_attack import Stage, attack

COLUMNS = 1000
FEED = 0.507


def job(task):
    i, f, seed = task
    stage = Stage(COLUMNS, 48, seed)
    top = max(0, int(i) - 1)
    bases = {0, 1, 2, 3, top // 3, top // 2, 2 * top // 3, 3 * top // 4,
             max(0, top - 3), max(0, top - 2), max(0, top - 1), top}
    best = max((attack(stage, b, i, f)[0] for b in sorted(bases) if b < i), default=0)
    return i, f, best


def closing_bulk(points):
    best = (float('-inf'), 0.0, 0.0)
    for (a, ea), (b, eb) in zip(points, points[1:]):
        for k in range(101):
            i, e = a + (b - a) * k / 100, ea + (eb - ea) * k / 100
            best = max(best, (i - 16 * e, i, e))
    return best[0] / FEED, best[1], best[2]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True)
    ap.add_argument('--masses', type=float, nargs='+',
                    default=[1, 2, 3, 4, 5, 6, 7, 8, 8.85, 10, 11, 12, 13, 14, 15, 16])
    ap.add_argument('--fringes', type=int, nargs='+', default=[13, 14, 15, 16])
    ap.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    ap.add_argument('--workers', type=int, default=14)
    args = ap.parse_args()
    tasks = [(i, f, s) for i in args.masses for f in args.fringes for s in args.seeds]
    table = {}
    with Pool(args.workers) as pool:
        for i, f, best in pool.imap_unordered(job, tasks):
            row = table.setdefault(str(f), {})
            row[str(i)] = max(row.get(str(i), 0.0), best / COLUMNS)
    with open(args.out, 'w') as handle:
        json.dump(table, handle, indent=0)
    for f in sorted(table, key=int):
        points = sorted((float(i), v) for i, v in table[f].items())
        bulk, i, e = closing_bulk(points)
        print(f'f={f}: closing bulk {bulk:.2f} rows, at mass {i:.2f}, E {e:.3f}')


if __name__ == '__main__':
    main()
