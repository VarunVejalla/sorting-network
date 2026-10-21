#!/usr/bin/env python3
"""Count-interval transfer under the local rank-tail contract.

This is a conservative finite diagnostic, not a proof of the uniform local
contract or of the D2 geometry. Unlike sparse_probe.py, it never assumes that
an output port is internally sorted: it bounds each port's zero count from the
two prefix bounds at its endpoints.
"""
from fractions import Fraction as F
from math import ceil
import argparse

from flow_dag import FlowDAG
from oracle import Par
from sparse_probe import profile_tail


def cap_tail(total, f, n, m):
    if total <= 0 or f >= m:
        return 0
    i = min(m, (total + n - 1) // n)
    return profile_tail(i * n, f, n, m)


def prefix_interval(a, H, pcut, row_count=1 << 12):
    """Bounds Y(pcut) uniformly for H in interval H=(lo,hi]."""
    lo, hi = H
    if a == 0:
        return (0, 0)
    m = row_count
    assert a % m == 0, (a, m)
    n = a // m
    if n == 1:
        # One column is sorted exactly by the first column sort.
        return (min(lo, pcut), min(hi, pcut))
    k, r = divmod(pcut, n)
    if k >= m:
        return H
    if lo == hi == 0:
        return (0, 0)
    # The local theorem is a one-sided prefix lower bound. A complementary
    # tail does not give an upper bound on zeros in this same prefix. For an
    # interval of possible total masses, round the high endpoint to its mass
    # class and use the low endpoint in the deterministic min(H,p) term.
    mark_tail = cap_tail(hi, k, n, m)
    hole_tail = cap_tail(a - lo, m - k, n, m) + r
    error = min(mark_tail, hole_tail) + r
    ylo = max(0, min(lo, pcut) - error)
    return (ylo, min(hi, pcut))


def port_interval(a, H, lo, hi, row_count=1 << 12):
    if lo == hi:
        return (0, 0)
    yl0, yh0 = prefix_interval(a, H, lo, row_count)
    yl1, yh1 = prefix_interval(a, H, hi, row_count)
    low = max(0, yl1 - yh0)
    high = min(hi - lo, yh1 - yl0)
    if high < low:
        return (0, hi - lo)
    return (low, max(0, high))


def sum_iv(xs):
    return (sum(x[0] for x in xs), sum(x[1] for x in xs))


def run(depth=4, scale=65536, threshold=F(1, 3), include_history=False,
        params=(2, 3, 2), row_count=1 << 12):
    p = Par(*params)
    flow = FlowDAG(depth, scale=scale, p=p).build()
    N = p.k ** depth * scale
    q = int(threshold * N)
    H = {(0, 0): (q, q)}
    history = [H.copy()]
    log = []
    for t in range(len(flow.rows)):
        ups, downs = {}, {}
        active = []
        if t == 0:
            active = [(0, 0)]
        else:
            active = [(lev, idx) for lev in range(depth + 1)
                      if p.active(depth, lev, t)
                      for idx in range(p.k ** lev)]
        for lev, idx in active:
            node = flow.lookup(t, lev, idx)
            a, pi, blocks = flow.rows[t][node]
            mass = H.get((lev, idx), (0, 0))
            if pi == a:
                ups[(lev, idx)] = mass
                continue
            h = pi // 2
            left = port_interval(a, mass, 0, h, row_count)
            right = port_interval(a, mass, a - h, a, row_count)
            ups[(lev, idx)] = (left[0] + right[0], left[1] + right[1])
            pos = h
            for j, width in enumerate(blocks):
                downs[(lev, idx, j)] = port_interval(
                    a, mass, pos, pos + width, row_count
                )
                pos += width

        active_set = set(active)
        Hnext = {}
        for lev in range(depth + 1):
            for idx in range(p.k ** lev):
                key = (lev, idx)
                is_active = key in active_set
                pieces = []
                if not is_active:
                    pieces.append(H.get(key, (0, 0)))
                if lev > 0:
                    parent = (lev - 1, idx // p.k)
                    port = idx % p.k
                    if (lev - 1, idx // p.k, port) in downs:
                        pieces.append(downs[(lev - 1, idx // p.k, port)])
                if lev < depth:
                    for j in range(p.k):
                        child = (lev + 1, idx * p.k + j)
                        if child in ups:
                            pieces.append(ups[child])
                lo, hi = sum_iv(pieces)
                target = flow.allocation(flow.lookup(t + 1, lev, idx))
                Hnext[key] = (min(target, lo), min(target, hi))
        H = Hnext
        history.append(H.copy())
        log.append((t, max((b - a for a, b in H.values()), default=0)))

    bad = []
    for lev in range(depth + 1):
        for idx in range(p.k ** lev):
            key = (lev, idx)
            node = flow.lookup(len(flow.rows), lev, idx)
            a = flow.allocation(node)
            if not a:
                continue
            wires = flow.bag_intervals(node, idx)
            before = sum(max(0, min(hi, q) - lo) for lo, hi in wires)
            after = a - before
            lo, hi = H.get(key, (0, 0))
            if before == a and lo != a:
                bad.append((lev, idx, 'below', lo, hi, a))
            elif after == a and hi != 0:
                bad.append((lev, idx, 'above', lo, hi, a))
    result = dict(depth=depth, scale=scale, N=N, q=q, stages=len(flow.rows),
                terminal_bad=len(bad), max_terminal_wrong=max(
                    [0] + [a - lo if side == 'below' else hi
                           for _, _, side, lo, hi, a in bad]),
                examples=bad[:8],
                widest_intervals=log)
    return (result, history) if include_history else result


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depth', type=int, default=4)
    ap.add_argument('--scale', type=int, default=65536)
    ap.add_argument('--threshold', default='1/3')
    ap.add_argument('--params', nargs=3, type=int, default=(2, 3, 2),
                    metavar=('X', 'Y', 'Z'))
    ap.add_argument('--row-bits', type=int, default=12)
    args = ap.parse_args()
    print('COUNT-INTERVAL CONTRACT RELAXATION; not a sorting proof')
    print(run(args.depth, args.scale, F(args.threshold),
              params=tuple(args.params), row_count=1 << args.row_bits))
