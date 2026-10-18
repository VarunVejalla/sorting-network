#!/usr/bin/env python3
"""Scratch: how many layers could a 'run-aware' first column sort save on the REAL flow table?

Input: flow_table.txt, rows `d t l a up down` dumped from Lean (`flowA7/flowUp7/flowDown7`).
Model (see discussion): a node at time t with a > 2^63 wires runs sort - scramble - sort on an
m x n matrix, m in (2^58, 2^59], a = m n, up = 2 f n, down = b n, m = 2 f + 64 b.  After its second sort
every column is exactly sorted, so what it sends is
    up   : the top f and bottom f rows of every column  -> sorted runs of length f
    down : b consecutive rows of every column per child  -> sorted runs of length b.
A node with a <= 2^63 wires sorts all a wires (one sorter), so it sends 2 runs of length up/2 (up) and
down-blocks (runs of length `down`).  A node with down = 0 runs no separator and passes everything up
unchanged, so the runs it sends are those it received.  The input of the first sort at (t+1, l) is the union of
  parent  (t, l-1): its `down` pieces (runs of its down-run length), and
  children(t, l+1): their `up` pieces (runs of their up-run length).
A first sort of height m on inputs that are unions of sorted runs of length >= 2^s costs T(L) - T(s) layers
(skip the first s merge levels of bitonic sort); a full sort costs T(L), T(p) = p(p+1)/2.
We report, per time step, the depth of the stage with and without the run-aware first sort.
"""
import math
import sys
from math import gcd

import sympy

LO, HI = 2 ** 58, 2 ** 59          # window for m
SMALL = 2 ** 63                    # nodes with a <= SMALL are sorted by one sorter


def T(p):
    return p * (p + 1) // 2


def clog2(x):
    return (x - 1).bit_length()


def flog2(x):
    return (x & -x).bit_length() - 1   # 2-adic valuation: largest 2^s dividing the run


def divisors_in(g, lo, hi):
    """divisors n of g with lo <= n <= hi (g is smooth)."""
    fac = sympy.factorint(g)
    divs = [1]
    for p, e in fac.items():
        divs = [d * p ** k for d in divs for k in range(e + 1)]
    return sorted(d for d in divs if lo <= d <= hi)


def geometry(a, up, down):
    """(m, n, f, b) with m in (LO, HI], or None."""
    g = gcd(gcd(a, up // 2), down) if up else gcd(a, down)
    nlo = -(-a // HI)                  # n >= a / HI
    nhi = (a - 1) // LO                # n < a / LO   (m > LO)
    ns = divisors_in(g, nlo, nhi)
    if not ns:
        return None
    n = ns[-1]                         # largest n  -> smallest m, as in the paper's scaling
    m = a // n
    return m, n, up // (2 * n), down // n


def load(path):
    F = {}
    for line in open(path):
        parts = line.split()
        if len(parts) != 6 or not all(p.isdigit() for p in parts):
            continue
        d, t, l, a, u, dn = map(int, parts)
        F[(d, t, l)] = (a, u, dn)
    return F


def lg(x):
    return math.log2(x) if x > 0 else 0.0


def analyse(F, d, verbose=True):
    tf = max(t for (dd, t, l) in F if dd == d)
    out = {}      # (t,l) -> dict(kind, geom, up_run, down_run)
    rows = []
    for t in range(0, tf + 1):
        for l in range(0, d + 1):
            if (d, t, l) not in F:
                continue
            a, u, dn = F[(d, t, l)]
            if t == 0:
                in_run, srcs = 1, "input"
            else:
                pieces = []
                tau_p = F.get((d, t - 1, l - 1), (0, 0, 0))[2] if l >= 1 else 0
                if tau_p:
                    pieces.append(("parent", out[(t - 1, l - 1)]["down_run"], tau_p))
                if (d, t - 1, l + 1) in F:
                    u_c = F[(d, t - 1, l + 1)][1]
                    if u_c:
                        pieces.append(("children", out[(t - 1, l + 1)]["up_run"], 64 * u_c))
                tot = sum(p[2] for p in pieces)
                if tot != a:
                    print(f"  WARNING d={d} t={t} l={l}: a={a} but sources give {tot}")
                in_run = min((p[1] for p in pieces), key=lambda r: r & -r) if pieces else 1
                srcs = "+".join(f"{p[0]}[run 2^{lg(p[1]):.1f}]" for p in pieces)
            geo = None
            if dn == 0:                                    # pass-through: sends everything up unchanged
                kind, depth_full, depth_run = "pass", 0, 0
                out[(t, l)] = dict(kind=kind, up_run=in_run, down_run=in_run)
            elif t == 0:                                   # root: arbitrary input, m = 2^79 (additive constant)
                kind, depth_full, depth_run = "root", None, None
                out[(t, l)] = dict(kind=kind, up_run=1, down_run=max(dn // 4, 1))
            elif a <= SMALL:
                L = clog2(a)
                kind = "small"
                depth_full = T(L)
                depth_run = T(L) - T(flog2(in_run)) if flog2(in_run) > 0 else T(L)
                out[(t, l)] = dict(kind=kind, up_run=max(u // 2, 1), down_run=dn)
            else:
                geo = geometry(a, u, dn)
                if geo is None:
                    print(f"  NO GEOMETRY d={d} t={t} l={l} a={a} up={u} down={dn}")
                    continue
                m, n, f, b = geo
                L = clog2(m)
                kind = "sep"
                depth_full = 2 * T(L)
                depth_run = T(L) + (T(L) - T(flog2(in_run)) if flog2(in_run) > 0 else T(L))
                out[(t, l)] = dict(kind=kind, up_run=max(f, 1), down_run=b)
            rows.append((t, l, kind, a, u, dn, geo, in_run, srcs, depth_full, depth_run))
    print(f"\n=== d = {d} ===")
    print("  t | binding node           | full | run-aware | saving      | min input run")
    summary = []
    for t in range(1, tf + 1):
        rs = [r for r in rows if r[0] == t and r[9]]
        if not rs:
            continue
        full = max(r[9] for r in rs)
        run = max(r[10] for r in rs)
        bind = max(rs, key=lambda r: r[10])
        summary.append((t, full, run))
        lgm = f"lg m={math.log2(bind[6][0]):.2f}" if bind[6] else "small bag"
        print(f"{t:3d} | l={bind[1]:2d} {bind[2]:5s} {lgm:14s}| {full:5d} | {run:6d}    | {full - run:4d} ({100 * (full - run) / full:4.1f}%) | 2^{flog2(bind[7])}")
    if verbose:
        print("\n  detail rows (t,l,kind,a,up,down, geometry, input min-run, sources)")
        for r in rows:
            if r[0] in (1, 2, 3, 4, tf - 1, tf):
                g = r[6]
                gs = (f"m=2^{math.log2(g[0]):.2f} n=2^{math.log2(g[1]):.1f} f=2^{lg(g[2]):.2f} b=2^{lg(g[3]):.2f}" if g else "")
                print(f"  t={r[0]:2d} l={r[1]:2d} {r[2]:5s} a=2^{lg(r[3]):.1f} up=2^{lg(r[4]):.1f} down=2^{lg(r[5]):.1f} {gs} "
                      f"| in-run v2={flog2(r[7])} | {r[8]}")
    return summary


if __name__ == "__main__":
    F = load(sys.argv[1])
    ds = sorted({d for (d, t, l) in F})
    for d in ds:
        s = analyse(F, d, verbose=(d == ds[0]))
        if s:
            tot_full = sum(x[1] for x in s)
            tot_run = sum(x[2] for x in s)
            print(f"  sum over stages 1..tf: full {tot_full}, run-aware {tot_run}  ->  "
                  f"{100 * (tot_full - tot_run) / tot_full:.1f}% saved")
