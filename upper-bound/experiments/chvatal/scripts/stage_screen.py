#!/usr/bin/env python3
"""Screen cheaper separator stages at ideal (attack-level) separators, UB-09 follow-on.

Tree side as in tree_pricing.py: (4.2)-(4.5) with analysis R1 (proved), R2c (best on paper)
or R3 (zero residual), attack eps_F table at the structural fringe, real x, y, z, L.

Stage families on an m = 2^L row matrix (S(q) = q(q+1)/2, Batcher):

  sort3       sort, scr, sort, scr, sort            3 S(L)                 leak d(L)
  sort2       sort, scr, sort                        2 S(L)                 leak E1(L)
  band        sort, scr, sort, scr, band(W)          2 S(L) + S(lg 2W)      leak d(L) + 4 T(W)
  band+merge  merge(f), scr, sort, scr, band(W)      S(L)-S(lg(f+1)) + S(L) + S(lg 2W)
  band3       sort, scr, sort, scr, band(W1), scr, band(W2)   attack level only; see code
  floor2      any stage containing two full m-row sorts, leak 0 (just the two sorts)
  floor1      one full m-row sort, leak 0

band(W) sorts disjoint bands of 2W rows; keys displaced further than the band escape.
T(W) is the round-1 tail beyond W rows (sub500-screen/screen.py tail_frac, certified form;
attack form = half of it, heuristic). The factor 4 is REVIEW-v7's. Merge-first assumes a
redesigned wiring giving sorted runs of f+1 rows (UB-44: the current R1 wiring gives 1).

Bulk: certified d (na_precision, two rounds), E1 (one round); attack d = 3.79 rows at 2^13
scaled m^(1/4), attack E1 = 95 rows at 2^13 scaled m^(1/2) (D2 sec. 11). Claim level: model.

    BULK_CACHE=<dir> python stage_screen.py
"""
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ideal_limit_screen import attack_table  # noqa: E402
from tree_pricing import allowance  # noqa: E402

LS = np.arange(4.0, 64.01, 2.0)


def S(q):
    return q * (q + 1) / 2


def cert_tables(cache_dir):
    path = os.path.join(cache_dir, 'bulk_cert2.npz') if cache_dir else None
    if path and os.path.exists(path):
        z = np.load(path)
        return z['d'], z['e1']
    sys.path.insert(0, os.path.join(HERE, '..', '..', 'walk-bound'))
    import na_precision as NP
    e1 = np.array([NP.e1_na(L, uniform=True) for L in LS])
    d = np.array([NP.d_na(L, e, uniform=True)[0] for L, e in zip(LS, e1)])
    if path:
        np.savez(path, d=d, e1=e1)
    return d, e1


def tail_frac(L, W):
    """screen.py tail_frac, vectorised over arrays L, W (fraction of m n)."""
    m = 2.0 ** L
    ps = np.geomspace(1e-14, 0.5, 400)
    H = -(ps * np.log(ps) + (1 - ps) * np.log1p(-ps))
    best = np.zeros(np.broadcast(L, W).shape)
    for p, h in zip(ps, H):
        v = math.sqrt(math.pi / 2) * np.sqrt(m * p * (1 - p)) + np.sqrt(2 * p * h * m) - W * p
        best = np.maximum(best, v)
    return best / m


LWS = np.arange(3.0, 64.0, 0.25)
_TCACHE = {}


def band_cost(L, room, level):
    """Least S(lg 2W) with 4 T(W) <= room (lg W on a 0.25 grid, 2W <= m); inf when none.
    L varies only along the last axis."""
    scale = (1.0 if level == 'certified' else 0.5) * float(os.environ.get('TAILSCALE', '1'))
    out = np.full(np.shape(room), np.inf)
    for j, Lj in enumerate(L[0, 0, :]):
        if Lj not in _TCACHE:
            _TCACHE[Lj] = tail_frac(np.full(LWS.shape, Lj), 2.0 ** LWS)      # decreasing in W
        T = 4 * scale * _TCACHE[Lj]
        r = room[..., j]
        # first index with T <= r: T is non-increasing, so count entries > r
        idx = (T[None, None, :] > r[..., None]).sum(axis=-1)
        lw = LWS[np.minimum(idx, len(LWS) - 1)]
        ok = (r > 0) & (idx < len(LWS)) & (lw + 1 <= Lj)
        out[..., j] = np.where(ok, S(lw + 1), np.inf)
    return out


def screen(stage, regime, level, dF, models, step=0.2):
    x = np.arange(1, 9 + 1e-9, step)
    z = np.arange(0.25, 9 + 1e-9, step)
    Ls = np.arange(6, 48, 0.25)
    X, Z, L = np.meshgrid(x, z, Ls, indexing='ij')
    lead = models[level]['d'](L) if stage != 'sort2' else models[level]['e1'](L)
    best = (math.inf, None)
    for yz in np.arange(step, 8 + 1e-9, step):
        Y = Z + yz
        k, A, nu = 2.0 ** X, 2.0 ** Y, 2.0 ** -Z
        fom = (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)
        f = 2.0 ** L * fom
        e = allowance(regime, X, Y, Z, dF, attack_table(np.maximum(f, 4), dF))
        base_ok = (e > 0) & (L >= 2 * (X + Y)) & (f >= 4)
        if stage == 'sort3':
            depth = np.where(lead <= e, 3 * S(L), np.inf)
        elif stage == 'sort2':
            depth = np.where(lead <= e, 2 * S(L), np.inf)
        elif stage in ('band', 'band+merge'):
            room = np.where(base_ok, e - lead, -1.0)
            first = S(L) if stage == 'band' else S(L) - S(np.floor(np.minimum(np.log2(f + 1), L)))
            depth = first + S(L) + band_cost(L, room, level)
        elif stage == 'band3':
            # third round: leak d / rho, rho = 2.8 at 2^13 growing as m^(1/8) (simulation, random
            # and two-level inputs, n = 1000); the round-2 band is 4x the round-2 spread
            # (30 rows at 2^13, scaled m^(1/4)) and its escapes are not charged (optimistic)
            rho = 2.8 * 2.0 ** ((L - 13) / 8)
            room = np.where(base_ok, e - lead / rho, -1.0)
            w2 = np.log2(120 * 2.0 ** ((L - 13) / 4))
            depth = 2 * S(L) + band_cost(L, room, level) + S(np.minimum(w2, L))
        elif stage == 'floor2':
            depth = 2 * S(L)
        elif stage == 'floor1':
            depth = S(L)
        else:
            raise ValueError(stage)
        s = np.where(base_ok, depth * (X + Y) / (X * Z), np.inf)
        i = np.unravel_index(np.argmin(s), s.shape)
        if s[i] < best[0]:
            best = (float(s[i]), (float(X[i]), float(Y[i]), float(Z[i]), float(L[i]), float(f[i])))
    return best


def main():
    cache = os.environ.get('BULK_CACHE')
    d, e1 = cert_tables(cache)
    ld, le1 = np.log(d), np.log(e1)
    models = {
        'certified': dict(d=lambda L: np.exp(np.interp(L, LS, ld)), e1=lambda L: np.exp(np.interp(L, LS, le1))),
        'attack': dict(d=lambda L: 2 * 3.79 * 2.0 ** ((L - 13) / 4) / 2.0 ** L,
                       e1=lambda L: 2 * 95 * 2.0 ** ((L - 13) / 2) / 2.0 ** L),
    }
    stages = sys.argv[1].split(',') if len(sys.argv) > 1 else ['floor1', 'floor2', 'sort2', 'sort3', 'band',
                                                                'band+merge']
    print('min slope (x y z L, fringe rows)', flush=True)
    for stage in stages:
        for level in (['attack'] if stage.startswith('floor') or stage == 'band3' else ['certified', 'attack']):
            for regime in ('R1', 'R2c', 'R3'):
                for dF in (0.5, 0.75):
                    v, p = screen(stage, regime, level, dF, models)
                    tag = 'infeasible' if p is None else (f'{v:.1f}  (' + ' '.join(f'{t:.2f}' for t in p[:4])
                                                          + f', f {p[4]:.0f})')
                    print(f'{stage:10s} {level:9s} {regime:3s} dF={dF:<4}: {tag}', flush=True)


if __name__ == '__main__':
    main()
