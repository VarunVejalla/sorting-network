#!/usr/bin/env python3
"""Band balancing for the fringe: does R rounds of merge-and-deal on column top bands cut misses ~2^-R?

Simulation only (finite, seeded); heuristic adversaries, not a worst-case certificate.

Model.  A bag is an m x n matrix after the two-round separator (see sim_lateral_residual.py): an
extreme set S of j keys has per-column counts p_c, occupying rows 0..p_c-1.  The fringe F is the top
f rows of every column.  Fringe misses = sum_c (p_c - f)_+ (keys of S outside F).

Band balancing: R rounds; in round r a fixed perfect matching M_r pairs the columns, and each pair
merges its two top bands of height h (sorted segments, bitonic merge depth lg(2h)) and deals the
merged sequence's even/odd positions back.  For the extreme set this maps band counts
(x, y) -> (ceil((x+y)/2), floor((x+y)/2)) with x, y capped at h; keys below the band are untouched.

Adversaries (they know sigma1, sigma2 and all matchings):
  random     : S uniformly placed;
  conc0      : concentrate after round 2 into target columns (the h^2/2-cost construction), ignoring
               the matchings;
  ancestry   : choose final columns T and give excess to every column that feeds T through the
               matching tree (2^R columns per target), so balancing cannot dilute it.
Misses are reported as a fraction of j; the 1/(2f) line is the one-round obstruction scale.

Run:  python -I sim_band_fringe.py
"""
import numpy as np


def round2_counts(cnt1, inv2):
    m = inv2.shape[0]
    rows = np.arange(m)[:, None]
    return (cnt1[inv2] > rows).sum(axis=0)


def build_cnt1(rng, m, n, j, inv2, targets, h):
    """Round-1 counts making each target column receive >= h after round 2; rest random."""
    cnt1 = np.zeros(n, dtype=np.int64)
    for T in targets:
        for i in range(h):
            c = inv2[i, T]
            cnt1[c] = max(cnt1[c], i + 1)
    used = int(cnt1.sum())
    if used > j:
        return None
    rest = j - used
    if rest:
        cap = m - cnt1
        cnt1 = cnt1 + np.bincount(rng.choice(np.repeat(np.arange(n), cap), size=rest, replace=False), minlength=n)
    return cnt1


def balance(p, matchings, h):
    p = p.copy()
    for M in matchings:
        a, b = M[:, 0], M[:, 1]
        x, y = np.minimum(p[a], h), np.minimum(p[b], h)
        ex_a, ex_b = p[a] - x, p[b] - y
        s = x + y
        p[a] = (s + 1) // 2 + ex_a
        p[b] = s // 2 + ex_b
    return p


def ancestry(matchings, T):
    """Columns whose band counts flow into column T through the matching sequence."""
    S = {T}
    for M in reversed(matchings):
        part = np.empty(M.size, dtype=np.int64)
        part[M[:, 0]] = M[:, 1]
        part[M[:, 1]] = M[:, 0]
        S = S | {int(part[c]) for c in S}
    return sorted(S)


def misses(p, f):
    return int(np.maximum(p - f, 0).sum())


def run(rng, m, n, f, j, R, mode, trials=3):
    out = []
    for _ in range(trials):
        inv2 = np.argsort(np.array([rng.permutation(n) for _ in range(m)]), axis=1)
        matchings = [rng.permutation(n).reshape(-1, 2) for _ in range(R)]
        h = min(m, 4 * f)
        best = 0
        if mode == "random":
            cnt1 = np.bincount(rng.choice(m * n, size=j, replace=False) % n, minlength=n)
            best = misses(balance(round2_counts(cnt1, inv2), matchings, h), f)
        else:
            for hh in sorted({f + 1, int(1.5 * f), 2 * f, 3 * f, 4 * f}):
                if hh > m:
                    continue
                if mode == "conc0":
                    nt = max(1, j // (2 * hh * (hh + 1) // 2))
                    targets = list(rng.choice(n, size=min(n, nt), replace=False))
                else:  # ancestry
                    targets, budget = [], j // 2
                    for T in rng.permutation(n):
                        anc = ancestry(matchings, int(T))
                        cost = len(anc) * hh * (hh + 1) // 2
                        if cost > budget:
                            break
                        targets += [c for c in anc if c not in targets]
                        budget -= cost
                    if not targets:
                        continue
                cnt1 = build_cnt1(rng, m, n, j, inv2, targets, hh)
                if cnt1 is None:
                    continue
                best = max(best, misses(balance(round2_counts(cnt1, inv2), matchings, h), f))
        out.append(best / j)
    return float(np.max(out))


def main():
    rng = np.random.default_rng(1018)
    m, n, f = 1024, 1024, 16
    print(f"m={m}, n={n}, fringe f={f} rows, band h=4f; misses/j (max over trials); 1/(2f) = {1/(2*f):.4f}")
    print("  j/(f n)   mode       " + "  ".join(f"R={R:<5d}" for R in range(0, 7)))
    for frac in (0.25, 0.5):
        j = int(frac * f * n)
        for mode in ("random", "conc0", "ancestry"):
            vals = [run(rng, m, n, f, j, R, mode) for R in range(0, 7)]
            print(f"  {frac:5.2f}    {mode:9s} " + "  ".join(f"{v:7.5f}" for v in vals), flush=True)


if __name__ == "__main__":
    main()
