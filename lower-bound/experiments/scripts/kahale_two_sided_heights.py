#!/usr/bin/env python3
"""LB-02: two-sided (zero AND one) certificate-height relaxation of Kahale.

Each wire carries (z, o): zero height z and one height o, meaning a zero
certificate of size <= 2^z and a one certificate of size <= 2^o.  A comparator
(i < j) acts as (the Certificates.lean rule and its order dual):

    min output i : z = min(z_i, z_j),      o = max(o_i, o_j) + 1
    max output j : z = max(z_i, z_j) + 1,  o = min(o_i, o_j)

Necessary conditions for a d-stage sorting network (redundant comparators
removed), at time t = d - s:

    (Z) z_t(i) >= s + 1 for every i >= 2^(s+1)            (Kahale, checked)
    (O) o_t(i) >= s + 1 for every i <  n - 2^(s+1)        (order dual of Z)
    (G) graded: z_t(i) >= h+1 if i >= 2^h + 2^s; o_t(i) >= h+1 if
        i < n - 2^h - 2^s   (h = s is Z/O; from ApproxSelect for every t)
    (W) a comparator with s' later stages has j - i <= 2^(s'+1) - 1
                                                  (ActiveWidth.lean, active)

Modes
  hist  : joint (z, o) histogram with equal-pair matching (no positions);
          (equal z first, leftovers by o), checks the counting forms of
          Z and O, and prints the certified
          sandwich  N_d <= n*_joint(d) <= min_s 2^(d+1)(s+1)/C(d-s,s).
  pos   : the explicit positional block-halving schedule of
          kahale_positional_barrier.py, per wire, tracking (z, o); checks
          Z, O, W.  With --skip-wide, every block whose halving width breaks W
          idles for that stage (the schedule then satisfies W by construction).
  rle   : the same positional schedule stored as runs of constant (z, o);
          exact for arities far beyond memory (runs grow roughly like d^2/6).

All arithmetic is exact (Python ints / int64 positions).  These are finite
checks of a relaxation, not sorting claims.
    python -B kahale_two_sided_heights.py hist 64 128 256 512
    python -B kahale_two_sided_heights.py pos 40 56 64 72 80 88 --skip-wide
"""

import argparse
import json
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("\\", 1)[0].rsplit("/", 1)[0])
from kahale_height_barrier import fib  # noqa: E402

PHI = (1 + 5 ** 0.5) / 2
KAHALE = 1 / (1 - math.log2(PHI))


def arity(d):
    return (1 << d) // ((d + 1) * fib(d + 1))


def kahale_upper(d):
    """Largest n allowed by the kernel-checked n*C(d-s,s) <= 2^(d+1)(s+1)."""
    return min((1 << (d + 1)) * (s + 1) // math.comb(d - s, s)
               for s in range(d // 2 + 1))


# ---------------------------------------------------------------- histogram
def hist_round(counts):
    """Pair equal z.  Within a z-class pair equal (z, o) first; the leftover
    singletons (one per o) are then paired consecutively in o-order, so at
    most one wire per z-class idles.  This is a legal schedule choice."""
    out = {}

    def put(key, add):
        if add:
            out[key] = out.get(key, 0) + add

    byz = {}
    for (z, o), c in counts.items():
        byz.setdefault(z, []).append((o, c))
    for z, cls in byz.items():
        left = []
        for o, c in sorted(cls):
            pairs, idle = divmod(c, 2)
            put((z, o + 1), pairs)
            put((z + 1, o), pairs)
            if idle:
                left.append(o)
        for a, b in zip(left[0::2], left[1::2]):   # a <= b
            put((z, b + 1), 1)
            put((z + 1, a), 1)
        if len(left) % 2:
            put((z, left[-1]), 1)
    return out


def hist_check(d, n):
    counts = {(0, 0): n}
    worst = {"Z": -math.inf, "O": -math.inf}
    for t in range(d + 1):
        s = d - t
        lowz = sum(c for (z, _), c in counts.items() if z <= s)
        lowo = sum(c for (_, o), c in counts.items() if o <= s)
        budget = 1 << (s + 1)
        worst["Z"] = max(worst["Z"], lowz / budget)
        worst["O"] = max(worst["O"], lowo / budget)
        if t < d:
            counts = hist_round(counts)
    return worst


def run_hist(depths):
    for d in depths:
        n = arity(d)
        worst = hist_check(d, n)
        up = kahale_upper(d)
        print(json.dumps({
            "mode": "hist", "depth": d, "n_witness_bits": n.bit_length(),
            "worst_Z_count_over_budget": round(worst["Z"], 6),
            "worst_O_count_over_budget": round(worst["O"], 6),
            "both_pass": worst["Z"] <= 1 and worst["O"] <= 1,
            "d_over_log2_n_witness": d / math.log2(n),
            "d_over_log2_n_upper": d / math.log2(up),
            "log2_upper_over_witness": math.log2(up) - math.log2(n),
            "kahale_coefficient": KAHALE,
        }))


# ---------------------------------------------------------------- positional
def pos_run(d, n, skip_wide):
    z = np.zeros(n, dtype=np.int16)
    o = np.zeros(n, dtype=np.int16)
    idx = np.arange(n, dtype=np.int64)
    res = {"Z_ok": True, "O_ok": True, "W_ok": True, "W_violations": 0,
           "comparators": 0, "skipped_blocks": 0,
           "min_Z_margin": None, "min_O_margin": None}
    for t in range(d + 1):
        s = d - t
        if np.any(z[1:] < z[:-1]):
            raise ArithmeticError("zero-height profile not sorted")
        budget = 1 << (s + 1)
        lowz = np.nonzero(z <= s)[0]
        lowo = np.nonzero(o <= s)[0]
        zm = budget - (int(lowz[-1]) + 1) if lowz.size else budget
        om = (int(lowo[0]) - (n - budget)) if lowo.size else budget
        zm, om = min(zm, n), min(om, n)
        res["min_Z_margin"] = zm if res["min_Z_margin"] is None else min(res["min_Z_margin"], zm)
        res["min_O_margin"] = om if res["min_O_margin"] is None else min(res["min_O_margin"], om)
        res["Z_ok"] &= zm >= 0
        res["O_ok"] &= om >= 0
        if t == d:
            break
        # block structure of equal z
        starts = np.flatnonzero(np.r_[True, z[1:] != z[:-1]])
        sizes = np.diff(np.r_[starts, n])
        bstart = np.repeat(starts, sizes)
        bsize = np.repeat(sizes, sizes)
        k = idx - bstart
        u = (bsize + 1) // 2
        lo_mask = k < bsize // 2
        later = d - t - 1                      # stages after this one
        wmax = (1 << (later + 1)) - 1 if later < 62 else 1 << 62
        wide = u > wmax
        if skip_wide:
            res["skipped_blocks"] += int(np.count_nonzero(sizes[(sizes + 1) // 2 > wmax] > 1))
            lo_mask &= ~wide
        lo = idx[lo_mask]
        hi = lo + u[lo_mask]
        nviol = int(np.count_nonzero(wide[lo_mask]))
        res["W_violations"] += nviol
        res["W_ok"] &= nviol == 0
        res["comparators"] += int(lo.size)
        zl, zh, ol, oh = z[lo], z[hi], o[lo], o[hi]
        z[lo], z[hi] = np.minimum(zl, zh), np.maximum(zl, zh) + 1
        o[lo], o[hi] = np.maximum(ol, oh) + 1, np.minimum(ol, oh)
    return res


def run_pos(depths, skip_wide):
    for d in depths:
        n = arity(d)
        if n > 60_000_000:
            print(json.dumps({"depth": d, "error": "arity too large for per-wire run"}))
            continue
        r = pos_run(d, n, skip_wide)
        r.update({"mode": "pos", "skip_wide": skip_wide, "depth": d, "n": n,
                  "d_over_log2_n": d / math.log2(n), "kahale_coefficient": KAHALE})
        print(json.dumps(r), flush=True)


# ------------------------------------------------- positional, run-length
def _slice(runs, start, length):
    """Pieces (len, o) of a run list [(len, o)] restricted to [start, start+length)."""
    out, pos = [], 0
    end = start + length
    for ln, o in runs:
        a, b = max(pos, start), min(pos + ln, end)
        if a < b:
            out.append((b - a, o))
        pos += ln
        if pos >= end:
            break
    return out


def _zip(xs, ys):
    """Common refinement of two piece lists of equal total length."""
    i = j = 0
    xs, ys = list(xs), list(ys)
    out = []
    while i < len(xs):
        (lx, ox), (ly, oy) = xs[i], ys[j]
        m = min(lx, ly)
        out.append((m, ox, oy))
        xs[i], ys[j] = (lx - m, ox), (ly - m, oy)
        if xs[i][0] == 0:
            i += 1
        if ys[j][0] == 0:
            j += 1
    return out


def pos_rle(d, n, skip_wide):
    """Exact run-length version of pos_run (same schedule, same checks)."""
    blocks = [(0, [(n, 0)])]            # [(z, [(len, o), ...])], z increasing
    res = {"Z_ok": True, "O_ok": True, "GZ_ok": True, "GO_ok": True,
           "W_ok": True, "W_violating_blocks": 0,
           "skipped_blocks": 0, "max_runs": 1}
    for t in range(d + 1):
        s = d - t
        budget = 1 << (s + 1)
        # Z: z sorted, so the low-z wires are a prefix
        lowz = sum(sum(ln for ln, _ in r) for z, r in blocks if z <= s)
        res["Z_ok"] &= lowz <= budget
        # O: first position with o <= s must be >= n - budget
        pos, first = 0, None
        for z, r in blocks:
            for ln, o in r:
                if o <= s:
                    first = pos
                    break
                pos += ln
            if first is not None:
                break
        if first is not None:
            res["O_ok"] &= first >= n - budget
        # graded forms G (from ApproxSelect pre t 2^s for every t):
        #   zero side: z(i) >= h+1 whenever i >= 2^h + 2^s
        #   one side : o(i) >= h+1 whenever i <  n - 2^h - 2^s
        pos, lowz_h = 0, {}
        firsto = {}
        for z, r in blocks:
            for ln, o in r:
                if o not in firsto:
                    firsto[o] = pos
                pos += ln
            lowz_h[z] = pos                       # count of wires with height <= z
        for z, cnt in lowz_h.items():
            if cnt > (1 << z) + (1 << s):
                res["GZ_ok"] = False
        best = None
        for o in sorted(firsto):
            best = firsto[o] if best is None else min(best, firsto[o])
            if best < n - (1 << o) - (1 << s):
                res["GO_ok"] = False
        res["max_runs"] = max(res["max_runs"], sum(len(r) for _, r in blocks))
        if t == d:
            break
        later = d - t - 1
        wmax = (1 << (later + 1)) - 1
        new = []

        def emit(z, pieces):
            for ln, o in pieces:
                if not ln:
                    continue
                if new and new[-1][0] == z:
                    r = new[-1][1]
                    if r and r[-1][1] == o:
                        r[-1] = (r[-1][0] + ln, o)
                    else:
                        r.append((ln, o))
                else:
                    new.append((z, [(ln, o)]))

        for z, r in blocks:
            m = sum(ln for ln, _ in r)
            f, u = m // 2, (m + 1) // 2
            if f and u > wmax:
                res["W_violating_blocks"] += 1
                res["W_ok"] = False
                if skip_wide:
                    res["skipped_blocks"] += 1
                    emit(z, r)
                    continue
            pairs = _zip(_slice(r, 0, f), _slice(r, u, f)) if f else []
            emit(z, [(ln, max(a, b) + 1) for ln, a, b in pairs])
            if u > f:
                emit(z, _slice(r, f, 1))
            emit(z + 1, [(ln, min(a, b)) for ln, a, b in pairs])
        blocks = new
    return res


def run_rle(depths, skip_wide, scale=1.0):
    for d in depths:
        n = int(arity(d) * scale)
        r = pos_rle(d, n, skip_wide)
        if skip_wide:
            r["W_ok"] = True   # wide blocks idled, so the run satisfies W
        r.update({"mode": "rle", "skip_wide": skip_wide, "depth": d,
                  "scale": scale, "n_bits": n.bit_length(),
                  "d_over_log2_n": d / math.log2(n)})
        print(json.dumps(r), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("mode", choices=["hist", "pos", "rle"])
    p.add_argument("depth", type=int, nargs="+")
    p.add_argument("--skip-wide", action="store_true")
    p.add_argument("--scale", type=float, default=1.0,
                   help="rle only: run on int(scale * N_d) wires (control runs)")
    a = p.parse_args()
    if a.mode == "hist":
        run_hist(a.depth)
    elif a.mode == "pos":
        run_pos(a.depth, a.skip_wide)
    else:
        run_rle(a.depth, a.skip_wide, a.scale)


if __name__ == "__main__":
    main()
