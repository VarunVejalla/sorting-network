#!/usr/bin/env python3
"""LB-33: does a correlation (Harris / BK / Reimer) potential see the
middle-wire defect of the Kahale barrier schedule at an exponential rate?

Model.  0/1 inputs x in {0,1}^n, i.i.d. with P(x_k = 0) = p (product measure
mu_p), or uniform on a weight slice (threshold images of a random
permutation).  Wire w after t stages computes a monotone function f_w; write
q_w(p) = mu_p(f_w = 0).  A comparator (lo < hi) sends
    min -> lo : zero iff a = 0 OR  b = 0   (event A u B, A = {a = 0})
    max -> hi : zero iff a = 0 AND b = 0   (event A n B)
and conserves q_lo' + q_hi' = q_a + q_b.  A, B are decreasing events, so
    Harris/FKG   mu(A n B) >= mu(A) mu(B)                         (lower)
    BK/Reimer    mu(A box B) <= mu(A) mu(B)                        (upper)
where A box B = "disjoint zero-certificates of a and of b inside zeros(x)".
Hence  mu(A box B) <= mu(A) mu(B) <= mu(A n B), and the covariance excess
mu(A n B) - mu(A) mu(B) is at most the OVERLAP-ONLY mass
    Ov = mu(A n B) - mu(A box B)   (both zero, every witness pair intersects).

Requirements (sized graded window (G) of LB-02/LB-24, s stages remaining,
w = 2^s, T_m(p) = P(Bin(n, p) >= m)):
    zero side  q_i(p) <= T_{i-w+1}(p),   one side  q_i(p) >= T_{i+w+1}(p),
    terminal (s = 0)  q_i(p) = T_{i+1}(p)  for all p.
The violation V_s = max_{i,p} of the positive parts is reported.

Modes
  ind   d [d ...]        independent (read-once / tree-unfolding) propagation
                         q_lo = a + b - ab, q_hi = ab on a p grid at N_d;
                         V_s per s and the worst wires.  This is the best case
                         of every potential that upper-bounds joint zero mass
                         by BK (Ov = 0), see the note.
  truth d [d ...]        actual barrier network on random permutations,
                         product-measure q_i(p) = E T_{R_i + 1}(p); V_s and
                         the gap |q_true - q_ind| on the worst wires.
  scan  d [d ...]        largest n (grid 2^(k/8)) with V_s <= eps for all s,
                         for 'ind' and 'truth' (sampled); log2(N_d / n).
  bk    n [n ...] --depth d   exact enumeration of all 2^n inputs (n <= 16):
                         per stage, mu(A n B), mu(A)mu(B), mu(A box B) for every
                         comparator (subset convolution), split by wire class.
Finite computations; no sorting claim, no Lean.
"""

import argparse
import json
import math
import sys

import numpy as np
from scipy.stats import binom

sys.path.insert(0, __file__.rsplit("\\", 1)[0].rsplit("/", 1)[0])
from kahale_pair_union_rate import arity, schedule  # noqa: E402

PHI = (1 + 5 ** 0.5) / 2
KAHALE = 1 / (1 - math.log2(PHI))


def pgrid(n, P):
    """p grid concentrated where the tails move: p = m/n for m on a grid,
    plus a few extreme points."""
    ms = np.unique(np.linspace(0.5, n - 0.5, P))
    return ms / n


def tails(n, ps):
    """T[k, m] = P(Bin(n, p_k) >= m) for m = 0..n+1 (T[.,0] = 1, T[.,n+1] = 0)."""
    m = np.arange(n + 2)
    return binom.sf(m[None, :] - 1, n, ps[:, None])


def violation(q, T, n, s):
    """q: (P, n) zero-probabilities.  Returns (V, wire, side)."""
    i = np.arange(n)
    if s == 0:
        ref = T[:, i + 1]
        dev = np.abs(q - ref)
        k, j = np.unravel_index(np.argmax(dev), dev.shape)
        return float(dev[k, j]), int(j), "terminal"
    w = 1 << s if s < 62 else 1 << 62
    up = T[:, np.clip(i - w + 1, 0, n + 1)]
    lo = T[:, np.clip(i + w + 1, 0, n + 1)]
    vz = q - up
    vo = lo - q
    a, b = vz.max(), vo.max()
    if a >= b:
        k, j = np.unravel_index(np.argmax(vz), vz.shape)
        return max(0.0, float(a)), int(j), "zero"
    k, j = np.unravel_index(np.argmax(vo), vo.shape)
    return max(0.0, float(b)), int(j), "one"


def ind_curves(layers, n, ps, keep):
    q = np.repeat(ps[:, None], n, axis=1).astype(np.float64)
    out = {}
    if 0 in keep:
        out[0] = q.copy()
    for t, (lo, hi) in enumerate(layers, start=1):
        a, b = q[:, lo], q[:, hi]
        ab = a * b
        q[:, lo], q[:, hi] = a + b - ab, ab
        if t in keep:
            out[t] = q.copy()
    return out


def truth_curves(layers, n, ps, keep, samples, seed=7, batch=128):
    """Product-measure zero-probabilities of the actual network:
    q_i(p) = E_perm T_{R_i + 1}(p) (R_i = rank on wire i)."""
    rng = np.random.default_rng(seed)
    T = tails(n, ps).astype(np.float32)
    acc = {t: np.zeros((len(ps), n)) for t in keep}
    minr = {t: np.full(n, n) for t in keep}
    maxr = {t: np.full(n, -1) for t in keep}
    done = 0
    while done < samples:
        b = min(batch, samples - done)
        X = np.argsort(rng.random((b, n)), axis=1).astype(np.int32)

        def record(t):
            for r in range(b):
                acc[t] += T[:, X[r] + 1]
            minr[t] = np.minimum(minr[t], X.min(0))
            maxr[t] = np.maximum(maxr[t], X.max(0))
        if 0 in keep:
            record(0)
        for t, (lo, hi) in enumerate(layers, start=1):
            a, c = X[:, lo], X[:, hi]
            X[:, lo], X[:, hi] = np.minimum(a, c), np.maximum(a, c)
            if t in keep:
                record(t)
        done += b
    return ({t: acc[t] / samples for t in keep}, minr, maxr)


def rank_violation(minr, maxr, n, s):
    """Witnessed rank-window violation (LB-24 truth mode)."""
    i = np.arange(n)
    w = 0 if s == 0 else (1 << s)
    return int(max(((i - w) - minr).max(), (maxr - (i + w)).max(), 0))


def run_ind(d, n, cleanup, P, smax):
    layers = list(schedule(d, n, cleanup))
    D = len(layers)
    ps = pgrid(n, P)
    T = tails(n, ps)
    keep = set(range(max(0, D - smax), D + 1))
    cur = ind_curves(layers, n, ps, keep)
    rows = []
    for t in sorted(keep):
        s = D - t
        v, j, side = violation(cur[t], T, n, s)
        rows.append({"s": s, "V": round(v, 4), "wire": j, "side": side})
    mid = n // 2
    def width(qq):
        return float(np.interp(0.9, qq, ps) - np.interp(0.1, qq, ps))
    wi, ws = width(cur[D][:, mid]), width(T[:, mid + 1])
    return ({"d": d, "n": n, "depth": D, "mid_width_ind": round(wi, 5),
             "mid_width_sorted": round(ws, 5),
             "log2(width_ind/width_sorted)": round(math.log2(wi / ws), 3),
             "rows": rows}, cur, ps, T, layers)


def first_bad(rows, eps):
    bad = [r["s"] for r in rows if r["V"] > eps]
    return max(bad) if bad else None


def cmd_ind(args):
    res = []
    for d in args.depths:
        n = args.n or arity(d)
        r, *_ = run_ind(d, n, args.cleanup, args.P, args.smax)
        r["first_s_with_V>eps"] = first_bad(r["rows"], args.eps)
        res.append(r)
        print(json.dumps(r), flush=True)
    return res


def cmd_truth(args):
    for d in args.depths:
        n = args.n or arity(d)
        ri, icur, ps, T, layers = run_ind(d, n, args.cleanup, args.P, args.smax)
        D = len(layers)
        keep = set(range(max(0, D - args.smax), D + 1))
        tcur, minr, maxr = truth_curves(layers, n, ps, keep, args.samples)
        rows = []
        for t in sorted(keep):
            s = D - t
            v, j, side = violation(tcur[t], T, n, s)
            gap = np.abs(tcur[t] - icur[t])
            gi = gap.max(0)
            jw = int(np.argmax(gi))
            rows.append({"s": s, "V_true": round(v, 4), "wire": j, "side": side,
                         "rank_viol": rank_violation(minr[t], maxr[t], n, s),
                         "V_ind": next(x["V"] for x in ri["rows"] if x["s"] == s),
                         "max_gap_true_ind": round(float(gi.max()), 4),
                         "gap_wire": jw,
                         "mean_gap": round(float(gap.max(0).mean()), 4)})
        # threshold location / width on the middle wire, both models
        mid = n // 2
        def thr(c):
            qq = c[:, mid]
            p50 = float(np.interp(0.5, qq, ps))
            p10 = float(np.interp(0.1, qq, ps)); p90 = float(np.interp(0.9, qq, ps))
            return {"p50": round(p50, 4), "width10_90": round(p90 - p10, 4)}
        req = {"p50": round(float(np.interp(0.5, T[:, mid + 1], ps)), 4),
               "width10_90": round(float(np.interp(0.9, T[:, mid + 1], ps)
                                         - np.interp(0.1, T[:, mid + 1], ps)), 4)}
        out = {"d": d, "n": n, "depth": D, "samples": args.samples,
               "middle_wire": mid, "mid_true": thr(tcur[D]), "mid_ind": thr(icur[D]),
               "mid_sorted": req, "rows": rows}
        print(json.dumps(out), flush=True)


def ok_ind(d, n, cleanup, P, eps, smax):
    r, *_ = run_ind(d, n, cleanup, P, smax)
    return max(x["V"] for x in r["rows"]) <= eps


def ok_truth(d, n, cleanup, P, eps, smax, samples):
    layers = list(schedule(d, n, cleanup))
    D = len(layers)
    ps = pgrid(n, P)
    T = tails(n, ps)
    keep = set(range(max(0, D - smax), D + 1))
    tcur, minr, maxr = truth_curves(layers, n, ps, keep, samples)
    return max(violation(tcur[t], T, n, D - t)[0] for t in keep) <= eps


def cmd_scan(args):
    for d in args.depths:
        Nd = arity(d)
        out = {"d": d, "N_d": Nd}
        for model in args.models:
            best, fails, k = None, 0, 8
            while fails < args.patience:
                n = int(round(2 ** (k / 8)))
                k += 1
                if n < 4 or (best is not None and n <= best):
                    continue
                if n > args.nmax:
                    break
                good = (ok_ind(d, n, args.cleanup, args.P, args.eps, args.smax)
                        if model == "ind" else
                        ok_truth(d, n, args.cleanup, args.P, args.eps, args.smax,
                                 args.samples))
                if good:
                    best, fails = n, 0
                elif best is not None:
                    fails += 1
            out[model] = best
            out["log2(N_d/" + model + ")"] = (None if not best
                                              else round(math.log2(Nd / best), 2))
        print(json.dumps(out), flush=True)


# ------------------------------------------------------------- exact BK mode
def popcounts(n):
    return np.array([bin(x).count("1") for x in range(1 << n)], dtype=np.int64)


def ranked_zeta(f, n, pc):
    """F[k, X] = sum_{S subset X, |S| = k} f(S)."""
    F = np.zeros((n + 1, 1 << n), dtype=np.int64)
    F[pc, np.arange(1 << n)] = f
    for b in range(n):
        bit = 1 << b
        idx = np.arange(1 << n)
        hi = idx[(idx & bit) != 0]
        F[:, hi] += F[:, hi ^ bit]
    return F


def moebius(F, n):
    for b in range(n):
        bit = 1 << b
        idx = np.arange(1 << n)
        hi = idx[(idx & bit) != 0]
        F[..., hi] -= F[..., hi ^ bit]
    return F


def disjoint_occurrence(fa, fb, n, pc):
    """D(Z) = OR_{S subset Z} fa(S) and fb(Z minus S)  (subset convolution)."""
    A = ranked_zeta(fa.astype(np.int64), n, pc)
    B = ranked_zeta(fb.astype(np.int64), n, pc)
    H = np.zeros((n + 1, 1 << n), dtype=np.int64)
    for k in range(n + 1):
        for j in range(k + 1):
            H[k] += A[j] * B[k - j]
    H = moebius(H, n)
    return H[pc, np.arange(1 << n)] > 0


def cmd_bk(args):
    for n in args.ns:
        d = args.depth
        layers = list(schedule(d, n, args.cleanup))
        N = 1 << n
        pc = popcounts(n)
        # zero-set Z (bit k = input k is 0); wire value 0 <=> Z contains a cert.
        # input values: x_k = 0 iff bit k of Z.  Wire functions as bit arrays.
        Z = np.arange(N)
        val = np.array([((Z >> k) & 1) == 0 for k in range(n)])  # value 1 iff not zero
        # val[w][Z] = value (True = 1) on input with zero set Z
        p = args.p
        wts = p ** pc * (1 - p) ** (n - pc)
        rows = []
        for t, (lo, hi) in enumerate(layers, start=1):
            stats = {"mid": [0, 0, 0, 0, 0], "edge": [0, 0, 0, 0, 0]}
            for a_, b_ in zip(lo.tolist(), hi.tolist()):
                A0 = ~val[a_]; B0 = ~val[b_]
                qa, qb = wts[A0].sum(), wts[B0].sum()
                J = wts[A0 & B0].sum()
                Dj = wts[disjoint_occurrence(A0, B0, n, pc)].sum()
                cls = "mid" if (n // 4 <= a_ < 3 * n // 4 or n // 4 <= b_ < 3 * n // 4) else "edge"
                st = stats[cls]
                st[0] += 1; st[1] += J; st[2] += qa * qb; st[3] += Dj; st[4] += J - Dj
                va, vb = val[a_].copy(), val[b_].copy()
                val[a_], val[b_] = va & vb, va | vb
            row = {"t": t, "s": len(layers) - t}
            for cls, st in stats.items():
                if st[0]:
                    row[cls] = {"cmp": st[0], "J": round(st[1], 4), "qaqb": round(st[2], 4),
                                "BKdisj": round(st[3], 4), "overlap_only": round(st[4], 4),
                                "cov": round(st[1] - st[2], 4),
                                "ov_share": round(st[4] / st[1], 3) if st[1] > 0 else None}
            rows.append(row)
        # does it sort?
        # sorted: wire i (ascending) is 1 iff #zeros <= i ; pc = #zeros
        srt = all((val[i] == (pc <= i)).all() for i in range(n))
        print(json.dumps({"n": n, "depth": len(layers), "p": p, "sorts": bool(srt),
                          "rows": rows}), flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("ind", "truth", "scan"):
        s = sub.add_parser(name)
        s.add_argument("depths", type=int, nargs="+")
        s.add_argument("--n", type=int, default=0)
        s.add_argument("--cleanup", type=int, default=2)
        s.add_argument("--P", type=int, default=96)
        s.add_argument("--smax", type=int, default=14)
        s.add_argument("--eps", type=float, default=0.02)
        s.add_argument("--samples", type=int, default=1024)
        if name == "scan":
            s.add_argument("--models", default="ind,truth")
            s.add_argument("--nmax", type=int, default=40000)
            s.add_argument("--patience", type=int, default=4)
    b = sub.add_parser("bk")
    b.add_argument("ns", type=int, nargs="+")
    b.add_argument("--depth", type=int, required=True)
    b.add_argument("--cleanup", type=int, default=2)
    b.add_argument("--p", type=float, default=0.5)
    a = ap.parse_args()
    if a.cmd == "scan":
        a.models = a.models.split(",")
    {"ind": cmd_ind, "truth": cmd_truth, "scan": cmd_scan, "bk": cmd_bk}[a.cmd](a)


if __name__ == "__main__":
    main()
