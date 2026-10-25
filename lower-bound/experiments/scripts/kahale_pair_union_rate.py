#!/usr/bin/env python3
"""LB-24: does the pairwise union-cost recurrence force a rate above 3.2706?

State (sizes, not heights).  For wires x, y after t stages:
    z[x], o[x]   upper bounds on the minimum zero / one certificate size,
    Z[x,y]       upper bound on the minimum size of a set forcing x AND y zero,
    O[x,y]       the same for "x AND y one";  Z[x,x] = z[x], O[x,x] = o[x].
Initially z = o = 1 and Z = O = 2 off the diagonal.

Layer update (closed upper recurrence of kahale-weighted-union.md /
PairUnionRecurrence.lean, applied to a whole layer of disjoint comparators).
On the zero side a min output is OR(a, b) ("zero if either input is zero") and
a max output is AND(a, b); on the one side the roles swap.  With p(x) the
partner of x (p(x) = x for an idle wire, treated as OR(x, x)):
    OR  x, OR  y : min_{u in {x,px}, v in {y,py}} Z[u,v]                (exact)
    AND x, OR  y : min_{v in {y,py}} T(x,px,v),
                   T(a,b,v) = min(Z[a,b]+z[v], Z[a,v]+z[b], Z[b,v]+z[a])
    AND x, AND y : min(Z[x,px]+Z[y,py], Z[x,y]+Z[px,py], Z[x,py]+Z[px,y])
    gate's own pair (x, px): Z[x,px] (both zero <=> the AND output zero)
    diagonal: z'[OR] = min(z[x], z[px]),  z'[AND] = Z[x,px]
then cap at n, impose Z[x,y] <= z[x]+z[y] (union of two certificates) and
tighten z[x] <= min_y Z[x,y].  Every rule is a certificate union / family
identity, so all entries stay valid upper bounds for any real network that
uses the schedule.  (The 'AND, AND' pairings dominate the sequential
pair-plus-single covers given Z <= z + z.)

Necessary conditions at time t, s = d - t stages remaining (sized forms of
LB-02's (G); rank window lo_i >= i - 2^s, hi_i <= i + 2^s):
    (GZ) z[i] >= i - 2^s + 1          (GO) o[i] >= n - i - 2^s
    and at s = 0 the exact thresholds z[i] >= i + 1, o[i] >= n - i
    (sorts_iff_certificate_card_bounds).
Pair requirements add nothing: the minimum zero certificate of {x, y} is at
least max(z_x, z_y), and at the end (s = 0) "no disjoint (zero cert of j, one
cert of i), i < j" is equivalent to the per-wire thresholds
(sorts_iff_certificates_intersect <-> sorts_iff_certificate_card_bounds).  So
the pair matrix can only help by making the *upper* bounds z, o smaller
(overlap of certificates), which is what this script measures.

Schedules (all satisfy the active width bound W by construction):
    kahale : LB-02 skip-wide block halving on Kahale heights (the barrier
             schedule).  Block of m equal heights pairs (b+k, b+ceil(m/2)+k).
Models evaluated on the same schedule:
    heights : LB-02 per-wire heights, Kahale's (G) height form (baseline)
    wire    : per-wire sizes, z'[AND] = min(n, z_a + z_b)
    pair    : the pair matrix above
Modes
    run   d [d ...] [--scale c]       one schedule run per depth, all models
    scan  d [d ...]                   largest feasible n per model (grid search)
    truth d [d ...] --samples k        run the actual network on random
                                      permutations (witnessed rank-window defects)
    validate n [n ...] --depth d      soundness test against exact certificates
    exact n [n ...] --depth d         exhaustive search over all width-legal
                                      layer schedules of the *pair relaxation*
                                      on n wires (exact optimum, tiny n only)
Exact integer arithmetic throughout; finite checks of a relaxation only.
"""

import argparse
import itertools
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


# ------------------------------------------------------------- the schedule
def kahale_layers(d, n, extra=0):
    """LB-02 skip-wide block-halving schedule (from kahale_two_sided_heights
    pos_run).  Yields, per stage, arrays (lo, hi) of comparator endpoints."""
    z = np.zeros(n, dtype=np.int16)
    idx = np.arange(n, dtype=np.int64)
    for t in range(d):
        starts = np.flatnonzero(np.r_[True, z[1:] != z[:-1]])
        sizes = np.diff(np.r_[starts, n])
        bstart = np.repeat(starts, sizes)
        bsize = np.repeat(sizes, sizes)
        k = idx - bstart
        u = (bsize + 1) // 2
        lo_mask = k < bsize // 2
        later = d - t - 1 + extra
        wmax = (1 << (later + 1)) - 1 if later < 62 else 1 << 62
        lo_mask &= ~(u > wmax)
        lo = idx[lo_mask]
        hi = lo + u[lo_mask]
        zl, zh = z[lo], z[hi]
        z[lo], z[hi] = np.minimum(zl, zh), np.maximum(zl, zh) + 1
        yield lo, hi


def schedule(d, n, cleanup=0):
    """d stages of the skip-wide Kahale schedule (widths legal for a total
    depth d + cleanup), then `cleanup` odd-even transposition layers
    (width-1 comparators (i, i+1), alternating parity)."""
    yield from kahale_layers(d, n, cleanup)
    for c in range(cleanup):
        lo = np.arange(c % 2, n - 1, 2)
        yield lo, lo + 1


# ------------------------------------------------------------ requirements
def margins(t, d, n, zs, os_):
    """Minimum slack of (GZ) and (GO) at time t (negative = violated)."""
    s = d - t
    w = 1 << s if s < 62 else 1 << 62
    i = np.arange(n, dtype=np.int64)
    if s == 0:                       # exact terminal thresholds
        needz, needo = i + 1, n - i
    else:
        needz, needo = i - w + 1, n - i - w
    mz = int(np.min(zs.astype(np.int64) - needz))
    mo = int(np.min(os_.astype(np.int64) - needo))
    return mz, mo


def heights_margins(t, d, n, zh, oh):
    """LB-02 (G) height form: z >= h+1 when i >= 2^h + 2^s (and dual)."""
    s = d - t
    i = np.arange(n, dtype=np.int64)
    ok = True
    for h in range(0, max(1, int(math.log2(n))) + 2):
        bad_z = (i >= (1 << h) + (1 << s)) & (zh < h + 1)
        bad_o = (i < n - (1 << h) - (1 << s)) & (oh < h + 1)
        if bad_z.any() or bad_o.any():
            ok = False
            break
    return ok


# ------------------------------------------------------------------ models
def step_wire(z, o, lo, hi, n):
    zl, zh, ol, oh = z[lo].copy(), z[hi].copy(), o[lo].copy(), o[hi].copy()
    z[lo] = np.minimum(zl, zh)
    z[hi] = np.minimum(n, zl + zh)
    o[hi] = np.minimum(ol, oh)
    o[lo] = np.minimum(n, ol + oh)


def step_heights(z, o, lo, hi):
    zl, zh, ol, oh = z[lo].copy(), z[hi].copy(), o[lo].copy(), o[hi].copy()
    z[lo], z[hi] = np.minimum(zl, zh), np.maximum(zl, zh) + 1
    o[lo], o[hi] = np.maximum(ol, oh) + 1, np.minimum(ol, oh)


def step_pair_side(M, lo, hi, n, and_at):
    """One layer on one side.  M: n x n int32 matrix with the diagonal holding
    single costs.  and_at: array of the wires whose output is AND on this side
    (hi for the zero side, lo for the one side)."""
    p = np.arange(n)
    p[lo], p[hi] = hi, lo
    is_and = np.zeros(n, dtype=bool)
    is_and[and_at] = True
    d = np.diag(M).copy()                      # singles
    dp = d[p]
    pair = M[np.arange(n), p].copy()           # M[x, px]  (= d[x] if idle)
    Mr = M[p, :]                               # M[px, y]
    Mc = M[:, p]                               # M[x, py]
    Mb = Mr[:, p]                              # M[px, py]
    OR = np.minimum(np.minimum(M, Mr), np.minimum(Mc, Mb))
    new = OR
    # AND x (rows), OR y:  min over v in {y, py} of T(x, px, v)
    A = is_and
    if A.any():
        T1 = np.minimum(pair[:, None] + d[None, :],
                        np.minimum(M + dp[:, None], Mr + d[:, None]))
        T2 = np.minimum(pair[:, None] + dp[None, :],
                        np.minimum(Mc + dp[:, None], Mb + d[:, None]))
        T = np.minimum(T1, T2)
        del T1, T2
        AA = np.minimum(pair[:, None] + pair[None, :],
                        np.minimum(M + Mb, Mc + Mr))
        rowA = A[:, None] & ~A[None, :]
        colA = ~A[:, None] & A[None, :]
        both = A[:, None] & A[None, :]
        new = np.where(rowA, T, new)
        new = np.where(colA, T.T, new)
        new = np.where(both, AA, new)
        del T, AA
    # gate's own pair, and diagonal
    x = np.arange(n)
    act = p != x
    new[x[act], p[act]] = pair[act]
    dnew = np.where(is_and, pair, np.minimum(d, dp))
    new[x, x] = dnew
    np.minimum(new, n, out=new)
    np.minimum(new, dnew[:, None] + dnew[None, :], out=new)
    new[x, x] = dnew
    # tighten singles by row minima (true single <= true pair cost)
    rowmin = new.min(axis=1)
    new[x, x] = np.minimum(dnew, rowmin)
    return new.astype(np.int32, copy=False)


def step_pair_side_chunked(M, lo, hi, n, and_at, rows=512):
    """Same update as step_pair_side, computed in row blocks with int32
    arithmetic and stored in M's dtype (int16 storage is exact for n <= 32767; sums are formed in int32)."""
    p = np.arange(n)
    p[lo], p[hi] = hi, lo
    A = np.zeros(n, dtype=bool)
    A[and_at] = True
    d = np.diag(M).astype(np.int32)
    dp = d[p]
    pair = M[np.arange(n), p].astype(np.int32)
    dnew = np.where(A, pair, np.minimum(d, dp))
    Mp = M[:, p]                                   # M[x, py], whole matrix once
    new = np.empty_like(M)
    for r0 in range(0, n, rows):
        r = np.arange(r0, min(n, r0 + rows))
        pr = p[r]
        Mx = M[r].astype(np.int32)                 # M[x, y]
        Mr = M[pr].astype(np.int32)                # M[px, y]
        Mc = Mp[r].astype(np.int32)                # M[x, py]
        Mb = Mp[pr].astype(np.int32)               # M[px, py]
        out = np.minimum(np.minimum(Mx, Mr), np.minimum(Mc, Mb))
        Ar = A[r]
        if A.any():
            T = np.minimum(np.minimum(pair[r][:, None] + d[None, :],
                                      np.minimum(Mx + dp[r][:, None], Mr + d[r][:, None])),
                           np.minimum(pair[r][:, None] + dp[None, :],
                                      np.minimum(Mc + dp[r][:, None], Mb + d[r][:, None])))
            AA = np.minimum(pair[r][:, None] + pair[None, :], np.minimum(Mx + Mb, Mc + Mr))
            # AND row, OR column: T ; AND row, AND column: AA
            sel = Ar[:, None] & ~A[None, :]
            out[sel] = T[sel]
            sel = Ar[:, None] & A[None, :]
            out[sel] = AA[sel]
            # OR row, AND column: T^T, i.e. T(y, py, v) for v in {x, px}
            cols = np.flatnonzero(A)
            if cols.size:
                pc = p[cols]
                Tt = np.minimum(
                    np.minimum(pair[cols][None, :] + d[r][:, None],
                               np.minimum(Mx[:, cols] + dp[cols][None, :], Mc[:, cols] + d[cols][None, :])),
                    np.minimum(pair[cols][None, :] + dp[r][:, None],
                               np.minimum(Mr[:, cols] + dp[cols][None, :], Mb[:, cols] + d[cols][None, :])))
                orrows = ~Ar
                sub = out[:, cols]
                sub[orrows] = Tt[orrows]
                out[:, cols] = sub
        act = pr != r
        out[np.flatnonzero(act), pr[act]] = pair[r][act]
        np.minimum(out, n, out=out)
        np.minimum(out, dnew[r][:, None] + dnew[None, :], out=out)
        out[np.arange(r.size), r] = dnew[r]
        rowmin = out.min(axis=1)
        out[np.arange(r.size), r] = np.minimum(dnew[r], rowmin)
        new[r] = out.astype(M.dtype)
    return new



def run(d0, n, models=("heights", "wire", "pair"), stats=False, cleanup=0):
    d = d0 + cleanup                      # total depth
    res = {"depth": d, "main_depth": d0, "cleanup": cleanup, "n": n}
    st = {}
    if "heights" in models:
        st["heights"] = [np.zeros(n, np.int64), np.zeros(n, np.int64), True]
    if "wire" in models:
        st["wire"] = [np.ones(n, np.int64), np.ones(n, np.int64), None, None, None, math.inf]
    if "pair" in models:
        Z = np.full((n, n), 2, np.int16 if n <= 32767 else np.int32)
        np.fill_diagonal(Z, 1)
        st["pair"] = [Z, Z.copy(), None, None, None, math.inf]
    track = []

    def check(t):
        if "heights" in st:
            S = st["heights"]
            S[2] &= heights_margins(t, d, n, S[0], S[1])
        for m in ("wire", "pair"):
            if m in st:
                S = st[m]
                if m == "pair":
                    zs, os_ = np.diag(S[0]).astype(np.int64), np.diag(S[1]).astype(np.int64)
                else:
                    zs, os_ = S[0], S[1]
                mz, mo = margins(t, d, n, zs, os_)
                if t < d:                      # interior (s >= 1)
                    S[2] = mz if S[2] is None else min(S[2], mz)
                    S[3] = mo if S[3] is None else min(S[3], mo)
                    # tightest ratio size / requirement over wires with need >= 2
                    i = np.arange(n)
                    w = 1 << min(d - t, 62)
                    nz, no = i - w + 1, n - i - w
                    r = math.inf
                    if (nz >= 2).any():
                        r = min(r, float((zs[nz >= 2] / nz[nz >= 2]).min()))
                    if (no >= 2).any():
                        r = min(r, float((os_[no >= 2] / no[no >= 2]).min()))
                    S[5] = min(S[5], r)
                else:
                    S[4] = min(mz, mo)
        if stats and "pair" in st and "wire" in st:
            zp = np.diag(st["pair"][0]).astype(np.int64)
            gap = st["wire"][0] - zp
            track.append({"t": t, "wires_with_overlap_saving": int((gap > 0).sum()),
                          "max_saving": int(gap.max()),
                          "sum_saving_over_sum_wire": float(gap.sum() / st["wire"][0].sum())})

    check(0)
    for t, (lo, hi) in enumerate(schedule(d0, n, cleanup), start=1):
        if "heights" in st:
            step_heights(st["heights"][0], st["heights"][1], lo, hi)
        if "wire" in st:
            step_wire(st["wire"][0], st["wire"][1], lo, hi, n)
        if "pair" in st:
            S = st["pair"]
            S[0] = step_pair_side_chunked(S[0], lo, hi, n, hi)
            S[1] = step_pair_side_chunked(S[1], lo, hi, n, lo)
        check(t)
    if "heights" in st:
        res["heights_ok"] = bool(st["heights"][2])
    for m in ("wire", "pair"):
        if m in st:
            res[m + "_interior_min_margin"] = min(st[m][2], st[m][3])
            res[m + "_interior_min_ratio"] = st[m][5]
            res[m + "_terminal_margin"] = st[m][4]
            res[m + "_interior_ok"] = min(st[m][2], st[m][3]) >= 0
            res[m + "_ok"] = res[m + "_interior_ok"] and st[m][4] >= 0
    if stats:
        res["overlap_track"] = track
    return res


def scan(d, models, nmax, cleanup=0, nmin=2):
    """Largest grid n (geometric grid, ratio 2^(1/8)) passing each model."""
    out = {"main_depth": d, "cleanup": cleanup, "N_d": arity(d)}
    grid = sorted({max(2, int(round(2 ** (k / 8)))) for k in range(8, 8 * int(math.log2(nmax)) + 9)})
    grid = [g for g in grid if nmin <= g <= nmax]
    for m, key in [(m, k) for m in models for k in (("_ok",) if m == "heights" else ("_interior_ok", "_ok"))]:
        best = None
        fails_after = 0
        for g in grid:
            r = run(d, g, models=(m,), cleanup=cleanup)
            if r[m + key]:
                best = g
                fails_after = 0
            else:
                fails_after += 1
                if best is not None and fails_after >= 6:
                    break
        out["max_n_" + m + key] = best
    print(json.dumps(out), flush=True)
    return out


# ------------------------------------------------- exact relaxation optimum
def exact_depth(n, dmax):
    """Exact minimum depth of the *pair relaxation* on n wires: BFS over all
    layer schedules (matchings with i<j, min at i), states = (Z, O) matrices,
    pruned by the sized (GZ)/(GO) requirements with s stages left and the
    active-width bound.  Returns the least d for which some schedule meets all
    requirements, also for the per-wire sized relaxation."""
    pairs = list(itertools.combinations(range(n), 2))

    def matchings(avail):
        if not avail:
            yield []
            return
        a = avail[0]
        rest = avail[1:]
        yield from matchings(rest)
        for k, b in enumerate(rest):
            for m in matchings(rest[:k] + rest[k + 1:]):
                yield [(a, b)] + m

    layers = [m for m in matchings(list(range(n))) if m]

    def ok(zs, os_, s):
        w = 1 << s
        if s == 0:
            return all(zs[i] >= i + 1 and os_[i] >= n - i for i in range(n))
        return all(zs[i] >= i - w + 1 and os_[i] >= n - i - w for i in range(n))

    out = {}
    for model in ("wire", "pair"):
        found = None
        for d in range(1, dmax + 1):
            if model == "pair":
                Z = np.full((n, n), 2, np.int32)
                np.fill_diagonal(Z, 1)
                start = (Z.tobytes(), Z.tobytes())
            else:
                start = ((1,) * n, (1,) * n)
            frontier = {start}
            for t in range(1, d + 1):
                s_after = d - t
                nxt = set()
                for state in frontier:
                    for L in layers:
                        if any(j - i > (1 << (s_after + 1)) - 1 for i, j in L):
                            continue
                        lo = np.array([i for i, _ in L])
                        hi = np.array([j for _, j in L])
                        if model == "pair":
                            Z = np.frombuffer(state[0], np.int32).reshape(n, n).copy()
                            O = np.frombuffer(state[1], np.int32).reshape(n, n).copy()
                            Z2 = step_pair_side(Z, lo, hi, n, hi)
                            O2 = step_pair_side(O, lo, hi, n, lo)
                            zs, os_ = list(np.diag(Z2)), list(np.diag(O2))
                            key = (Z2.tobytes(), O2.tobytes())
                        else:
                            zs, os_ = np.array(state[0]), np.array(state[1])
                            step_wire(zs, os_, lo, hi, n)
                            zs, os_ = list(zs), list(os_)
                            key = (tuple(zs), tuple(os_))
                        if ok(zs, os_, s_after):
                            nxt.add(key)
                frontier = nxt
                if not frontier:
                    break
            if frontier:
                found = d
                break
        out[model] = found
    return out


# ------------------------------------------------------------- validation
def validate(n, trials, depth, seed=1):
    """Random layered networks on n <= 12 wires: every pair-matrix entry must
    upper-bound the exact minimum certificate size (computed from all 2^n
    inputs), and the pair diagonal must never exceed the per-wire sizes."""
    rng = np.random.default_rng(seed)
    V = ((np.arange(1 << n)[:, None] >> np.arange(n)[None, :]) & 1).astype(np.int8)
    zeros = (1 - V).sum(1)
    worst_gain = 0
    tight = total = 0
    for _ in range(trials):
        W = V.copy()
        Z = np.full((n, n), 2, np.int32); np.fill_diagonal(Z, 1); O = Z.copy()
        zw = np.ones(n, np.int64); ow = np.ones(n, np.int64)
        for _t in range(depth):
            perm = rng.permutation(n)
            k = rng.integers(1, n // 2 + 1)
            L = [tuple(sorted(perm[2 * r:2 * r + 2])) for r in range(k)]
            lo = np.array([a for a, _ in L]); hi = np.array([b for _, b in L])
            a, b = W[:, lo].copy(), W[:, hi].copy()
            W[:, lo], W[:, hi] = np.minimum(a, b), np.maximum(a, b)
            Z = step_pair_side(Z, lo, hi, n, hi)
            O = step_pair_side(O, lo, hi, n, lo)
            step_wire(zw, ow, lo, hi, n)
            for x in range(n):
                for y in range(n):
                    both0 = (W[:, x] == 0) & (W[:, y] == 0)
                    both1 = (W[:, x] == 1) & (W[:, y] == 1)
                    ez = zeros[both0].min(); eo = (n - zeros[both1]).max() if False else (n - zeros)[both1].min()
                    assert Z[x, y] >= ez, (x, y, Z[x, y], ez)
                    assert O[x, y] >= eo, (x, y, O[x, y], eo)
                    total += 2; tight += (Z[x, y] == ez) + (O[x, y] == eo)
            assert (np.diag(Z) <= zw).all() and (np.diag(O) <= ow).all()
            worst_gain = max(worst_gain, int((zw - np.diag(Z)).max()))
    return {"n": n, "trials": trials, "depth": depth, "all_upper_bounds_valid": True,
            "fraction_entries_exact": tight / total, "max_single_gain_over_wire": worst_gain}


# --------------------------------------------- the actual network (sampled)
def truth_probe(d0, n, samples, cleanup=2, seed=7, batch=256):
    """Run the actual comparator network of the schedule on random
    permutations.  Observed min / max rank at wire i after t stages are upper
    / lower bounds on the true lo_i / hi_i, hence z_true <= minrank + 1 and
    o_true <= n - maxrank.  Reports, per remaining depth s, the largest
    witnessed violation of the rank window lo_i >= i - 2^s, hi_i <= i + 2^s
    (a witnessed violation proves the network fails the necessary condition,
    which the pair relaxation certified as satisfied)."""
    rng = np.random.default_rng(seed)
    layers = list(schedule(d0, n, cleanup))
    d = len(layers)
    mn = np.full((d + 1, n), n, np.int64)
    mx = np.full((d + 1, n), -1, np.int64)
    done = 0
    while done < samples:
        b = min(batch, samples - done)
        X = np.argsort(rng.random((b, n)), axis=1).astype(np.int32)   # ranks
        mn[0] = np.minimum(mn[0], X.min(0)); mx[0] = np.maximum(mx[0], X.max(0))
        for t, (lo, hi) in enumerate(layers, start=1):
            a, c = X[:, lo], X[:, hi]
            X[:, lo], X[:, hi] = np.minimum(a, c), np.maximum(a, c)
            mn[t] = np.minimum(mn[t], X.min(0)); mx[t] = np.maximum(mx[t], X.max(0))
        done += b
    i = np.arange(n)
    rows = []
    for t in range(d + 1):
        s = d - t
        w = 0 if s == 0 else (1 << s if s < 62 else 1 << 62)
        viol = max(int(((i - w) - mn[t]).max()), int((mx[t] - (i + w)).max()))
        rows.append({"t": t, "s": s, "max_window_violation": viol})
    first = next((r for r in rows if r["max_window_violation"] > 0), None)
    jz = int(np.argmax(i - mn[d])); jo = int(np.argmax(mx[d] - i))
    return {"main_depth": d0, "cleanup": cleanup, "n": n, "samples": samples,
            "first_witnessed_violation": first,
            "terminal_violation": rows[-1]["max_window_violation"],
            "worst_zero_wire": jz, "its_min_rank": int(mn[d][jz]),
            "worst_one_wire": jo, "its_max_rank": int(mx[d][jo]),
            "by_s": {r["s"]: r["max_window_violation"] for r in rows if r["s"] <= 12}}


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("mode", choices=["run", "scan", "exact", "validate", "truth"])
    p.add_argument("vals", type=int, nargs="+")
    p.add_argument("--scale", type=float, default=1.0)
    p.add_argument("--models", default="heights,wire,pair")
    p.add_argument("--nmax", type=int, default=4096)
    p.add_argument("--nmin", type=int, default=2,
                   help="scan: smallest grid value (assumed feasible region starts above)")
    p.add_argument("--depth", type=int, default=12, help="exact: max depth")
    p.add_argument("--stats", action="store_true")
    p.add_argument("--samples", type=int, default=4096, help="truth: random permutations")
    p.add_argument("--cleanup", type=int, default=0,
                   help="append this many odd-even transposition layers")
    a = p.parse_args()
    models = tuple(a.models.split(","))
    if a.mode == "run":
        for d in a.vals:
            n = max(2, int(arity(d) * a.scale))
            r = run(d, n, models, stats=a.stats, cleanup=a.cleanup)
            r.update({"scale": a.scale, "d_over_log2_n": d / math.log2(n)})
            print(json.dumps(r), flush=True)
    elif a.mode == "scan":
        for d in a.vals:
            scan(d, models, a.nmax, a.cleanup, a.nmin)
    elif a.mode == "truth":
        for d in a.vals:
            n = max(2, int(arity(d) * a.scale))
            print(json.dumps(truth_probe(d, n, a.samples, a.cleanup)), flush=True)
    elif a.mode == "validate":
        for n in a.vals:
            print(json.dumps(validate(n, 30, a.depth)), flush=True)
    else:
        for n in a.vals:
            print(json.dumps({"n": n, "exact_min_depth": exact_depth(n, a.depth)}), flush=True)


if __name__ == "__main__":
    main()
