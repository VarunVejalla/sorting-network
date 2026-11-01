#!/usr/bin/env python3
"""LB-34: worst-case 0-1 inputs of the LB-35 `tr` hybrid.

Exact identity used throughout (proved in docs/kahale-worst-case-inputs.md):
    worst rank error of a network = max_w max(w + 1 - z_w, n - w - o_w),
with z_w, o_w the true minimum zero / one certificate sizes of output wire w.
So a search for breaking inputs is a search for small certificates.  Every
witness reported here is re-simulated on the integer network before printing.
Finite search: witnesses are lower bounds on the worst error unless marked exact.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kahale_amplification_kill import build  # noqa: E402
from kahale_pair_union_rate import arity, step_wire  # noqa: E402

KS = {24: 12, 28: 14, 32: 16, 36: 18, 40: 20, 44: 22, 48: 20, 52: 22, 56: 28, 60: 30,
      64: 32, 72: 36, 80: 36}
CACHE = os.environ.get("LB34_CACHE", "")


def tr_layers(d, n=None, K=None):
    """The LB-35 network: `tr` on all wires, depth d + 2, same design seed."""
    n = n or arity(d)
    K = KS[d] if K is None else K
    if CACHE:
        p = os.path.join(CACHE, f"tr_{d}_{n}_{K}.npz")
        if os.path.exists(p):
            f = np.load(p)
            return [(f[f"l{t}"], f[f"h{t}"]) for t in range(d + 2)], n
    L = build(d, n, "tr", 0, "oet", K, 1.0)
    if CACHE:
        os.makedirs(CACHE, exist_ok=True)
        np.savez(p, **{f"l{t}": a for t, (a, _) in enumerate(L)},
                 **{f"h{t}": b for t, (_, b) in enumerate(L)})
    return L, n


def tail_schedule(d, n, K, rule="tr", M=64, seed=5, wide_every=2, extra=None):
    """Barrier prefix (d - K stages), then a tail chosen on the design sample.
    rule 'tr' reproduces LB-35's network exactly (asserted by the caller).
    rule 'tw': on every wide_every-th tail stage, instead of consecutive pairs,
    compare positions p, p + delta of the mean-rank order inside blocks of
    2 delta; delta runs n/4, n/8, ..., 1 and repeats.  Depth is unchanged."""
    from kahale_pair_union_rate import kahale_layers
    from kahale_amplification_kill import wmax_after
    base = list(kahale_layers(d, n, 2))[:d - K]
    half = max(1, int(round(n / 2)))              # LB-35 band; misses the top wire if n is odd
    band0, band1 = max(0, n // 2 - half), min(n, n // 2 + half)
    Xd = np.argsort(np.random.default_rng(seed).random((M, n)), axis=1).astype(np.int32)
    if extra is not None:
        Xd = np.concatenate([Xd, extra], axis=0)
    L = []
    for lo, hi in base:
        L.append((lo, hi))
        u, v = Xd[:, lo], Xd[:, hi]
        Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
    top = max(1, int(math.log2(max(2, n))) - 2)
    w = 0
    for t in range(d - K, d):
        wmax = wmax_after(d - t - 1 + 2)
        g = band0 + np.argsort(Xd[:, band0:band1].mean(0), kind="stable")
        if rule == "tw" and (t - (d - K)) % wide_every == 0:
            delta = 1 << (top - (w % (top + 1)))
            w += 1
            r = np.arange(g.size)
            first = r[(r // delta) % 2 == 0]
            first = first[first + delta < g.size]
            a0, b0 = g[first], g[first + delta]
        else:
            h = g[(t % 2):]
            m = min(h[0:-1:2].size, h[1::2].size)
            a0, b0 = h[0:-1:2][:m], h[1::2][:m]
        a, b = np.minimum(a0, b0), np.maximum(a0, b0)
        ok = (b - a) <= wmax
        lo, hi = a[ok].astype(np.int64), b[ok].astype(np.int64)
        L.append((lo, hi))
        u, v = Xd[:, lo], Xd[:, hi]
        Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
    for c in range(2):
        lo = np.arange(c % 2, n - 1, 2)
        L.append((lo, lo + 1))
    return L


def sim(L, W):
    """0-1 simulation, in place, on arrays indexed by wire first (any dtype
    supporting & and |; a packed uint64 array gives bit parallelism)."""
    for lo, hi in L:
        a, b = W[lo], W[hi]
        W[lo], W[hi] = a & b, a | b
    return W


def sim_perm(L, X):
    for lo, hi in L:
        a, b = X[lo], X[hi]
        X[lo], X[hi] = np.minimum(a, b), np.maximum(a, b)
    return X


def errors(out):
    """out: 0-1 output (n,) or (n, b).  Returns zeros k, misplacement m (ones in
    the first k positions), rank error E = max(k - first one, last zero - k + 1)."""
    o = out.astype(bool)
    if o.ndim == 1:
        o = o[:, None]
    n, b = o.shape
    k = n - o.sum(0)
    c = np.cumsum(o, axis=0)
    m = np.where(k > 0, c[np.maximum(k - 1, 0), np.arange(b)], 0)
    first = np.where(o.any(0), o.argmax(0), n)
    last = np.where((~o).any(0), n - 1 - (~o)[::-1].argmax(0), -1)
    E = np.maximum(np.maximum(k - first, last - k + 1), 0)
    return k, m, E


def forward_cost(L, n, price, side, alpha, block=None):
    """Tree cost of forcing each wire to `side` (0 or 1) by inputs with the given
    prices; OR = min, AND = max + alpha min.  `block` marks wires that may not
    be used (value differs from side under a reference input)."""
    c = price.astype(np.float64).copy()
    H = []
    for t, (lo, hi) in enumerate(L):
        H.append(c.copy())
        a, b = c[lo], c[hi]
        mn, mx = np.minimum(a, b), np.maximum(a, b)
        fin = np.minimum(mx, 1e15)
        if side == 0:                      # lo = OR of zeros, hi = AND of zeros
            c[lo], c[hi] = mn, fin + alpha * mn
        else:
            c[hi], c[lo] = mn, fin + alpha * mn
    return c, H


def extract(L, n, H, target, side, rng, greedy=True):
    """Backward proof tree for `target` = side; returns input set (bool)."""
    need = np.zeros(n, bool)
    need[target] = True
    for t in range(len(L) - 1, -1, -1):
        lo, hi = L[t]
        c = H[t]
        andw, orw = (hi, lo) if side == 0 else (lo, hi)
        na, no = need[andw], need[orw]
        ca, cb = c[lo], c[hi]
        pick_lo = (ca < cb) | ((ca == cb) & rng.integers(0, 2, lo.size).astype(bool))
        both = na
        one = no & ~na
        need[lo] = both | (one & pick_lo)
        need[hi] = both | (one & ~pick_lo)
    return need


def refine(L, n, target, side, rng, S=None, iters=200, alpha=1.0, disc=0.02, drop=0.05):
    """Iterated proof-tree search for a small certificate of target = side.
    Prices: 1 off the current set, disc on it, with light noise; a certificate is
    always valid by construction (checked by the caller with sim)."""
    best = None
    cur = S
    for it in range(iters):
        p = 1.0 + 0.3 * rng.random(n)
        if cur is not None:
            keep = cur & (rng.random(n) >= drop)
            p[keep] = disc
        _, H = forward_cost(L, n, p, side, alpha)
        c = extract(L, n, H, target, side, rng)
        if cur is None or c.sum() <= cur.sum():
            cur = c
        if best is None or c.sum() < best.sum():
            best = c.copy()
    return best


def check_cert(L, n, S, target, side):
    """Simulate: S forced to side, all other inputs the opposite value."""
    x = (~S) if side == 0 else S
    out = sim(L, x.copy())
    assert bool(out[target]) == bool(side), "invalid certificate"
    return out


def err_of(w, s, n, side):
    return w + 1 - s if side == 0 else n - w - s


def cmd_certs(a):
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        L, n = tr_layers(d, a.n or None, a.K or None)
        wires = np.unique(np.linspace(0, n - 1, a.wires).round().astype(int))
        res, best = [], (-1, None)
        t0 = time.time()
        for w in wires:
            for side in (0, 1):
                S = refine(L, n, int(w), side, rng, iters=a.iters, alpha=a.alpha)
                check_cert(L, n, S, int(w), side)
                e = err_of(int(w), int(S.sum()), n, side)
                res.append((int(w), side, int(S.sum()), e))
                if e > best[0]:
                    best = (e, (int(w), side))
        print(json.dumps({"d": d, "n": n, "best_err": best[0], "err/n": round(best[0] / n, 4),
                          "at": best[1], "secs": round(time.time() - t0, 1), "rows": res}), flush=True)


def proof_tree(L, n, w, side, S):
    """Proof tree of target w inside certificate S.  Returns, per layer, the
    wires needed, the number of AND gates, sharing gates (both outputs needed)
    and the unfolded tree size (leaves with multiplicity, as float)."""
    p = np.where(S, 0.0, 1.0)
    _, H = forward_cost(L, n, p, side, 1.0)
    need = np.zeros(n, bool)
    need[w] = True
    mult = np.zeros(n)                       # tree multiplicity of each needed wire
    mult[w] = 1
    D = len(L)
    prof, ands, shared, sets = [0] * (D + 1), [0] * D, [0] * D, [None] * (D + 1)
    prof[D], sets[D] = 1, need.copy()
    for t in range(D - 1, -1, -1):
        lo, hi = L[t]
        c = H[t]
        andw, orw = (hi, lo) if side == 0 else (lo, hi)
        na, no = need[andw], need[orw]
        ands[t] = int(na.sum())
        shared[t] = int((na & no).sum())
        pl = c[lo] <= c[hi]
        ml, mh = mult[andw].copy(), mult[orw].copy()
        one = no & ~na
        l2, h2 = na | (one & pl), na | (one & ~pl)
        need[lo], need[hi] = l2, h2
        mult[lo] = ml + np.where(na, mh, np.where(pl, mh, 0.0))
        mult[hi] = ml + np.where(na, mh, np.where(~pl, mh, 0.0))
        prof[t], sets[t] = int(need.sum()), need.copy()
    return prof, ands, shared, float(mult.sum()), sets


def reach_low(L, n, frm):
    """Lowest output wire reachable from each wire of the network suffix L[frm:],
    and the highest (any path through comparators)."""
    lo_r, hi_r = np.arange(n), np.arange(n)
    for lo, hi in reversed(L[frm:]):
        m = np.minimum(lo_r[lo], lo_r[hi])
        x = np.maximum(hi_r[lo], hi_r[hi])
        lo_r[lo], lo_r[hi] = m, m
        hi_r[lo], hi_r[hi] = x, x
    return lo_r, hi_r


def reach_margins(L, n):
    """Reach-graded test, sizes form.  r_t(u) = lowest output wire reachable from
    wire u through L[t:].  If S is a zero certificate of u at time t then, on the
    input with zeros exactly S, a zero sits on u at time t and ends at a wire >=
    r_t(u), so a sorter has |S| >= r_t(u) + 1 (dually for ones).  Applied to the
    LB-24 upper bounds z, o this is a closed, sound, schedule-checkable condition.
    Returns the worst margin over t, u for both sides (negative = fails) and the
    time of the worst margin, plus the same test with the width-rule reach."""
    D = len(L)
    rl, rh = [None] * (D + 1), [None] * (D + 1)
    a, b = np.arange(n), np.arange(n)
    rl[D], rh[D] = a.copy(), b.copy()
    for t in range(D - 1, -1, -1):
        lo, hi = L[t]
        m = np.minimum(a[lo], a[hi])
        x = np.maximum(b[lo], b[hi])
        a[lo], a[hi], b[lo], b[hi] = m, m, x, x
        rl[t], rh[t] = a.copy(), b.copy()
    z, o = np.ones(n, np.int64), np.ones(n, np.int64)
    best = (10 ** 9, None)
    bys = {}
    for t, (lo, hi) in enumerate(L, 1):
        step_wire(z, o, lo, hi, n)
        mz = z - (rl[t] + 1)
        mo = o - (n - rh[t])
        m = int(min(mz.min(), mo.min()))
        bys[D - t] = m
        if m < best[0]:
            best = (m, D - t)
    r = {"reach_margin": best[0], "at_s": best[1],
         "median_reach_at_s": {s: int(np.median(np.arange(n) - rl[D - s]))
                               for s in (1, 2, 4, 8, 12, 16, 20, 24, 28, 32) if s <= D}}
    return r


def schedule_report(d, n, K, rule, wide_every, models="heights,wire", samples=64):
    from kahale_amplification_kill import check_relaxations
    L = tail_schedule(d, n, K, rule, wide_every=wide_every)
    r = {"d": d, "n": n, "K": K, "rule": rule, "wide_every": wide_every}
    rel = check_relaxations(L, n, tuple(models.split(",")))
    r.update({k: v for k, v in rel.items() if k.endswith("_ok")})
    r.update(reach_margins(L, n))
    rng = np.random.default_rng(11)
    X = np.argsort(rng.random((samples, n)), axis=1).astype(np.int32).T
    X = sim_perm(L, X)
    i = np.arange(n)
    mean, std = X.mean(1), X.std(1)
    rt = math.sqrt(n)
    r["sp"] = round(float(((np.abs(mean - i) <= rt) & (std <= rt / 2)).mean()), 4)
    r["exact"] = round(float((X == i[:, None]).all(0).mean()), 3)
    r["wrong_wires"] = round(float((X != i[:, None]).mean()), 4)
    return L, r


def cmd_repair(a):
    """Worst-error scan on tail variants, same barrier prefix, same depth."""
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        n = a.n or arity(d)
        K = a.K or KS[d]
        for rule, we in [("tr", 2)] + [("tw", int(x)) for x in a.wide.split(",") if x]:
            L, r = schedule_report(d, n, K, rule, we, a.models, a.samples)
            r.update(worst_scan(L, n, rng, a.iters, a.stride, a.top, a.budget))
            print(json.dumps(r), flush=True)


def worst_scan(L, n, rng, iters, stride, top, budget):
    t0 = time.time()
    errs, sets = {}, {}
    for w in np.arange(0, n, max(1, stride)):
        for side in (0, 1):
            S = refine(L, n, int(w), side, rng, iters=iters, alpha=float(rng.choice([0.5, 1.0, 1.0])))
            errs[(int(w), side)] = err_of(int(w), int(S.sum()), n, side)
            sets[(int(w), side)] = S
        if time.time() - t0 > budget * 0.6:
            break
    for w, side in sorted(errs, key=lambda q: -errs[q])[:top]:
        for al in (1.0, 0.7, 0.4):
            if time.time() - t0 > budget:
                break
            S = refine(L, n, w, side, rng, S=sets[(w, side)], iters=iters * 4, alpha=al)
            e = err_of(w, int(S.sum()), n, side)
            if e > errs[(w, side)]:
                errs[(w, side)], sets[(w, side)] = e, S
    q = max(errs, key=lambda x: errs[x])
    check_cert(L, n, sets[q], q[0], q[1])
    return {"worst_err": errs[q], "worst_err/n": round(errs[q] / n, 4), "worst_at": q,
            "frac_targets_err>0.01n": round(float(np.mean([e > 0.01 * n for e in errs.values()])), 4)}


def pack(X):
    """bool (n, b) -> uint64 (n, ceil(b/64)), little-endian bits."""
    n, b = X.shape
    w = (b + 63) // 64
    B = np.zeros((n, w * 64), np.uint8)
    B[:, :b] = X
    return np.frombuffer(np.packbits(B, axis=1, bitorder="little").tobytes(), np.uint64).reshape(n, w).copy()


def unpack(P, b):
    return np.unpackbits(P.view(np.uint8).reshape(P.shape[0], -1), axis=1, bitorder="little")[:, :b].astype(bool)


def cover(L, n, k, side, rng, alpha=1.0, frac=0.03, tries=12, rf=12):
    """Greedy multi-wire cover: a set of at most k (side 0) or n - k (side 1) inputs
    forcing as many wrong-side wires as possible (marginal proof-tree prices)."""
    budget = k if side == 0 else n - k
    targets = np.arange(k, n) if side == 0 else np.arange(0, k)
    S = np.zeros(n, bool)
    if targets.size == 0 or budget <= 0:
        return S
    while True:
        p = 1.0 + 1e-3 * rng.random(n)
        p[S] = 0.0
        c, H = forward_cost(L, n, p, side, alpha)
        val = c[targets]
        pos = val >= 0.5
        if not pos.any():
            return S
        order = targets[pos][np.argsort(val[pos])]
        left = budget - int(S.sum())
        take = order[:max(1, int(frac * order.size))]
        need = np.zeros(n, bool)
        need[take] = True
        for t in range(len(L) - 1, -1, -1):
            lo, hi = L[t]
            q = H[t]
            andw, orw = (hi, lo) if side == 0 else (lo, hi)
            na, no = need[andw], need[orw]
            pl = q[lo] < q[hi]
            need[lo] = na | (no & ~na & pl)
            need[hi] = na | (no & ~na & ~pl)
        new = int((need & ~S).sum())
        if new == 0:
            return S
        if new > left:
            if take.size > 1:
                frac = max(frac / 3, 1.0 / order.size)
                continue
            for w in order[:tries]:              # proof-tree search with overlap discount
                R = refine(L, n, int(w), side, rng, S=S if S.any() else None, iters=rf, alpha=1.0)
                if int((R & ~S).sum()) <= left and (R & ~S).any():
                    S |= R
                    break
            else:
                return S
            continue
        S |= need


def es_thresh(L, n, k, x0, rng, steps, B, tlimit):
    """(1 + B) hill climb on inputs with exactly k zeros (True = one), objective
    (misplacement, rank error), moves 1-3 random swaps."""
    x = x0.copy()
    _, m, E = errors(sim(L, x.copy()))
    best = (int(m[0]), int(E[0]))
    bestE = int(E[0])
    t0 = time.time()
    for st in range(steps):
        if time.time() - t0 > tlimit:
            break
        zeros, ones = np.flatnonzero(~x), np.flatnonzero(x)
        if zeros.size == 0 or ones.size == 0:
            break
        X = np.repeat(x[:, None], B, axis=1)
        col = np.arange(1, B)
        for rep in range(1 + (st % 3)):
            mask = rng.random(B - 1) < 1.0 / (rep + 1)
            a = rng.choice(zeros, B - 1)
            b = rng.choice(ones, B - 1)
            X[a[mask], col[mask]] = True
            X[b[mask], col[mask]] = False
        Y = unpack(sim(L, pack(X)), B)
        _, m, E = errors(Y)
        score = m.astype(np.int64) * (n + 1) + E
        j = int(score.argmax())
        bestE = max(bestE, int(E.max()))
        if (int(m[j]), int(E[j])) >= best:
            best = (int(m[j]), int(E[j]))
            x = X[:, j].copy()
    return best, bestE, x


def cmd_thresh(a):
    """Per threshold k: the worst k-zero input found: misplacement m(x), rank
    error E, the random baseline, and the start that won."""
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        L, n = tr_layers(d)
        ks = np.unique(np.linspace(1, n - 1, a.grid).round().astype(int))
        rows = []
        for k in ks:
            k = int(k)
            t0 = time.time()
            base = []
            for _ in range(32):
                x = np.ones(n, bool)
                x[rng.choice(n, k, replace=False)] = False
                base.append(x)
            _, m0, E0 = errors(sim(L, np.array(base).T.copy()))
            starts = {"rand": base[0]}
            for side in (0, 1):
                S = cover(L, n, k, side, rng)
                if side == 0:
                    x = ~S
                    extra = k - int(S.sum())       # more zeros, off S
                    if extra > 0:
                        x[rng.choice(np.flatnonzero(x), extra, replace=False)] = False
                else:
                    x = S.copy()
                    extra = (n - k) - int(S.sum())  # more ones, off S
                    if extra > 0:
                        x[rng.choice(np.flatnonzero(~x), extra, replace=False)] = True
                assert int((~x).sum()) == k
                starts[f"cover{side}"] = x
            res = {}
            for nm, x in starts.items():
                _, m, E = errors(sim(L, x.copy()))
                res[nm] = (int(m[0]), int(E[0]))
            nm = max(res, key=lambda q: res[q])
            bm, bE, _ = es_thresh(L, n, k, starts[nm], rng, a.steps, a.batch, a.tlimit)
            bm2, bE2, _ = es_thresh(L, n, k, starts["rand"], rng, a.steps // 4, a.batch, a.tlimit / 4)
            rows.append({"k": k, "rand_m_mean": round(float(m0.mean()), 2), "rand_E_max": int(E0.max()),
                         "starts": res, "m": max(bm[0], bm2[0]), "E": max(bE, bE2),
                         "hc_from_rand": bm2, "secs": round(time.time() - t0, 1)})
            print(json.dumps({"d": d, "n": n, **rows[-1]}), flush=True)
        print(json.dumps({"d": d, "n": n, "summary": True,
                          "max_m": max(r["m"] for r in rows),
                          "max_m/n": round(max(r["m"] for r in rows) / n, 4),
                          "at_k": max(rows, key=lambda r: r["m"])["k"],
                          "max_E": max(r["E"] for r in rows),
                          "max_E/n": round(max(r["E"] for r in rows) / n, 4)}), flush=True)


def cmd_cegar(a):
    """Counterexample-guided repair of the tail.  Each round: scan the current
    network for witnesses and add them to a bank.  Rebuild: in each tail stage, for
    bank inputs (worst first), compare the wire of the first misplaced one with
    the wire of the last misplaced zero (disjoint, width legal); the wires left take
    the `tr` pairing.  Depth does not change."""
    from kahale_amplification_kill import wmax_after, check_relaxations
    from kahale_pair_union_rate import kahale_layers
    rng = np.random.default_rng(a.seed)
    d = a.depths[0]
    n = a.n or arity(d)
    K = a.K or KS[d]
    A = np.zeros((n, 0), bool)
    base = list(kahale_layers(d, n, 2))[:d - K]
    half = max(1, int(round(n / 2)))
    band0, band1 = max(0, n // 2 - half), min(n, n // 2 + half)
    for rnd in range(a.rounds):
        t0 = time.time()
        Xd = np.argsort(np.random.default_rng(5).random((64, n)), axis=1).astype(np.int32)
        Y = A.copy()
        kz = n - Y.sum(0)
        L = []
        wide = 0

        def app(lo, hi):
            L.append((lo, hi))
            u, v = Xd[:, lo], Xd[:, hi]
            Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
            p, q = Y[lo], Y[hi]
            Y[lo], Y[hi] = p & q, p | q
        for lo, hi in base:
            app(lo, hi)
        for t in range(d - K, d):
            wmax = wmax_after(d - t - 1 + 2)
            used = np.zeros(n, bool)
            lo2, hi2 = [], []
            if Y.shape[1]:
                _, m, E = errors(Y)
                for c in np.argsort(-E)[:a.fix]:
                    if E[c] <= 0:
                        break
                    y = Y[:, c]
                    k = int(kz[c])
                    ones = np.flatnonzero(y[:k] & ~used[:k])
                    zer = k + np.flatnonzero((~y[k:]) & ~used[k:])
                    if ones.size and zer.size:
                        i, j = int(ones[0]), int(zer[-1])
                        if j - i <= wmax:
                            used[i] = used[j] = True
                            lo2.append(i)
                            hi2.append(j)
            g = band0 + np.argsort(Xd[:, band0:band1].mean(0), kind="stable")
            g = g[~used[g]]
            h = g[(t % 2):]
            mm = min(h[0:-1:2].size, h[1::2].size)
            a0, b0 = h[0:-1:2][:mm], h[1::2][:mm]
            p, q = np.minimum(a0, b0), np.maximum(a0, b0)
            ok = (q - p) <= wmax
            app(np.r_[np.array(lo2, np.int64), p[ok]].astype(np.int64),
                np.r_[np.array(hi2, np.int64), q[ok]].astype(np.int64))
            wide += len(lo2)
        for c in range(2):
            lo = np.arange(c % 2, n - 1, 2)
            app(lo, lo + 1)
        rel = check_relaxations(L, n, ("heights", "wire"))
        X = np.argsort(np.random.default_rng(11).random((64, n)), axis=1).astype(np.int32).T
        X = sim_perm(L, X)
        i = np.arange(n)
        mean, std = X.mean(1), X.std(1)
        rt = math.sqrt(n)
        errs, sets = {}, {}
        if a.adv == "tree":
            for side in (0, 1):
                Sz, _ = tree_family(L, n, side)
                cnt = np.bitwise_count(Sz).sum(1).astype(np.int64)
                for w in range(n):
                    errs[(w, side)] = err_of(w, int(cnt[w]), n, side)
                    if errs[(w, side)] > 0:
                        sets[(w, side)] = bits_to_mask(Sz[w], n)
        else:
            for w in np.arange(0, n, a.stride):
                for side in (0, 1):
                    S = refine(L, n, int(w), side, rng, iters=a.iters, alpha=float(rng.choice([0.5, 1.0, 1.0])))
                    errs[(int(w), side)] = err_of(int(w), int(S.sum()), n, side)
                    sets[(int(w), side)] = S
        top = sorted(errs, key=lambda q: -errs[q])[:a.add]
        new = [(~sets[q]) if q[1] == 0 else sets[q].copy() for q in top if errs[q] > 0]
        worst = max(errs.values())
        print(json.dumps({"d": d, "n": n, "K": K, "round": rnd, "bank": A.shape[1], "directed_comparators": wide,
                          "heights_ok": rel["heights_ok"], "wire_ok": rel["wire_ok"],
                          "sp": round(float(((np.abs(mean - i) <= rt) & (std <= rt / 2)).mean()), 4),
                          "exact": round(float((X == i[:, None]).all(0).mean()), 3),
                          "wrong_wires": round(float((X != i[:, None]).mean()), 4),
                          "worst_err": int(worst), "worst_err/n": round(worst / n, 4),
                          "frac_err>0.01n": round(float(np.mean([e > 0.01 * n for e in errs.values()])), 4),
                          "secs": round(time.time() - t0, 1)}), flush=True)
        if not new:
            if a.adv == "tree" and a.final:          # passed the tree test: stronger adversary
                w = worst_scan(L, n, rng, 30, a.stride, 30, a.final)
                print(json.dumps({"d": d, "n": n, "tree_passed_at_round": rnd, "search_err": w["worst_err"],
                                  "search_err/n": w["worst_err/n"]}), flush=True)
            break
        A = np.concatenate([A, np.array(new).T], axis=1)


def milp_cert(L, n, w, side, tlimit, ub=None):
    """Exact minimum certificate of wire w = side as a MILP.  x_i binary, 1 if input i
    is forced to `side`.  Wire variables y in [0, 1]: y = 1 only if the wire is
    forced.  AND output: y <= each input.  OR output: y <= sum of inputs.  With x
    integral every feasible y is <= the true forced value, so y_w = 1 iff x is a
    certificate.  Returns (status, best size, proved lower bound).  Only the cone of
    the target is encoded."""
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import coo_matrix
    D = len(L)
    need = np.zeros(n, bool)
    need[w] = True
    cone = [None] * (D + 1)
    cone[D] = need.copy()
    for t in range(D - 1, -1, -1):
        lo, hi = L[t]
        act = need[lo] | need[hi]
        need[lo] = need[lo] | act
        need[hi] = need[hi] | act
        cone[t] = need.copy()
    var = {}
    nv = 0
    cur = {}
    for i in np.flatnonzero(cone[0]):
        var[int(i)] = nv
        cur[int(i)] = nv
        nv += 1
    nx = nv
    rows, cols, vals, ub_rhs = [], [], [], []
    r = 0

    def le(terms, rhs):
        nonlocal r
        for c, v in terms:
            rows.append(r)
            cols.append(c)
            vals.append(v)
        ub_rhs.append(rhs)
        r += 1
    for t in range(D):
        lo, hi = L[t]
        andw, orw = (hi, lo) if side == 0 else (lo, hi)
        ca, co = cone[t + 1][andw], cone[t + 1][orw]
        for a, b, ina, ino in zip(andw.tolist(), orw.tolist(), ca.tolist(), co.tolist()):
            if not (ina or ino):
                continue
            ua, ub_ = cur.get(a), cur.get(b)
            if ina:
                y = nv
                nv += 1
                le([(y, 1)] + [(ua, -1)], 0)
                le([(y, 1)] + [(ub_, -1)], 0)
            if ino:
                y2 = nv
                nv += 1
                le([(y2, 1), (ua, -1), (ub_, -1)], 0)
            if ina:
                cur[a] = y
            if ino:
                cur[b] = y2
    c = np.zeros(nv)
    c[:nx] = 1
    A = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
    lb, ubd = np.zeros(nv), np.ones(nv)
    lb[cur[w]] = 1
    integ = np.zeros(nv)
    integ[:nx] = 1
    res = milp(c, constraints=LinearConstraint(A, -np.inf, np.array(ub_rhs, float)), integrality=integ,
               bounds=Bounds(lb, ubd), options={"time_limit": tlimit, "disp": False})
    best = None if res.x is None else int(round(res.fun))
    lbd = getattr(res, "mip_dual_bound", None)
    return res.status, best, None if lbd is None else math.ceil(lbd - 1e-6)


def exact_product(L, n, T):
    """All outputs of the first T layers as a product over connected components,
    then the rest of the network bit-parallel.  Exact (every input's image after T
    layers is in the product).  Returns worst E over all 2^n inputs, and the count."""
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for lo, hi in L[:T]:
        for a, b in zip(lo.tolist(), hi.tolist()):
            par[find(a)] = find(b)
    comps = {}
    for i in range(n):
        comps.setdefault(find(i), []).append(i)
    states = []
    for c in comps.values():
        pos = {w: j for j, w in enumerate(c)}
        m = len(c)
        v = np.arange(1 << m, dtype=np.int64)
        X = ((v[None, :] >> np.arange(m)[:, None]) & 1).astype(bool)
        for lo, hi in L[:T]:
            for a, b in zip(lo.tolist(), hi.tolist()):
                if a in pos:
                    p, q = X[pos[a]].copy(), X[pos[b]].copy()
                    X[pos[a]], X[pos[b]] = p & q, p | q
        states.append((c, np.unique(X, axis=1)))
    total = 1.0
    for _, U in states:
        total *= U.shape[1]
    if total > 4e9:
        return None, total
    # odometer in chunks: fix the first components, vectorize the rest
    states.sort(key=lambda q: q[1].shape[1])
    worst, split = 0, 0
    tail = 1
    while split < len(states) and tail * states[-1 - split][1].shape[1] <= 1 << 24:
        tail *= states[-1 - split][1].shape[1]
        split += 1
    head, rest = states[:len(states) - split], states[len(states) - split:]
    Wt = np.zeros((n, tail), bool)
    rep = 1
    for c, U in rest:
        idx = (np.arange(tail) // rep) % U.shape[1]
        Wt[c] = U[:, idx]
        rep *= U.shape[1]
    Pt = pack(Wt)
    sizes = [U.shape[1] for _, U in head]
    for code in range(int(np.prod(sizes)) if sizes else 1):
        P = Pt.copy()
        c0 = code
        for (c, U), sz in zip(head, sizes):
            col = c0 % sz
            c0 //= sz
            P[c] = np.where(U[:, col][:, None], ~np.uint64(0), np.uint64(0))
        Y = unpack(sim(L[T:], P), tail)
        _, m, E = errors(Y)
        worst = max(worst, int(E.max()))
    return worst, total


def z3_unsorted(L, n, tlimit):
    """SAT: is there a 0-1 input on which some adjacent output pair is (1, 0)?"""
    import z3
    x = [z3.Bool(f"x{i}") for i in range(n)]
    v = list(x)
    s = z3.SolverFor("QF_FD")
    s.set("timeout", int(tlimit * 1000))
    c = 0
    for lo, hi in L:
        for a, b in zip(lo.tolist(), hi.tolist()):
            p, q = z3.Bool(f"a{c}"), z3.Bool(f"b{c}")
            c += 1
            s.add(p == z3.And(v[a], v[b]), q == z3.Or(v[a], v[b]))
            v[a], v[b] = p, q
    s.add(z3.Or([z3.And(v[i], z3.Not(v[i + 1])) for i in range(n - 1)]))
    return str(s.check())


def z3_error_at_least(L, n, e, tlimit, wires=None):
    """SAT: is there a wire w and an input with at most w + 1 - e zeros and w = 0, or
    at most n - w - e ones and w = 1?  A sat answer is re-simulated."""
    import z3
    x = [z3.Bool(f"x{i}") for i in range(n)]
    v = list(x)
    s = z3.Solver()
    s.set("timeout", int(tlimit * 1000))
    c = 0
    for lo, hi in L:
        for a, b in zip(lo.tolist(), hi.tolist()):
            p, q = z3.Bool(f"a{c}"), z3.Bool(f"b{c}")
            c += 1
            s.add(p == z3.And(v[a], v[b]), q == z3.Or(v[a], v[b]))
            v[a], v[b] = p, q
    ones = lambda m: z3.AtMost(*x, m)            # at most m ones
    ones_ge = lambda m: z3.AtLeast(*x, m)        # at least m ones
    opts = []
    for w in (range(n) if wires is None else wires):
        if w + 1 - e >= 0:
            opts.append(z3.And(z3.Not(v[w]), ones_ge(n - (w + 1 - e))))
        if n - w - e >= 0:
            opts.append(z3.And(v[w], ones(n - w - e)))
    s.add(z3.Or(opts))
    r = str(s.check())
    wit = None
    if r == "sat":
        mdl = s.model()
        y = np.array([z3.is_true(mdl.eval(q, model_completion=True)) for q in x])
        _, _, E = errors(sim(L, y.copy()))
        wit = int(E[0])
        assert wit >= e
    return r, wit


def cmd_exact(a):
    """Exact worst rank error at small d.  n <= 22: all 2^n inputs.  Otherwise a MILP
    per wire and side, seeded by nothing; status 0 = optimal, else time limit."""
    for d in a.depths:
        L, n = tr_layers(d)
        t0 = time.time()
        if n <= 22:
            sorted_all, worst = True, 0
            B = 1 << 14
            for st in range(0, 1 << n, B):
                v = np.arange(st, min(st + B, 1 << n), dtype=np.int64)
                X = ((v[None, :] >> np.arange(n)[:, None]) & 1).astype(bool)
                _, m, E = errors(unpack(sim(L, pack(X)), v.size))
                worst = max(worst, int(E.max()))
            print(json.dumps({"d": d, "n": n, "method": "all 2^n inputs", "worst_err": worst,
                              "sorts": worst == 0, "secs": round(time.time() - t0, 1)}), flush=True)
            continue
        if a.T:
            worst, total = exact_product(L, n, a.T)
            print(json.dumps({"d": d, "n": n, "method": f"image product after {a.T} layers", "images": total,
                              "worst_err": worst, "sorts": worst == 0, "secs": round(time.time() - t0, 1)}), flush=True)
            continue
        if a.z3:
            print(json.dumps({"d": d, "n": n, "method": "z3 QF_FD", "unsorted_input_exists": z3_unsorted(L, n, a.z3),
                              "secs": round(time.time() - t0, 1)}), flush=True)
            continue
        if a.ge:
            r, wit = z3_error_at_least(L, n, a.ge, a.tlimit)
            print(json.dumps({"d": d, "n": n, "method": "z3 E >= e", "e": a.ge, "result": r, "witness_E": wit,
                              "secs": round(time.time() - t0, 1)}), flush=True)
            continue
        wires = range(n) if not a.wires else [int(x) for x in a.wires.split(",")]
        rows, unresolved, worst = [], 0, 0
        for w in wires:
            for side in (0, 1):
                st, best, lb = milp_cert(L, n, w, side, a.tlimit)
                need = w + 1 if side == 0 else n - w
                rows.append((w, side, st, best, lb))
                if best is not None:
                    worst = max(worst, need - best)
                if st != 0 and (lb is None or lb < need):
                    unresolved += 1
                if a.verbose:
                    print(json.dumps({"w": w, "side": side, "status": int(st), "size": best, "lb": lb,
                                      "need": need, "secs": round(time.time() - t0, 1)}), flush=True)
            if time.time() - t0 > a.budget:
                break
        print(json.dumps({"d": d, "n": n, "method": "milp", "wires_done": len(rows) // 2,
                          "worst_err_found": worst, "unresolved_targets": unresolved,
                          "secs": round(time.time() - t0, 1)}), flush=True)


INF = 1 << 62


def beam_zero(L, n, B, side, keep_rule="size"):
    """Single-polarity support recurrence: each wire keeps at most B certificates of
    `side` as explicit input sets.  OR output: the two beams together.  AND output:
    all pairwise set unions.  Keep the B smallest distinct sets.  Upper-closed: every
    kept set is a true certificate, and no size is ever capped or summed."""
    w = (n + 63) // 64
    Sz = np.zeros((n, B, w), np.uint64)
    cnt = np.full((n, B), INF, np.int64)
    Sz[np.arange(n), 0, np.arange(n) // 64] = np.uint64(1) << (np.arange(n) % 64).astype(np.uint64)
    cnt[:, 0] = 1
    for lo, hi in L:
        andw, orw = (hi, lo) if side == 0 else (lo, hi)
        A, Bb = Sz[lo], Sz[hi]
        ca, cb = cnt[lo], cnt[hi]
        U = (A[:, :, None, :] | Bb[:, None, :, :]).reshape(lo.size, B * B, w)
        cU = np.bitwise_count(U).sum(2).astype(np.int64)
        bad = (ca[:, :, None] >= INF) | (cb[:, None, :] >= INF)
        cU[bad.reshape(lo.size, B * B)] = INF
        V = np.concatenate([A, Bb], axis=1)
        cV = np.concatenate([ca, cb], axis=1)
        for tgt, X, c in ((andw, U, cU), (orw, V, cV)):
            order = np.argsort(c, axis=1, kind="stable")
            rows = np.arange(tgt.size)[:, None]
            X, c = X[rows, order], c[rows, order]
            dup = (X[:, 1:] == X[:, :-1]).all(2)
            c[:, 1:][dup] = INF
            order = np.argsort(c, axis=1, kind="stable")[:, :B]
            Sz[tgt], cnt[tgt] = X[rows, order], c[rows, order]
    return Sz, cnt


def bits_to_mask(row, n):
    return np.unpackbits(row.view(np.uint8), bitorder="little")[:n].astype(bool)


def beam_report(L, n, B):
    wit = []
    closest = -10 ** 9
    for side in (0, 1):
        Sz, cnt = beam_zero(L, n, B, side)
        for w in range(n):
            e = err_of(w, int(cnt[w, 0]), n, side)
            closest = max(closest, e)
            if e > 0:
                wit.append((e, w, side, bits_to_mask(Sz[w, 0], n)))
    wit.sort(key=lambda q: -q[0])
    for e, w, side, mask in wit[:8]:
        check_cert(L, n, mask, w, side)
    return {"worst_err": wit[0][0] if wit else 0, "targets_err>0": len(wit), "closest_margin": closest}, wit


def merge_families(f1, f2, rank="size"):
    """All pairs of two beams (P, B, w); keep compatible unions.  rank 'size': the
    rank is the true support size; rank 'tree': the sum of the parents' ranks."""
    S1, T1, c1 = f1
    S2, T2, c2 = f2
    P, B, w = S1.shape
    a = S1[:, :, None, :] | S2[:, None, :, :]
    b = T1[:, :, None, :] | T2[:, None, :, :]
    clash = ((a & b) != 0).any(3)
    both = (c1[:, :, None] < INF) & (c2[:, None, :] < INF)
    if rank == "size":
        size = (np.bitwise_count(a) + np.bitwise_count(b)).sum(3).astype(np.int64)
    else:
        size = np.minimum(np.minimum(c1, 1 << 60)[:, :, None] + np.minimum(c2, 1 << 60)[:, None, :], 1 << 61)
    ok = both & ~clash
    size = np.where(ok, size, INF)
    return (a.reshape(P, B * B, w), b.reshape(P, B * B, w), size.reshape(P, B * B)), int(both.sum()), int(ok.sum())


def pair_family(L, n, B, rank="size"):
    """Mixed-polarity recurrence with supports (the ticket's object).  F[u, v] holds at
    most B restrictions (S -> 0, T -> 1) forcing wire u = 1 and wire v = 0.  One layer:
    u = 1 needs one input of a max output, both inputs of a min output; v = 0 needs one
    input of a min output, both inputs of a max output.  Each option is one earlier pair
    fact, or two facts that merge only if their supports are compatible.  Upper-closed:
    every member really forces the pair.  Keep the B smallest."""
    w = (n + 63) // 64
    S = np.zeros((n, n, B, w), np.uint64)
    T = np.zeros((n, n, B, w), np.uint64)
    c = np.full((n, n, B), INF, np.int64)
    bit = np.uint64(1) << (np.arange(n) % 64).astype(np.uint64)
    idx = np.arange(n)
    for u in range(n):
        T[u, :, 0, u // 64] |= bit[u]
        S[:, u, 0, u // 64] |= bit[u]
    c[:, :, 0] = 2
    c[idx, idx, 0] = INF
    stats = []
    iu = np.triu(np.ones((n, n), bool), 1)
    for t, (lo, hi) in enumerate(L):
        part = idx.copy()
        part[lo], part[hi] = hi, lo
        kind = np.zeros(n, np.int8)              # 0 idle, 1 min output, 2 max output
        kind[lo], kind[hi] = 1, 2
        nS, nT, nc = S.copy(), T.copy(), c.copy()
        tried, compat = 0, 0

        def fam(a, v):
            return S[a, v], T[a, v], c[a, v]

        def mrg(x, y):
            nonlocal tried, compat
            r, tr, ok = merge_families(x, y, rank)
            tried += tr
            compat += ok
            return r
        for u in range(n):
            pu = int(part[u])
            Aopts = [(u,)] if kind[u] == 0 else ([(u, pu)] if kind[u] == 1 else [(u,), (pu,)])
            for kv in (0, 1, 2):
                vs = idx[(kind == kv) & (idx != u)]
                if vs.size == 0:
                    continue
                pv = part[vs]
                Copts = [(vs,)] if kv == 0 else ([(vs,), (pv,)] if kv == 1 else [(vs, pv)])
                cand = []
                for A in Aopts:
                    for C in Copts:
                        if len(A) == 1 and len(C) == 1:
                            cand.append(fam(A[0], C[0]))
                        elif len(A) == 2 and len(C) == 1:
                            cand.append(mrg(fam(A[0], C[0]), fam(A[1], C[0])))
                        elif len(A) == 1:
                            cand.append(mrg(fam(A[0], C[0]), fam(A[0], C[1])))
                        else:
                            cand.append(mrg(fam(A[0], C[0]), fam(A[1], C[1])))
                            cand.append(mrg(fam(A[0], C[1]), fam(A[1], C[0])))
                Sc = np.concatenate([q[0] for q in cand], 1)
                Tc = np.concatenate([q[1] for q in cand], 1)
                Cc = np.concatenate([q[2] for q in cand], 1).copy()
                ordr = np.argsort(Cc, axis=1, kind="stable")
                rows = np.arange(vs.size)[:, None]
                Sc, Tc, Cc = Sc[rows, ordr], Tc[rows, ordr], Cc[rows, ordr]
                dup = (Sc[:, 1:] == Sc[:, :-1]).all(2) & (Tc[:, 1:] == Tc[:, :-1]).all(2)
                Cc[:, 1:][dup] = INF
                ordr = np.argsort(Cc, axis=1, kind="stable")[:, :B]
                nS[u, vs], nT[u, vs], nc[u, vs] = Sc[rows, ordr], Tc[rows, ordr], Cc[rows, ordr]
        S, T, c = nS, nT, nc
        live = c[:, :, 0] < INF
        stats.append({"t": t + 1, "nonempty_pairs": round(float(live.sum() / (n * (n - 1))), 4),
                      "inversions_i<j": int((live & iu).sum()),
                      "merge_compat": round(compat / max(1, tried), 4),
                      "median_size": int(np.median(c[:, :, 0][live])) if live.any() else None})
    return S, T, c, stats


def cmd_family(a):
    """Upper-closed families on a given schedule.  zero: beam_zero; pair: pair_family."""
    from kahale_amplification_kill import build
    for d in a.depths:
        n = a.n or arity(d)
        for sched in a.scheds.split(","):
            L = tr_layers(d, n)[0] if sched == "tr" else build(d, n, "barrier")
            for B in [int(x) for x in a.B.split(",")]:
                t0 = time.time()
                if a.kind == "zero":
                    r, _ = beam_report(L, n, B)
                    print(json.dumps({"d": d, "n": n, "sched": sched, "family": "zero beam", "B": B, **r,
                                      "err/n": round(r["worst_err"] / n, 4),
                                      "secs": round(time.time() - t0, 1)}), flush=True)
                else:
                    S, T, c, st = pair_family(L, n, B, a.rank)
                    live = c[:, :, 0] < INF
                    iu = np.triu(np.ones((n, n), bool), 1)
                    pairs = np.argwhere(live & iu)
                    rng = np.random.default_rng(0)
                    allp = np.argwhere(live)
                    sample = allp[rng.choice(len(allp), min(200, len(allp)), replace=False)] if len(allp) else []
                    for u, v in list(sample) + list(pairs[:50]):   # every member must force the pair
                        Sm, Tm = bits_to_mask(S[u, v, 0], n), bits_to_mask(T[u, v, 0], n)
                        assert not (Sm & Tm).any()
                        for free in (True, False):
                            y = np.full(n, free)
                            y[Sm], y[Tm] = False, True
                            o = sim(L, y.copy())
                            assert o[u] and not o[v]
                    print(json.dumps({"d": d, "n": n, "sched": sched, "family": "pair", "rank": a.rank, "B": B,
                                      "terminal_inversions": int(pairs.shape[0]),
                                      "per_layer": [st[i] for i in range(4, len(st), 6)] + [st[-1]],
                                      "secs": round(time.time() - t0, 1)}), flush=True)


def cmd_validate(a):
    """Brute-force check of the identity on random layered networks: worst rank error
    over all permutations = max over wires of max(w + 1 - z_w, n - w - o_w), and the
    max of E over 0-1 inputs is the same number."""
    import itertools
    rng = np.random.default_rng(a.seed)
    for n in (5, 6, 7):
        for rep in range(a.reps):
            L = []
            for t in range(a.layers):
                p = rng.permutation(n)
                m = int(rng.integers(0, n // 2 + 1))
                x, y = p[:m], p[m:2 * m]
                L.append((np.minimum(x, y).astype(np.int64), np.maximum(x, y).astype(np.int64)))
            P = np.array(list(itertools.permutations(range(n)))).T.astype(np.int32).copy()
            Y = sim_perm(L, P)
            w1 = int(np.abs(Y - np.arange(n)[:, None]).max())
            v = np.arange(1 << n)
            X = ((v[None, :] >> np.arange(n)[:, None]) & 1).astype(bool)
            O = sim(L, X.copy())
            _, _, E = errors(O)
            w2 = int(E.max())
            weight = X.sum(0)
            z = [int((n - weight)[~O[i]].min()) for i in range(n)]
            o = [int(weight[O[i]].min()) for i in range(n)]
            w3 = max(max(i + 1 - z[i], n - i - o[i]) for i in range(n))
            assert w1 == w2 == w3, (n, rep, w1, w2, w3)
            # proof-tree extraction is always a valid certificate
            for i in range(n):
                for side in (0, 1):
                    check_cert(L, n, refine(L, n, i, side, rng, iters=3), i, side)
    print(json.dumps({"validate": "ok", "networks": 3 * a.reps, "layers": a.layers}), flush=True)


def cmd_fib(a):
    """Growth of the proof tree behind the last AND gate, from saved witnesses:
    geometric mean ratio of needed wires per layer while the count is below 200."""
    for d in a.depths:
        L, n = tr_layers(d)
        f = np.load(f"{a.save}_{d}_{n}.npz")
        keys, sets = f["keys"], f["sets"]
        rat, cnt = [], []
        for q in range(min(a.top, len(keys))):
            w, side = int(keys[q, 0]), int(keys[q, 1])
            prof, ands, _, _, _ = proof_tree(L, n, w, side, sets[q])
            tstar = max(t for t in range(len(L)) if ands[t])
            seq = []
            for t in range(tstar, -1, -1):
                if prof[t] >= 200:
                    break
                seq.append(prof[t])
            if len(seq) >= 3:
                rat.append((seq[-1] / seq[0]) ** (1 / (len(seq) - 1)))
                cnt.append(len(seq))
        print(json.dumps({"d": d, "n": n, "witnesses": len(rat), "growth_median": round(float(np.median(rat)), 3),
                          "growth_min": round(min(rat), 3), "growth_max": round(max(rat), 3),
                          "phi": 1.618}), flush=True)


def tree_family(L, n, side, rng=None, alpha=1.0):
    """One support set per wire, ranked by uncapped tree cost, not by set size:
       OR output  : the set of the input with the smaller tree cost,
       AND output : the union of both sets; tree cost max + alpha * min.
    A forward recurrence: state (cost, set) per wire.  Upper-closed: every set is a true
    certificate.  With alpha = 1 the cost is the LB-24 wire recurrence without the cap,
    so this adds exactly one thing to LB-24: the union of the leaves of its own argmin
    tree, in place of their multiset count."""
    w = (n + 63) // 64
    Sz = np.zeros((n, w), np.uint64)
    Sz[np.arange(n), np.arange(n) // 64] = np.uint64(1) << (np.arange(n) % 64).astype(np.uint64)
    c = np.ones(n) if rng is None else 1 + 1e-6 * rng.random(n)
    for lo, hi in L:
        andw, orw = (hi, lo) if side == 0 else (lo, hi)
        A, B = Sz[lo].copy(), Sz[hi].copy()
        ca, cb = c[lo].copy(), c[hi].copy()
        pick = (ca <= cb)[:, None]
        Sz[orw] = np.where(pick, A, B)
        Sz[andw] = A | B
        mn, mx = np.minimum(ca, cb), np.maximum(ca, cb)
        c[orw], c[andw] = mn, mx + alpha * mn
    return Sz, c


def tree_report(L, n, alpha=1.0, rng=None):
    best, at, pos, wit = 0, None, 0, None
    sizes = {}
    for side in (0, 1):
        Sz, c = tree_family(L, n, side, rng, alpha)
        cnt = np.bitwise_count(Sz).sum(1).astype(np.int64)
        sizes[side] = cnt
        e = (np.arange(n) + 1 - cnt) if side == 0 else (n - np.arange(n) - cnt)
        pos += int((e > 0).sum())
        j = int(e.argmax())
        if e[j] > best:
            best, at, wit = int(e[j]), (j, side), bits_to_mask(Sz[j], n)
    if wit is not None:
        check_cert(L, n, wit, at[0], at[1])
    return {"worst_err": best, "err/n": round(best / n, 4), "at": at, "targets_err>0": pos,
            "frac_targets": round(pos / (2 * n), 4)}, sizes


def cmd_tree(a):
    """The tree family on tr and barrier; every worst witness is re-simulated."""
    from kahale_amplification_kill import build
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        n = a.n or arity(d)
        for sched in a.scheds.split(","):
            if sched == "tr":
                L = tr_layers(d, n, a.K or None)[0]
            else:
                L = build(d, n, "barrier")
            for al in [float(x) for x in a.alpha.split(",")]:
                t0 = time.time()
                best = None
                for r in range(a.reps):
                    q, _ = tree_report(L, n, al, rng if r else None)
                    if best is None or q["worst_err"] > best["worst_err"]:
                        best = q
                print(json.dumps({"d": d, "n": n, "sched": sched, "alpha": al, "reps": a.reps, **best,
                                  "secs": round(time.time() - t0, 1)}), flush=True)


def random_barrier(d, n, seed=1, extra=2):
    """The barrier with random wiring: same blocks, same halves, same heights in every
    stage, but the bijection from the lower half to the upper half of each block is
    random (kept to i <-> i + u when a random pair could break the width rule)."""
    from kahale_amplification_kill import wmax_after
    rng = np.random.default_rng(seed)
    z = np.zeros(n, dtype=np.int16)
    L = []
    for t in range(d):
        wmax = wmax_after(d - t - 1 + extra)
        starts = np.flatnonzero(np.r_[True, z[1:] != z[:-1]])
        sizes = np.diff(np.r_[starts, n])
        lo_all, hi_all = [], []
        for b, sz in zip(starts.tolist(), sizes.tolist()):
            m, u = sz // 2, (sz + 1) // 2
            if m == 0 or u > wmax:
                continue
            lo = np.arange(b, b + m)
            hi = lo + u
            if 2 * u - 1 <= wmax:
                hi = rng.permutation(hi)
            lo_all.append(lo)
            hi_all.append(hi)
        lo = np.concatenate(lo_all).astype(np.int64) if lo_all else np.zeros(0, np.int64)
        hi = np.concatenate(hi_all).astype(np.int64) if hi_all else np.zeros(0, np.int64)
        zl, zh = z[lo], z[hi]
        z[lo], z[hi] = np.minimum(zl, zh), np.maximum(zl, zh) + 1
        L.append((lo, hi))
    return L


def hybrid(d, n, K, seed=1, M=64):
    """random_barrier for d - K stages, then the `tr` tail; K = 0: plain random barrier."""
    from kahale_amplification_kill import wmax_after
    base = random_barrier(d, n, seed)[:d - K]
    L = list(base)
    half = max(1, int(round(n / 2)))
    band0, band1 = max(0, n // 2 - half), min(n, n // 2 + half)
    Xd = np.argsort(np.random.default_rng(5).random((M, n)), axis=1).astype(np.int32)
    for lo, hi in base:
        u, v = Xd[:, lo], Xd[:, hi]
        Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
    for t in range(d - K, d):
        wmax = wmax_after(d - t - 1 + 2)
        g = band0 + np.argsort(Xd[:, band0:band1].mean(0), kind="stable")
        h = g[(t % 2):]
        m = min(h[0:-1:2].size, h[1::2].size)
        a0, b0 = h[0:-1:2][:m], h[1::2][:m]
        a, b = np.minimum(a0, b0), np.maximum(a0, b0)
        ok = (b - a) <= wmax
        lo, hi = a[ok].astype(np.int64), b[ok].astype(np.int64)
        L.append((lo, hi))
        u, v = Xd[:, lo], Xd[:, hi]
        Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
    for c in range(2):
        lo = np.arange(c % 2, n - 1, 2)
        L.append((lo, lo + 1))
    return L


def batcher(n):
    """Batcher odd-even merge sort on the next power of two, layered greedily and
    cut to the n lowest wires (a sorter stays a sorter when the top wires are removed,
    since those inputs may be taken as +infinity)."""
    N = 1
    while N < n:
        N *= 2
    comps = []

    def merge(lo, hi, r):
        step = r * 2
        if step < hi - lo:
            merge(lo, hi, step)
            merge(lo + r, hi, step)
            for i in range(lo + r, hi - r, step):
                comps.append((i, i + r))
        else:
            comps.append((lo, lo + r))

    def sort(lo, hi):
        if hi - lo >= 1:
            m = lo + (hi - lo) // 2
            sort(lo, m)
            sort(m + 1, hi)
            merge(lo, hi, 1)
    sort(0, N - 1)
    last = [0] * N
    layers = {}
    for a, b in comps:
        t = max(last[a], last[b])
        last[a] = last[b] = t + 1
        if b < n:
            layers.setdefault(t, []).append((a, b))
    L = []
    for t in range(max(last)):
        c = np.array(layers.get(t, np.zeros((0, 2))), np.int64).reshape(-1, 2)
        L.append((c[:, 0], c[:, 1]))
    return L, max(last)


def cmd_matrix(a):
    """Schedules x adversaries at n = N_d.  sched: barrier, tr, rb (random barrier), rbtr
    (random prefix, tr tail).  adversaries: tree family, proof-tree search."""
    from kahale_amplification_kill import build, check_relaxations
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        n = a.n or arity(d)
        K = a.K or KS[d]
        for sched in a.scheds.split(","):
            t0 = time.time()
            if sched == "barrier":
                L = build(d, n, "barrier")
            elif sched == "tr":
                L = tr_layers(d, n, K)[0]
            elif sched == "rb":
                L = hybrid(d, n, 0, a.seed)
            else:
                L = hybrid(d, n, K, a.seed)
            rel = check_relaxations(L, n, tuple(a.models.split(",")))
            X = np.argsort(np.random.default_rng(11).random((a.samples, n)), axis=1).astype(np.int32).T
            X = sim_perm(L, X)
            i = np.arange(n)
            mean, std = X.mean(1), X.std(1)
            rt = math.sqrt(n)
            res = {"d": d, "n": n, "sched": sched, **{k: v for k, v in rel.items() if k.endswith("_ok")},
                   "sp": round(float(((np.abs(mean - i) <= rt) & (std <= rt / 2)).mean()), 4),
                   "exact": round(float((X == i[:, None]).all(0).mean()), 3),
                   "rand_max_err/n": round(float(np.abs(X - i[:, None]).max()) / n, 4)}
            t, _ = tree_report(L, n)
            res["tree_err"], res["tree_err/n"], res["tree_targets"] = t["worst_err"], t["err/n"], t["frac_targets"]
            if a.budget > 0:
                w = worst_scan(L, n, rng, a.iters, a.stride, a.top, a.budget)
                res["search_err"], res["search_err/n"] = w["worst_err"], w["worst_err/n"]
            res["secs"] = round(time.time() - t0, 1)
            print(json.dumps(res), flush=True)


def cmd_batcher(a):
    """Soundness control: the tree family and the search must find nothing on a sorter."""
    rng = np.random.default_rng(1)
    for n in a.depths:
        L, D = batcher(n)
        if n <= 64:
            p = np.argsort(rng.random((256, n)), axis=1).T.astype(np.int32)
            assert (sim_perm(L, p) == np.arange(n)[:, None]).all()
        q, _ = tree_report(L, n)
        w = worst_scan(L, n, rng, 8, max(1, n // 64), 8, 60)
        print(json.dumps({"n": n, "depth": D, "tree_err": q["worst_err"], "search_err": w["worst_err"]}), flush=True)


def cmd_treepass(a):
    """Largest n on the grid N_d 2^(j/2) passing the tree test, per schedule.  The test is
    not monotone in n, so this reports the largest passing grid point.  Schedule
    specific: never a statement about the optimum over schedules."""
    from kahale_amplification_kill import build
    lo_j, hi_j = [int(x) for x in a.grid.split(",")]
    for d in a.depths:
        N = arity(d)
        for sched in a.scheds.split(","):
            best, rows = None, []
            for j in range(lo_j, hi_j + 1):
                n = max(8, int(round(N * 2 ** (j / 2))))
                K = d // 2
                if sched == "tr":
                    L = tail_schedule(d, n, K, "tr")
                elif sched == "rbtr":
                    L = hybrid(d, n, K, 1)
                elif sched == "rb":
                    L = hybrid(d, n, 0, 1)
                else:
                    L = build(d, n, "barrier")
                q, _ = tree_report(L, n)
                rows.append((j, q["worst_err"]))
                if q["worst_err"] == 0:
                    best = n
            print(json.dumps({"d": d, "N_d": N, "sched": sched, "largest_pass_n": best,
                              "log2(N_d/n)": round(math.log2(N / best), 2) if best else None,
                              "rows": rows}), flush=True)


def cmd_compare(a):
    """Certificate size at the worst wires: LB-24 wire bound, size-ranked beam, tree family,
    proof-tree search; and the need."""
    from kahale_pair_union_rate import step_wire as sw
    for d in a.depths:
        L, n = tr_layers(d)
        f = np.load(f"{a.save}_{d}_{n}.npz")
        keys, sets = f["keys"], f["sets"]
        z, o = np.ones(n, np.int64), np.ones(n, np.int64)
        zc, oc = np.ones(n), np.ones(n)
        for lo, hi in L:
            sw(z, o, lo, hi, n)
        bz = beam_zero(L, n, a.B, 0)[1][:, 0]
        bo = beam_zero(L, n, a.B, 1)[1][:, 0]
        tz = np.bitwise_count(tree_family(L, n, 0)[0]).sum(1).astype(np.int64)
        to = np.bitwise_count(tree_family(L, n, 1)[0]).sum(1).astype(np.int64)
        for q in range(min(a.top, len(keys))):
            w, side = int(keys[q, 0]), int(keys[q, 1])
            print(json.dumps({"d": d, "n": n, "wire": w, "side": side,
                              "need": w + 1 if side == 0 else n - w,
                              "lb24_bound": int((z if side == 0 else o)[w]),
                              f"beam{a.B}": int((bz if side == 0 else bo)[w]),
                              "tree": int((tz if side == 0 else to)[w]),
                              "search": int(sets[q].sum())}), flush=True)


def cmd_dump(a):
    """Best saved witness per depth as hex (bit i = input i in the certificate), after
    re-simulating it on the rebuilt network; check verifies a dumped line."""
    for d in a.depths:
        L, n = tr_layers(d)
        f = np.load(f"{a.save}_{d}_{n}.npz")
        w, side = int(f["keys"][0, 0]), int(f["keys"][0, 1])
        S = f["sets"][0]
        out = check_cert(L, n, S, w, side)
        k, m, E = errors(out)
        print(json.dumps({"d": d, "n": n, "wire": w, "side": side, "size": int(S.sum()), "zeros_k": int(k[0]),
                          "misplaced_m": int(m[0]), "rank_err_E": int(E[0]),
                          "hex": np.packbits(S, bitorder="little").tobytes().hex()}), flush=True)


def cmd_struct(a):
    """Anatomy of the saved witnesses."""
    for d in a.depths:
        L, n = tr_layers(d)
        f = np.load(f"{a.save}_{d}_{n}.npz")
        keys, sets = f["keys"], f["sets"]
        D = len(L)
        rows = []
        for q in range(min(a.top, len(keys))):
            w, side = int(keys[q, 0]), int(keys[q, 1])
            S = sets[q]
            out = check_cert(L, n, S, w, side)
            k, m, E = errors(out)
            prof, ands, shared, leaves, ws = proof_tree(L, n, w, side, S)
            tstar = max((t for t in range(D) if ands[t]), default=0)   # last AND gate
            u = int(np.flatnonzero(ws[tstar + 1])[0]) if prof[tstar + 1] == 1 else -1
            lo_r, hi_r = reach_low(L, n, tstar + 1)
            rl = int(lo_r[u]) if side == 0 else int(hi_r[u])
            hops = sum(1 for t in range(tstar + 1, D)
                       if (ws[t + 1] != ws[t]).any())
            rows.append({"wire": w, "side": side, "size": int(S.sum()), "E": int(E[0]), "m": int(m[0]),
                         "last_AND_layer_from_end": D - 1 - tstar,
                         "single_wire_at_last_AND": prof[tstar + 1] == 1,
                         "u": u, "|u-w|": abs(u - w), "hops": hops,
                         "reach_limit": rl, "unfolded/size": round(leaves / max(1, S.sum()), 2),
                         "needed_at_D-K": prof[D - 2 - KS[d]],
                         "AND_frac_last20": round(sum(ands[-20:]) / max(1, sum(prof[-20:])), 4)})
        keysum = {x: float(np.median([r[x] for r in rows])) for x in
                  ("last_AND_layer_from_end", "hops", "|u-w|", "m", "unfolded/size", "needed_at_D-K")}
        keysum["all_single_wire"] = bool(all(r["single_wire_at_last_AND"] for r in rows))
        print(json.dumps({"d": d, "n": n, "medians": keysum, "rows": rows[:a.show]}), flush=True)


def cmd_scan(a):
    """All wires (stride a.stride), both sides: quick search, then a long search on
    the worst wires.  Every certificate is checked by simulation.  Saves the top
    witnesses to --save (npz), with one summary line per depth."""
    rng = np.random.default_rng(a.seed)
    for d in a.depths:
        L, n = tr_layers(d, a.n or None, a.K or None)
        t0 = time.time()
        wires = np.arange(0, n, max(1, a.stride))
        errs = {}
        sets = {}
        for w in wires:
            for side in (0, 1):
                al = float(rng.choice([0.5, 1.0, 1.0]))
                S = refine(L, n, int(w), side, rng, iters=a.iters, alpha=al)
                errs[(int(w), side)] = err_of(int(w), int(S.sum()), n, side)
                sets[(int(w), side)] = S if errs[(int(w), side)] > 0 else None
            if time.time() - t0 > a.budget * 0.6:
                break
        top = sorted(errs, key=lambda q: -errs[q])[:a.top]
        for w, side in top:
            for al in (1.0, 0.7, 0.4):
                if time.time() - t0 > a.budget:
                    break
                S = refine(L, n, w, side, rng, S=sets[(w, side)], iters=a.iters * 8, alpha=al)
                e = err_of(w, int(S.sum()), n, side)
                if e > errs[(w, side)]:
                    errs[(w, side)], sets[(w, side)] = e, S
        keys = sorted(errs, key=lambda q: -errs[q])
        E = np.array([errs[q] for q in keys])
        for w, side in keys[:a.top]:
            if sets[(w, side)] is not None:
                check_cert(L, n, sets[(w, side)], w, side)
        if a.save:
            sv = [q for q in keys[:a.top] if sets[q] is not None]
            np.savez_compressed(f"{a.save}_{d}_{n}.npz",
                                keys=np.array(sv, int).reshape(-1, 2),
                                sets=np.array([sets[q] for q in sv], bool).reshape(len(sv), n),
                                all_keys=np.array(list(errs), int),
                                all_errs=np.array(list(errs.values()), int))
        w0 = np.array([q[0] for q in keys])
        print(json.dumps({"d": d, "n": n, "K": a.K or KS.get(d), "checked_targets": len(keys),
                          "best_err": int(E[0]), "err/n": round(float(E[0]) / n, 4),
                          "at": keys[0], "z_or_o": (keys[0][0] + 1 - int(E[0])) if keys[0][1] == 0
                          else (n - keys[0][0] - int(E[0])),
                          "frac_targets_err>0": round(float((E > 0).mean()), 4),
                          "frac_err>0.01n": round(float((E > 0.01 * n).mean()), 4),
                          "frac_err>0.05n": round(float((E > 0.05 * n).mean()), 4),
                          "frac_err>0.1n": round(float((E > 0.1 * n).mean()), 4),
                          "worst_err_by_wire_decile": [int(E[(w0 * 10 // n) == q].max()) if ((w0 * 10 // n) == q).any() else None for q in range(10)],
                          "secs": round(time.time() - t0, 1)}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("certs")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--wires", type=int, default=17)
    s.add_argument("--iters", type=int, default=100)
    s.add_argument("--alpha", type=float, default=1.0)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("scan")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--stride", type=int, default=1)
    s.add_argument("--iters", type=int, default=6)
    s.add_argument("--top", type=int, default=40)
    s.add_argument("--budget", type=float, default=1200)
    s.add_argument("--seed", type=int, default=1)
    s.add_argument("--save", default="")
    s = sub.add_parser("struct")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--save", default="")
    s.add_argument("--top", type=int, default=40)
    s.add_argument("--show", type=int, default=4)
    s = sub.add_parser("repair")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--wide", default="2,3,4")
    s.add_argument("--models", default="heights,wire")
    s.add_argument("--samples", type=int, default=64)
    s.add_argument("--iters", type=int, default=6)
    s.add_argument("--stride", type=int, default=1)
    s.add_argument("--top", type=int, default=30)
    s.add_argument("--budget", type=float, default=120)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("thresh")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--grid", type=int, default=33)
    s.add_argument("--steps", type=int, default=400)
    s.add_argument("--batch", type=int, default=128)
    s.add_argument("--tlimit", type=float, default=60)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("cegar")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--rounds", type=int, default=20)
    s.add_argument("--stride", type=int, default=2)
    s.add_argument("--iters", type=int, default=4)
    s.add_argument("--add", type=int, default=64)
    s.add_argument("--fix", type=int, default=2000)
    s.add_argument("--adv", default="search")
    s.add_argument("--final", type=float, default=0)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("exact")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--wires", default="")
    s.add_argument("--tlimit", type=float, default=60)
    s.add_argument("--budget", type=float, default=1200)
    s.add_argument("--verbose", action="store_true")
    s.add_argument("--T", type=int, default=0)
    s.add_argument("--ge", type=int, default=0)
    s.add_argument("--z3", type=float, default=0)
    s = sub.add_parser("family")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--kind", default="zero")
    s.add_argument("--scheds", default="tr,barrier")
    s.add_argument("--B", default="1,4,16")
    s.add_argument("--rank", default="size")
    s = sub.add_parser("validate")
    s.add_argument("--reps", type=int, default=20)
    s.add_argument("--layers", type=int, default=6)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("fib")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--save", default="")
    s.add_argument("--top", type=int, default=40)
    s = sub.add_parser("tree")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--scheds", default="tr,barrier")
    s.add_argument("--alpha", default="1")
    s.add_argument("--reps", type=int, default=1)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("matrix")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--n", type=int, default=0)
    s.add_argument("--K", type=int, default=0)
    s.add_argument("--scheds", default="barrier,tr,rb,rbtr")
    s.add_argument("--models", default="heights,wire")
    s.add_argument("--samples", type=int, default=64)
    s.add_argument("--iters", type=int, default=8)
    s.add_argument("--stride", type=int, default=4)
    s.add_argument("--top", type=int, default=30)
    s.add_argument("--budget", type=float, default=90)
    s.add_argument("--seed", type=int, default=1)
    s = sub.add_parser("batcher")
    s.add_argument("depths", type=int, nargs="+")
    s = sub.add_parser("treepass")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--scheds", default="barrier,tr,rb")
    s.add_argument("--grid", default="-10,0")
    s = sub.add_parser("compare")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--save", default="")
    s.add_argument("--B", type=int, default=16)
    s.add_argument("--top", type=int, default=3)
    s = sub.add_parser("dump")
    s.add_argument("depths", type=int, nargs="+")
    s.add_argument("--save", default="")
    a = ap.parse_args()
    {"dump": cmd_dump, "treepass": cmd_treepass, "compare": cmd_compare, "matrix": cmd_matrix, "batcher": cmd_batcher, "tree": cmd_tree, "validate": cmd_validate, "fib": cmd_fib, "family": cmd_family, "exact": cmd_exact, "certs": cmd_certs, "scan": cmd_scan, "struct": cmd_struct, "repair": cmd_repair,
     "thresh": cmd_thresh, "cegar": cmd_cegar}[a.mode](a)


if __name__ == "__main__":
    main()
