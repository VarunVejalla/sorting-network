#!/usr/bin/env python3
"""LB-35: amplification kill test on the Kahale barrier schedule.

Question.  The LB-02/LB-24/LB-33 barrier schedule (skip-wide block halving on
Kahale heights + 2 odd-even cleanup layers) meets every per-wire, pair and
correlation relaxation at n = N_d, but its middle wires are not amplified:
under the independence (read-once / tree-unfolding) model their 10-90%
threshold width stays ~0.03 while sorting needs ~2.56 sqrt(p(1-p)/n).  Can
read-once-optimal amplification be added to the middle wires (a) inside idle
slots, (b) by re-choosing the middle comparators, or (c) only by appending
extra depth, while the relaxations still pass?

Schedules (every comparator satisfies the width rule (W) for the TOTAL depth):
  barrier          kahale_pair_union_rate.schedule(d, n, 2)
  fill             barrier, plus in every stage the idle wires are paired
                   (consecutive idle wires i < j, alternating offset, j - i <= wmax)
  append A         barrier with widths legal for depth d + 2 + A, then A
                   amplification stages ('oet' = odd-even transposition, or
                   'shell' = distances 2^k, k = K..0 cycling, K <= width rule)
  fill+append A    both
  remix K          barrier, but in the last K main stages every comparator
                   touching the middle band |i - n/2| < n/4 is replaced by
                   local amplifiers (oet among middle wires)
  drop K           the same deletion, with no replacement
  bfly K           the same, replaced by a cycling butterfly (Valiant wires)
  zadj K, zq K     the same, replaced by an equal-height matching (coupled_layers)
  zs K, qs K       zq with the pair kept only if the wire of larger q has the
                   lower index (zs: inside a height group, qs: whole band)
  tr K             whole band paired by closest mean rank, estimated on 64
                   design permutations of the actual network (fresh in ranks)
  zh K             barrier halves, closest-curve bijection between them

Checks on the same layer list (all exact integer arithmetic except ind/truth):
  heights  LB-02 (G) height form, both sides, positional
  wire     LB-24 per-wire certificate sizes (GZ)/(GO) + exact terminal thresholds
  pair     LB-24 pair matrix (optional, n <= ~4000)
  ind      LB-33 independence-model middle width / sorted width, V_ind
  truth    actual network on random permutations: V_true, middle width
Modes:
  idle   d ...            idle-slot census of the barrier schedule
  run    d ... --sched S  one schedule per depth; all checks
  need   d ...            smallest A (append) with ind middle width <= sorted
  blind  d ...            largest K with the middle band deletable (relaxations pass)
  budget d K d K ...      width to gain vs read-once budget in the blind window
  ranks  d ...            actual network: per-wire rank mean/std, sharp vs placed,
                          exact-sort rate, errors on structured inputs
                          (reverse, half rotation, sawtooth, organ pipe)
  nscan  d ... --grid a,b  rule tr on n = N_d 2^(j/2): largest sharp / exact n
  fit    file ...         n_exact, and the sharpness trend, from nscan output
  pairk  d ... --Ks a,b   LB-24 pair relaxation on a list of K
  valiant                 read-once arithmetic (stages needed from width w0)
Finite computations of relaxations and sampled runs; no sorting claim, no Lean.
"""

import argparse
import json
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("\\", 1)[0].rsplit("/", 1)[0])
from kahale_pair_union_rate import (arity, kahale_layers, heights_margins,  # noqa: E402
                                    margins, step_heights, step_wire,
                                    step_pair_side_chunked)
from kahale_correlation_potential import (pgrid, tails, violation,  # noqa: E402
                                          ind_curves, truth_curves)

PHI = (1 + 5 ** 0.5) / 2
KAHALE = 1 / (1 - math.log2(PHI))
GAIN = math.log2(2 / PHI)          # read-once optimal slope gain per layer
DESIGN = 64                        # design permutations of rule 'tr'


def wmax_after(later):
    return (1 << (later + 1)) - 1 if later < 62 else 1 << 62


def pair_idle(lo, hi, n, later, t, band=None):
    """Extra comparators on the wires idle in this stage: consecutive idle
    wires (in index order), offset alternating with t, width <= wmax."""
    act = np.zeros(n, bool)
    act[lo] = True
    act[hi] = True
    idle = np.flatnonzero(~act)
    if band is not None:
        idle = idle[(idle >= band[0]) & (idle < band[1])]
    idle = idle[(t % 2):]
    a, b = idle[0:-1:2], idle[1::2]
    m = min(a.size, b.size)
    a, b = a[:m], b[:m]
    ok = (b - a) <= wmax_after(later)
    return a[ok], b[ok]


def amp_stage(n, j, rule, later, band=None):
    """One appended amplification stage."""
    lo0, hi0 = (0, n) if band is None else band
    if rule == "oet":
        lo = np.arange(lo0 + (j % 2), hi0 - 1, 2)
        return lo, lo + 1
    if rule == "shell":
        K = max(0, min(later, int(math.log2(max(2, hi0 - lo0))) - 1, 6))
        k = K - (j % (K + 1))
        dlt = 1 << k
        i = np.arange(lo0, hi0 - dlt)
        i = i[((i - lo0) // dlt) % 2 == 0]
        return i, i + dlt
    raise ValueError(rule)


def butterfly_stage(band, j, later):
    """Cycling descending butterfly on the band: distances 2^(B-1), ..., 2, 1,
    repeated (B = log2 of the band size), each capped by the width rule.
    On wires with alternating index bits a full cycle is Valiant's
    alternating AND/OR tree (read-once optimal, gain 2/phi per layer)."""
    b0, b1 = band
    B = max(1, int(math.log2(max(2, b1 - b0))))
    k = (B - 1) - (j % B)
    while k > 0 and (1 << k) > wmax_after(later):
        k -= 1
    dlt = 1 << k
    i = np.arange(b0, b1 - dlt)
    i = i[((i - b0) // dlt) % 2 == 0]
    return i, i + dlt


def coupled_layers(d, n, K, frac, rule, extra=2):
    """Kahale skip-wide block halving (as kahale_layers) outside the middle
    band; inside the band, for the last K main stages, an equal-height
    amplifying matching: band wires are grouped by zero height z, and inside a
    group consecutive wires are paired, in index order ('zadj') or in the
    order of their independence-model zero probability at p = 1/2 ('zq',
    closest curves first), alternating the offset; widths <= wmax."""
    z = np.zeros(n, dtype=np.int16)
    idx = np.arange(n, dtype=np.int64)
    half = max(1, int(round(frac * n / 2)))
    b0, b1 = n // 2 - half, n // 2 + half
    inband = (idx >= b0) & (idx < b1)
    q = np.full(n, 0.5)                       # ind model at p = 1/2
    # 'tr': design sample (actual network), used only to choose comparators;
    # evaluation in cmd_ranks uses fresh permutations (different seed)
    Xd = (np.argsort(np.random.default_rng(5).random((DESIGN, n)), axis=1).astype(np.int32)
          if rule == "tr" else None)
    for t in range(d):
        later = d - t - 1 + extra
        wmax = wmax_after(later)
        if t < d - K or rule == "zh":
            starts = np.flatnonzero(np.r_[True, z[1:] != z[:-1]])
        else:
            zz = z.astype(np.int64).copy()
            zz[inband] = -1                   # band handled separately
            starts = np.flatnonzero(np.r_[True, zz[1:] != zz[:-1]])
        sizes = np.diff(np.r_[starts, n])
        bstart = np.repeat(starts, sizes)
        bsize = np.repeat(sizes, sizes)
        k = idx - bstart
        u = (bsize + 1) // 2
        lo_mask = (k < bsize // 2) & ~(u > wmax)
        if t >= d - K and rule != "zh":
            lo_mask &= ~inband
            lo_mask &= ~inband[np.minimum(idx + u, n - 1)]
        lo = idx[lo_mask]
        hi = lo + u[lo_mask]
        if rule == "zh" and t >= d - K:
            # same blocks and halves as the barrier; inside band blocks the
            # lower-half -> upper-half bijection matches closest q(1/2)
            lo_mask2 = (k < bsize // 2) & ~(u > wmax)
            lo = idx[lo_mask2]
            hi = lo + u[lo_mask2]
            nl, nh = [lo], [hi]
            bands = np.unique(bstart[lo[inband[lo]]]) if lo.size else []
            sel = np.ones(lo.size, bool)
            for b in bands:
                m = int(bsize[b]) // 2
                uu = int(u[b])
                L = np.arange(b, b + m)
                H = np.arange(b + uu, b + uu + m)
                Ls = L[np.argsort(-q[L], kind="stable")]
                Hs = H[np.argsort(-q[H], kind="stable")]
                if np.all(np.abs(Hs - Ls) <= wmax):
                    sel &= ~((lo >= b) & (lo < b + m))
                    nl.append(Ls)
                    nh.append(Hs)
            lo = np.r_[lo[sel], np.concatenate(nl[1:]) if len(nl) > 1 else np.zeros(0, np.int64)].astype(np.int64)
            hi = np.r_[hi[sel], np.concatenate(nh[1:]) if len(nh) > 1 else np.zeros(0, np.int64)].astype(np.int64)
        if t >= d - K and rule != "zh":
            al, ah = [], []
            bw = idx[inband]
            for h in ([0] if rule in ("qs", "tr") else np.unique(z[bw])):
                g = bw if rule in ("qs", "tr") else bw[z[bw] == h]
                if rule in ("zq", "zs", "qs"):
                    g = g[np.argsort(-q[g], kind="stable")]
                elif rule == "tr":            # closest estimated mean rank
                    g = g[np.argsort(Xd[:, g].mean(0), kind="stable")]
                g = g[(t % 2):]
                a, b = g[0:-1:2], g[1::2]
                m = min(a.size, b.size)
                a0, b0_ = a[:m], b[:m]
                a, b = np.minimum(a0, b0_), np.maximum(a0, b0_)
                ok = (b - a) <= wmax
                if rule in ("zs", "qs"):      # orientation agrees with position
                    ok &= a0 < b0_
                al.append(a[ok])
                ah.append(b[ok])
            lo = np.r_[lo, np.concatenate(al)].astype(np.int64)
            hi = np.r_[hi, np.concatenate(ah)].astype(np.int64)
        zl, zh = z[lo], z[hi]
        z[lo], z[hi] = np.minimum(zl, zh), np.maximum(zl, zh) + 1
        ql, qh = q[lo], q[hi]
        q[lo], q[hi] = ql + qh - ql * qh, ql * qh
        if Xd is not None:
            u, v = Xd[:, lo], Xd[:, hi]
            Xd[:, lo], Xd[:, hi] = np.minimum(u, v), np.maximum(u, v)
        yield lo, hi


def build(d, n, sched, A=0, rule="oet", K=0, frac=0.5):
    cleanup = 2
    D = d + cleanup + A
    if sched.startswith(("zadj", "zq", "zh", "zs", "qs", "tr")):
        rl = sched[:4] if sched.startswith("zadj") else sched[:2]
        base = list(coupled_layers(d, n, K, frac, rl,
                                   cleanup + A))
    else:
        base = list(kahale_layers(d, n, cleanup + A))
    layers = []
    half = max(1, int(round(frac * n / 2)))
    band = (n // 2 - half, n // 2 + half)
    for t, (lo, hi) in enumerate(base):
        later = D - t - 1
        if sched.startswith("bfly") and t >= d - K:
            keep = ~(((lo >= band[0]) & (lo < band[1])) | ((hi >= band[0]) & (hi < band[1])))
            lo, hi = lo[keep], hi[keep]
            a, b = butterfly_stage(band, t - (d - K), later)
            lo, hi = np.r_[lo, a], np.r_[hi, b]
        if (sched.startswith("remix") or sched.startswith("drop")) and t >= d - K:
            keep = ~(((lo >= band[0]) & (lo < band[1])) | ((hi >= band[0]) & (hi < band[1])))
            lo, hi = lo[keep], hi[keep]
            if sched.startswith("remix"):
                a, b = pair_idle(lo, hi, n, later, t, band)
                lo, hi = np.r_[lo, a], np.r_[hi, b]
        if "fill" in sched:
            a, b = pair_idle(lo, hi, n, later, t)
            lo, hi = np.r_[lo, a], np.r_[hi, b]
        layers.append((lo, hi))
    for c in range(cleanup):
        lo = np.arange(c % 2, n - 1, 2)
        layers.append((lo, lo + 1))
    for j in range(A):
        later = A - j - 1
        layers.append(amp_stage(n, j, rule, later))
    assert len(layers) == D
    # width rule audit
    for t, (lo, hi) in enumerate(layers):
        assert np.all(hi > lo) and np.all(hi - lo <= wmax_after(D - t - 1)), t
        u = np.r_[lo, hi]
        assert np.unique(u).size == u.size, t
    return layers


def check_relaxations(layers, n, models=("heights", "wire")):
    D = len(layers)
    out = {}
    if "heights" in models:
        z, o = np.zeros(n, np.int64), np.zeros(n, np.int64)
        ok = heights_margins(0, D, n, z, o)
        for t, (lo, hi) in enumerate(layers, 1):
            step_heights(z, o, lo, hi)
            ok &= heights_margins(t, D, n, z, o)
        out["heights_ok"] = bool(ok)
    if "wire" in models:
        z, o = np.ones(n, np.int64), np.ones(n, np.int64)
        mi = math.inf
        for t, (lo, hi) in enumerate(layers, 1):
            step_wire(z, o, lo, hi, n)
            mz, mo = margins(t, D, n, z, o)
            if t < D:
                mi = min(mi, mz, mo)
            else:
                out["wire_terminal_margin"] = min(mz, mo)
        out["wire_interior_margin"] = mi
        out["wire_ok"] = mi >= 0 and out["wire_terminal_margin"] >= 0
    if "pair" in models:
        Z = np.full((n, n), 2, np.int16 if n <= 32767 else np.int32)
        np.fill_diagonal(Z, 1)
        O = Z.copy()
        mi = math.inf
        for t, (lo, hi) in enumerate(layers, 1):
            Z = step_pair_side_chunked(Z, lo, hi, n, hi)
            O = step_pair_side_chunked(O, lo, hi, n, lo)
            mz, mo = margins(t, D, n, np.diag(Z).astype(np.int64), np.diag(O).astype(np.int64))
            if t < D:
                mi = min(mi, mz, mo)
            else:
                out["pair_terminal_margin"] = min(mz, mo)
        out["pair_interior_margin"] = mi
        out["pair_ok"] = mi >= 0 and out["pair_terminal_margin"] >= 0
    return out


def fine_grid(n, P):
    """pgrid plus a fine grid on the middle threshold window (width ~ n^-1/2)."""
    h = min(0.45, 8.0 / math.sqrt(n))
    return np.unique(np.r_[pgrid(n, P), np.linspace(0.5 - h, 0.5 + h, 161)])


def width(qq, ps):
    return float(np.interp(0.9, qq, ps) - np.interp(0.1, qq, ps))


def eval_ind(layers, n, P=400, smax=8):
    D = len(layers)
    ps = fine_grid(n, P)
    T = tails(n, ps)
    keep = set(range(max(0, D - smax), D + 1))
    cur = ind_curves(layers, n, ps, keep)
    mid = n // 2
    wi, ws = width(cur[D][:, mid], ps), width(T[:, mid + 1], ps)
    V = {D - t: round(violation(cur[t], T, n, D - t)[0], 4) for t in sorted(keep)}
    vt, vw, vside = violation(cur[D], T, n, 0)
    p50 = float(np.interp(0.5, cur[D][::-1, mid], ps[::-1])) if cur[D][0, mid] > cur[D][-1, mid] else float(np.interp(0.5, cur[D][:, mid], ps))
    # band of middle wires: median over |i - n/2| < sqrt(n) of log2 width ratio
    r = max(1, int(math.isqrt(n)))
    wr = [math.log2(width(cur[D][:, i], ps) / width(T[:, i + 1], ps))
          for i in range(mid - r, mid + r, max(1, r // 8))]
    return {"mid_width_ind": round(wi, 5), "mid_width_sorted": round(ws, 5),
            "log2_ratio_mid": round(math.log2(wi / ws), 3),
            "log2_ratio_band_max": round(max(wr), 3),
            "mid_p50_ind": round(p50, 4),
            "V_ind_max": max(V.values()), "V_ind_terminal": V[0],
            "V_ind_terminal_wire": vw, "V_by_s": {k: V[k] for k in sorted(V) if k <= 8}}


def eval_truth(layers, n, samples, P=96, smax=8):
    D = len(layers)
    ps = fine_grid(n, P)
    T = tails(n, ps)
    keep = set(range(max(0, D - smax), D + 1))
    tcur, minr, maxr = truth_curves(layers, n, ps, keep, samples)
    mid = n // 2
    V = {D - t: round(violation(tcur[t], T, n, D - t)[0], 4) for t in sorted(keep)}
    return {"mid_width_true": round(width(tcur[D][:, mid], ps), 5),
            "V_true_max": max(V.values()), "V_true_terminal": V[0]}


def cmd_idle(a):
    for d in a.depths:
        n = a.n or arity(d)
        D = d + 2
        L = build(d, n, "barrier")
        act = np.zeros((D, n), bool)
        for t, (lo, hi) in enumerate(L):
            act[t, lo] = True
            act[t, hi] = True
        c, r = n // 2, max(1, int(math.isqrt(n)))
        core = act[:d, c - r:c + r]
        last = np.array([np.flatnonzero(core[:, w]).max() for w in range(core.shape[1])])
        tail = d - 1 - last
        res = {"d": d, "n": n, "log2n": round(math.log2(n), 3),
               "slot_util_all": round(float(act[:d].mean()), 4),
               "slot_util_midhalf": round(float(act[:d, n // 4:n - n // 4].mean()), 4),
               "core_idle_stages_mean": round(float((~core).sum(0).mean()), 2),
               "core_idle_tail_mean": round(float(tail.mean()), 2),
               "tail/log2n": round(float(tail.mean()) / math.log2(n), 3),
               "valiant_stages_needed_from_w0.03": None}
        ps = pgrid(n, 200)
        T = tails(n, ps)
        ws = width(T[:, c + 1], ps)
        res["valiant_stages_needed_from_w0.03"] = round(math.log2(0.03 / ws) / GAIN, 2)
        print(json.dumps(res), flush=True)


def cmd_run(a):
    for d in a.depths:
        n = a.n or arity(d)
        L = build(d, n, a.sched, a.A, a.rule, a.K, a.frac)
        res = {"d": d, "n": n, "sched": a.sched, "A": a.A, "rule": a.rule, "K": a.K, "frac": a.frac,
               "depth": len(L), "log2n": round(math.log2(n), 3),
               "depth/log2n": round(len(L) / math.log2(n), 3),
               "comparators": int(sum(lo.size for lo, _ in L))}
        res.update(check_relaxations(L, n, tuple(a.models.split(","))))
        res.update(eval_ind(L, n, a.P, a.smax))
        if a.samples:
            res.update(eval_truth(L, n, a.samples))
        print(json.dumps(res), flush=True)


def cmd_need(a):
    """Smallest A for which the appended schedule's ind middle width <= sorted."""
    for d in a.depths:
        n = a.n or arity(d)
        out = {"d": d, "n": n, "log2n": round(math.log2(n), 3), "sched": a.sched, "rule": a.rule}
        for A in range(0, a.Amax + 1):
            L = build(d, n, a.sched, A, a.rule)
            r = eval_ind(L, n, a.P)
            if r["log2_ratio_mid"] <= 0 and r["log2_ratio_band_max"] <= a.tol:
                out.update({"A_needed": A, "A/log2n": round(A / math.log2(n), 3), **r})
                rel = check_relaxations(L, n)
                out.update(rel)
                break
        else:
            out["A_needed"] = None
        print(json.dumps(out), flush=True)


def cmd_blind(a):
    """Largest K such that dropping every comparator touching the middle band
    in the last K main stages keeps the heights and wire relaxations."""
    for d in a.depths:
        n = a.n or arity(d)
        def ok(K):
            r = check_relaxations(build(d, n, "drop", 0, "oet", K, a.frac), n,
                                  tuple(a.models.split(",")))
            return all(v for k, v in r.items() if k.endswith("_ok"))
        lo, hi = 0, d
        if ok(d):
            lo = d
        else:
            while hi - lo > 1:
                m = (lo + hi) // 2
                lo, hi = (m, hi) if ok(m) else (lo, m)
        lg = math.log2(n)
        print(json.dumps({"d": d, "n": n, "log2n": round(lg, 3), "frac": a.frac,
                          "K_blind": lo, "K_blind/log2n": round(lo / lg, 3),
                          "d-K_blind": d - lo, "(d-K)/log2n": round((d - lo) / lg, 3),
                          "readonce_need_from_input/log2n": round(math.log2(0.8 * math.sqrt(n) / 1.28) / GAIN / lg, 3)}),
              flush=True)


def cmd_budget(a):
    """Read-once amplification budget of the relaxation-blind window: band
    median ind width at time d - K_blind (barrier), the sorted width, and the
    read-once-optimal gain GAIN * K_blind, all in bits."""
    for d, K in zip(a.depths[0::2], a.depths[1::2]):
        n = a.n or arity(d)
        L = build(d, n, "barrier")
        ps = fine_grid(n, a.P)
        T = tails(n, ps)
        t0 = d - K
        cur = ind_curves(L[:t0], n, ps, {t0})[t0]
        mid = n // 2
        w0 = width(cur[:, mid], ps)
        ws = width(T[:, mid + 1], ps)
        lg = math.log2(n)
        need = math.log2(w0 / ws)
        print(json.dumps({"d": d, "n": n, "log2n": round(lg, 3), "K_blind": K,
                          "w_at_d-K": round(w0, 5), "w_sorted": round(ws, 5),
                          "need_bits": round(need, 3), "need/log2n": round(need / lg, 3),
                          "readonce_budget_bits": round(GAIN * K, 3),
                          "budget/log2n": round(GAIN * K / lg, 3),
                          "surplus_bits": round(GAIN * K - need, 3)}), flush=True)


def cmd_nscan(a):
    """Rule tr, band = all wires: on a grid n = N_d 2^(j/2) report the exact
    sort rate on fresh permutations, the sharp-and-placed fraction, and the
    relaxations.  n_exact = largest n with rate >= 1/2; n_sharp = largest n
    with sharp-and-placed >= 0.99 (both restricted to relaxation-passing n)."""
    rng = np.random.default_rng(23)
    lo_j, hi_j = [int(x) for x in a.grid.split(",")]
    for d in a.depths:
        N = arity(d)
        K = a.K or d // 2
        for j in range(lo_j, hi_j + 1):
            n = max(8, int(round(N * 2 ** (j / 2))))
            L = build(d, n, "tr", 0, "oet", K, 1.0)
            rel = check_relaxations(L, n, ("heights", "wire"))
            ex, m1, m2, done = 0, np.zeros(n), np.zeros(n), 0
            i = np.arange(n)
            while done < a.samples:
                b = min(32, a.samples - done)
                X = np.argsort(rng.random((b, n)), axis=1).astype(np.int32)
                for lo, hi in L:
                    u, v = X[:, lo], X[:, hi]
                    X[:, lo], X[:, hi] = np.minimum(u, v), np.maximum(u, v)
                ex += int((X == i).all(1).sum())
                m1 += X.sum(0)
                m2 += (X.astype(np.float64) ** 2).sum(0)
                done += b
            mean = m1 / done
            std = np.sqrt(np.maximum(0, m2 / done - mean ** 2))
            rt = math.sqrt(n)
            print(json.dumps({"d": d, "K": K, "N_d": N, "j": j, "n": n,
                              "log2(n/N_d)": round(math.log2(n / N), 2),
                              "depth/log2n": round((d + 2) / math.log2(n), 3),
                              "heights_ok": rel["heights_ok"], "wire_ok": rel["wire_ok"],
                              "exact_sorted_frac": round(ex / done, 3),
                              "sharp_placed": round(float(((np.abs(mean - i) <= rt)
                                                           & (std <= rt / 2)).mean()), 4),
                              "std/sqrtn_median": round(float(np.median(std)) / rt, 4)}),
                  flush=True)


def cmd_fit(a):
    """Fit nscan output.  n_exact(d) = interpolated n with exact rate 1/2.
    Sharpness: least squares log2(std/sqrt n) = A d + B log2(n/N_d) + C.  The
    largest sharp n solves std/sqrt n = 1/2; if the trend persisted, its
    deficit against N_d grows A/B bits per stage, so the implied asymptotic
    coefficient of this heuristic is 1/(1/c - A/B).  Extrapolation of one
    heuristic: an upper estimate of what schedules need, never a lower bound."""
    rows = []
    for f in a.files:
        for line in open(f):
            if line.startswith("{"):
                r = json.loads(line)
                if "exact_sorted_frac" in r and "j" in r:
                    rows.append(r)
    exact = []
    for d in sorted({r["d"] for r in rows}):
        g = sorted((r for r in rows if r["d"] == d), key=lambda r: r["n"])
        ne = None
        for u, v in zip(g, g[1:]):
            if u["exact_sorted_frac"] >= 0.5 > v["exact_sorted_frac"]:
                t = (u["exact_sorted_frac"] - 0.5) / (u["exact_sorted_frac"] - v["exact_sorted_frac"])
                ne = 2 ** (math.log2(u["n"]) + t * (math.log2(v["n"]) - math.log2(u["n"])))
        exact.append((d, g[0]["N_d"], ne))
        passing = [r for r in g if r["heights_ok"] and r["wire_ok"]]
        print(json.dumps({"d": d, "N_d": g[0]["N_d"],
                          "n_exact": round(ne) if ne else None,
                          "log2(N_d/n_exact)": round(math.log2(g[0]["N_d"] / ne), 2) if ne else None,
                          "largest_relaxation_passing_n": passing[-1]["n"] if passing else None,
                          "min_sharp_placed_on_grid": min(r["sharp_placed"] for r in g),
                          "min_depth/log2n_on_grid": min(r["depth/log2n"] for r in g)}))
    use = [r for r in rows if r["std/sqrtn_median"] >= 0.002]
    M = np.array([[r["d"], r["log2(n/N_d)"], 1.0] for r in use])
    y = np.log2([r["std/sqrtn_median"] for r in use])
    (A, B, C), *_ = np.linalg.lstsq(M, y, rcond=None)
    res = y - M @ np.array([A, B, C])
    print(json.dumps({"fit_rows": len(use), "A_bits_per_stage": round(float(A), 4),
                      "B_bits_per_bit_of_n": round(float(B), 4), "C": round(float(C), 3),
                      "resid_rms": round(float(np.sqrt((res ** 2).mean())), 3),
                      "sharp_deficit_slope_A/B": round(float(A / B), 4),
                      "implied_coefficient": round(1 / (1 / KAHALE - float(A / B)), 3),
                      "d_where_sharp_limit_reaches_N_d": round((-1 - float(C)) / float(A), 1)}))
    ds = [(d, math.log2(N / ne)) for d, N, ne in exact if ne]
    if len(ds) >= 2:
        x, z = np.array(ds).T
        sl = np.polyfit(x, z, 1)[0]
        print(json.dumps({"exact_deficit_slope_bits_of_n_per_stage": round(float(sl), 4)}))


def cmd_pairk(a):
    """LB-24 pair relaxation only, on a list of K values."""
    for d in a.depths:
        n = a.n or arity(d)
        for K in map(int, a.Ks.split(",")):
            r = check_relaxations(build(d, n, a.sched, 0, "oet", K, a.frac), n, ("pair",))
            print(json.dumps({"d": d, "n": n, "sched": a.sched, "K": K, **r}), flush=True)


def cmd_ranks(a):
    """Actual network on random permutations: per-wire rank mean and std.
    sharp: std(R_i) <= sqrt(n)/2 (the width of the wire is then within a
    constant of the sorted width).  placed: |mean R_i - i| <= sqrt(n).
    relabel: the same placement test after sorting the wires by mean rank."""
    rng = np.random.default_rng(11)
    for d in a.depths:
        n = a.n or arity(d)
        L = build(d, n, a.sched, a.A, a.rule, a.K, a.frac)
        m1, m2, done = np.zeros(n), np.zeros(n), 0
        mn, mx = np.full(n, n), np.full(n, -1)
        exact, wrong = 0, 0.0

        def run_net(X):
            for lo, hi in L:
                u, v = X[:, lo], X[:, hi]
                X[:, lo], X[:, hi] = np.minimum(u, v), np.maximum(u, v)
            return X

        while done < a.samples:
            b = min(64, a.samples - done)
            X = np.argsort(rng.random((b, n)), axis=1).astype(np.int32)
            X = run_net(X)
            exact += int((X == np.arange(n)).all(1).sum())
            wrong += float((X != np.arange(n)).sum())
            m1 += X.sum(0)
            mn, mx = np.minimum(mn, X.min(0)), np.maximum(mx, X.max(0))
            m2 += (X.astype(np.float64) ** 2).sum(0)
            done += b
        mean = m1 / done
        std = np.sqrt(np.maximum(0, m2 / done - mean ** 2))
        i = np.arange(n)
        rt = math.sqrt(n)
        err = np.maximum(mx - i, i - mn)
        # structured inputs: a sorting network must also get these right
        h = n // 2
        rot = (i + h) % n
        saw = np.argsort(np.r_[np.arange(0, n, 2), np.arange(1, n, 2)], kind="stable")
        pipe = np.r_[np.arange(0, n, 2), np.arange(n - 1 - (n % 2 == 0) * 0, 0, -2)[:n // 2]]
        pipe = np.argsort(np.argsort(pipe, kind="stable"), kind="stable")
        rev = n - 1 - i
        S = np.stack([rev, rot, saw, pipe]).astype(np.int32)
        Y = run_net(S.copy())
        c0, c1 = n // 2 - n // 4, n // 2 + n // 4
        core = np.abs(i - n // 2) <= rt
        order = np.argsort(mean, kind="stable")
        res = {"d": d, "n": n, "sched": a.sched, "K": a.K, "samples": done,
               "std/sqrtn_median_midhalf": round(float(np.median(std[c0:c1])) / rt, 3),
               "std/sqrtn_core_median": round(float(np.median(std[core])) / rt, 3),
               "std/sqrtn_wire_n/2": round(float(std[n // 2]) / rt, 3),
               "sharp_frac_all": round(float((std <= rt / 2).mean()), 4),
               "sharp_frac_midhalf": round(float((std[c0:c1] <= rt / 2).mean()), 4),
               "placed_frac_all": round(float((np.abs(mean - i) <= rt).mean()), 4),
               "placed_frac_midhalf": round(float((np.abs(mean[c0:c1] - i[c0:c1]) <= rt).mean()), 4),
               "disp/n_median_midhalf": round(float(np.median(np.abs(mean[c0:c1] - i[c0:c1]))) / n, 4),
               "disp/n_max": round(float(np.abs(mean - i).max()) / n, 4),
               "rank_err/n_max": round(float(max((mx - i).max(), (i - mn).max())) / n, 4),
               "rank_err/sqrtn_median": round(float(np.median(err)) / rt, 2),
               "rank_err/n_q99": round(float(np.quantile(err, 0.99)) / n, 4),
               "exact_sorted_frac": round(exact / done, 4),
               "wrong_wires_frac_mean": round(wrong / done / n, 4),
               "structured_mean_err/n": [round(float(np.abs(Y[k] - i).mean()) / n, 4) for k in range(4)],
               "structured_max_err/n": [round(float(np.abs(Y[k] - i).max()) / n, 4) for k in range(4)],
               "sharp_placed_frac_all": round(float(((np.abs(mean - i) <= rt)
                                                     & (std <= rt / 2)).mean()), 4),
               "relabel_sharp_placed_frac": round(float(((np.abs(mean[order] - i) <= rt)
                                                         & (std[order] <= rt / 2)).mean()), 4)}
        print(json.dumps(res), flush=True)


def cmd_valiant(a):
    # slope gain per layer at the read-once optimum, and the sum rule
    rows = []
    for lg in (10, 14, 20, 32, 64, 128):
        n = 2.0 ** lg
        ws = 2.56 * 0.5 / math.sqrt(n)
        need_ro = math.log2(0.03 / ws) / GAIN       # from LB-33's w0 = 0.03
        need_ro_raw = math.log2(0.8 / ws) / GAIN     # from a single input
        need_sum = math.log2(0.8 / ws)               # sum rule: slope x2 per layer
        rows.append({"log2n": lg, "readonce_from_0.03": round(need_ro, 2),
                     "readonce_from_input": round(need_ro_raw, 2),
                     "sum_rule_from_input": round(need_sum, 2),
                     "kahale_depth": round(KAHALE * lg, 2)})
    print(json.dumps({"gain_per_layer_readonce": GAIN, "readonce_coeff": 0.5 / GAIN,
                      "sum_rule_coeff": 0.5, "rows": rows}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="mode", required=True)
    for name in ("idle", "run", "need", "blind", "budget", "ranks", "pairk", "nscan"):
        s = sub.add_parser(name)
        s.add_argument("depths", type=int, nargs="+")
        s.add_argument("--n", type=int, default=0)
        s.add_argument("--sched", default="barrier")
        s.add_argument("--A", type=int, default=0)
        s.add_argument("--Amax", type=int, default=60)
        s.add_argument("--K", type=int, default=0)
        s.add_argument("--rule", default="oet")
        s.add_argument("--P", type=int, default=400)
        s.add_argument("--samples", type=int, default=0)
        s.add_argument("--models", default="heights,wire")
        s.add_argument("--tol", type=float, default=0.25)
        s.add_argument("--frac", type=float, default=0.5)
        s.add_argument("--smax", type=int, default=8)
        s.add_argument("--Ks", default="0")
        s.add_argument("--grid", default="-8,8")
        s.add_argument("--M", type=int, default=64)
    sub.add_parser("valiant")
    f = sub.add_parser("fit")
    f.add_argument("files", nargs="+")
    a = ap.parse_args()
    global DESIGN
    DESIGN = getattr(a, "M", DESIGN)
    if a.mode == "fit":
        return cmd_fit(a)
    {"idle": cmd_idle, "run": cmd_run, "need": cmd_need, "blind": cmd_blind, "budget": cmd_budget, "ranks": cmd_ranks, "pairk": cmd_pairk, "nscan": cmd_nscan, "fit": cmd_fit,
     "valiant": cmd_valiant}[a.mode](a)


if __name__ == "__main__":
    main()
