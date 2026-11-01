#!/usr/bin/env python3
"""LB-03: comparison information on the Kahale-extremal schedules.

For a comparator g write S_g for its swap bit on a uniform random permutation,
Y_g for the whole rank vector after g, and S_<g for all earlier swap bits, in a
fixed gate order.  Three per-gate quantities are kept apart:

  marginal    H(S_g)            the screen's h_g (binary entropy of the outcome)
  learned     H(S_g | S_<g)     decision-tree information
  forgotten   H(S_g | Y_g)      the ticket's h_g, H(Y_(g-1)) - H(Y_g) (LB-26)

The chain rule and conditioning give, for every network,

  sum forgotten = lg n! - H(Y_final) <= sum learned = H(S) <= sum marginal.

On a sorter the two lower sums both equal lg n!.  At large n only the marginal
and a sound relaxation of 'learned' can be estimated:

  ctx1  H(S_g | swap bits of the two gates feeding g)
  ctx2  H(S_g | those bits and the bits of the gates feeding them)

each of which upper-bounds H(S_g | S_<g) because it conditions on less.

Modes:
  exact    every permutation on n <= 10 wires: all three sums, identities
  blocks   two sorted blocks, one aligned layer, exact: marginal, learned, forgotten
  screen   barrier and tr at n = N_d: stage profile, totals, residual entropy bound
  control  Batcher at n = N_d (a real sorter) on the same estimators
  butterfly  recursive doubling on 2^t wires: marginal waste, equal heights
Sampled figures are finite estimates.  Nothing here is a rate or a sorting claim.
"""

import argparse
import json
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("\\", 1)[0].rsplit("/", 1)[0])
from kahale_amplification_kill import build, check_relaxations  # noqa: E402
from kahale_pair_union_rate import arity  # noqa: E402
from kahale_worst_case_inputs import batcher  # noqa: E402

KAHALE = 1 / (1 - math.log2((1 + 5 ** 0.5) / 2))
LN2 = math.log(2)
LB35_K = {40: 20, 48: 20, 56: 28, 64: 32, 72: 36, 80: 36}


def tr_K(d):
    return LB35_K.get(d, d // 2)


def lg_fact(n):
    return math.lgamma(n + 1) / LN2


def h2(p):
    p = np.asarray(p, dtype=np.float64)
    out = np.zeros_like(p)
    m = (p > 0) & (p < 1)
    out[m] = -(p[m] * np.log2(p[m]) + (1 - p[m]) * np.log2(1 - p[m]))
    return out


def entropy_of(keys):
    """Shannon entropy in bits of the empirical law of an integer array."""
    _, c = np.unique(keys, return_counts=True)
    q = c / keys.size
    return float(-(q * np.log2(q)).sum())


def forced(n, D):
    """Slots, information need, and the waste every sorter of this size has."""
    M = D * (n // 2)
    need = lg_fact(n)
    return M, need, M - need


# ----------------------------------------------------------------- exact mode
def all_perms(n):
    X = np.array([[0]], dtype=np.int8)
    for k in range(1, n):
        m = X.shape[0]
        Y = np.empty((m * (k + 1), k + 1), dtype=np.int8)
        for pos in range(k + 1):
            Y[pos * m:(pos + 1) * m, :pos] = X[:, :pos]
            Y[pos * m:(pos + 1) * m, pos] = k
            Y[pos * m:(pos + 1) * m, pos + 1:] = X[:, pos:]
        X = Y
    return X


def exact_sums(n, layers):
    """Exact gate sums on all n! inputs, gates in layer order, by lo index."""
    X = all_perms(n).astype(np.int64)
    N = X.shape[0]
    pw = n ** np.arange(n, dtype=np.int64)
    Hy = lg_fact(n)
    hist = np.zeros(N, dtype=np.int64)        # dense relabelled history
    Hh = 0.0
    tot = dict(marginal=0.0, learned=0.0, forgotten=0.0)
    prof = []
    G = 0
    for lo, hi in layers:
        rm = rl = rf = 0.0
        for a, b in sorted(zip(lo.tolist(), hi.tolist())):
            G += 1
            s = X[:, a] > X[:, b]
            rm += float(h2(s.mean()))
            u, v = X[:, a].copy(), X[:, b].copy()
            X[:, a], X[:, b] = np.minimum(u, v), np.maximum(u, v)
            Hy2 = entropy_of(X @ pw)
            rf += Hy - Hy2
            Hy = Hy2
            _, hist = np.unique(hist * 2 + s, return_inverse=True)
            Hh2 = entropy_of(hist)
            rl += Hh2 - Hh
            Hh = Hh2
        prof.append((round(rm, 4), round(rl, 4), round(rf, 4)))
        tot["marginal"] += rm
        tot["learned"] += rl
        tot["forgotten"] += rf
    final_sorted = bool((X == np.arange(n)).all())
    return dict(G=G, H_final=Hy, H_S=Hh, sorted=final_sorted, prof=prof, **tot)


def butterfly_layers(t):
    """R_t: two copies of R_(t-1) on the low and high halves, then a layer
    comparing corresponding outputs.  Wire i meets wire i + 2^k at stage k."""
    L = []
    for k in range(t):
        step = 1 << k
        lo = np.array([i for i in range(1 << t) if not i & step], dtype=np.int64)
        L.append((lo, lo + step))
    return L


def cmd_exact(a):
    cases = []
    for n in a.ns:
        B, D = batcher(n)
        cases.append(("batcher", n, B))
        for dd in (2 * n, 3 * n):
            cases.append((f"barrier d={dd}", n, build(dd, n, "barrier")))
    for t in (2, 3):
        cases.append(("butterfly", 1 << t, butterfly_layers(t)))
    for name, n, L in cases:
        r = exact_sums(n, L)
        M, need, _ = forced(n, len(L))
        tol = 1e-8
        ident = abs(r["forgotten"] - (need - r["H_final"])) < tol
        chain = r["forgotten"] <= r["H_S"] + tol and r["H_S"] <= r["marginal"] + tol
        sorter = (not r["sorted"]) or abs(r["H_S"] - need) < tol
        ok = ident and chain and sorter and abs(r["H_S"] - r["learned"]) < tol
        print(json.dumps({"mode": "exact", "name": name, "n": n, "depth": len(L), "G": r["G"],
                          "M": M, "lg_n!": round(need, 6), "sum_marginal": round(r["marginal"], 6),
                          "sum_learned": round(r["learned"], 6),
                          "sum_forgotten": round(r["forgotten"], 6),
                          "H_final": round(r["H_final"], 6), "sorted": r["sorted"],
                          "identities_ok": ok, "by_layer(m,l,f)": r["prof"]}), flush=True)
        if not ok:
            sys.exit(1)


def cmd_blocks(a):
    """Two sorted blocks of size k, uniform interleaving, aligned layer."""
    from itertools import combinations
    from math import comb
    for k in range(1, a.kmax + 1):
        N = comb(2 * k, k)
        A = np.array(list(combinations(range(2 * k), k)), dtype=np.int16)
        mask = np.ones((N, 2 * k), bool)
        mask[np.arange(N)[:, None], A] = False
        Bv = np.nonzero(mask)[1].reshape(N, k).astype(np.int16)
        S = A > Bv
        marg = float(h2(S.mean(0)).sum())
        code = S @ (1 << np.arange(k, dtype=np.int64))
        learned = entropy_of(code)
        lo, hi = np.minimum(A, Bv), np.maximum(A, Bv)
        y = (lo.astype(np.int64) @ (2 * k) ** np.arange(k, dtype=np.int64)) if k <= 10 else None
        y2 = (hi.astype(np.int64) @ (2 * k) ** np.arange(k, dtype=np.int64)) if k <= 10 else None
        # forgotten: H(interleaving) - H(layer output)
        _, inv = np.unique(np.c_[y, y2], axis=0, return_inverse=True)
        forgot = math.log2(N) - entropy_of(inv.ravel())
        closed = 4 ** k / N - 1
        print(json.dumps({"mode": "blocks", "k": k, "gates": k, "sum_marginal": round(marg, 6),
                          "learned": round(learned, 6), "forgotten": round(forgot, 6),
                          "closed_form_4^k/C(2k,k)-1": round(closed, 6),
                          "matches_closed_form": abs(forgot - closed) < 1e-9}), flush=True)


# ---------------------------------------------------------------- sampled mode
def gate_entropy(counts, T):
    """counts: gates x cells x 2 swap counts.  Conditional entropy per gate:
    plug-in, and Miller-Madow corrected, capped at 1 bit."""
    tot = counts.sum(2)
    with np.errstate(divide="ignore", invalid="ignore"):
        p = np.where(tot > 0, counts[:, :, 1] / tot, 0.0)
    H = h2(p.ravel()).reshape(p.shape)
    plug = (H * tot).sum(1) / T
    both = (counts > 0).all(2).sum(1)
    mm = np.minimum(plug + both / (2 * T * LN2), 1.0)
    return plug, mm


def run_network(layers, n, T, seed, ctx=True, chunk=1024):
    """Forward run on T uniform permutations.  Wire-major storage (n x T)."""
    rng = np.random.default_rng(seed)
    X = np.argsort(rng.random((T, n)), axis=1).astype(np.int32).T.copy()
    c1 = np.zeros((n, T), np.uint8)          # bit of the last gate on the wire
    c2 = np.zeros((n, T), np.uint8)          # the 2 bits that fed that gate
    rows = []
    for t, (lo, hi) in enumerate(layers):
        g = lo.size
        S = X[lo] > X[hi]
        p = S.mean(1)
        marg = h2(p)
        rec = {"t": t, "G": int(g)}
        if g == 0:
            rows.append({**rec, "marg": 0.0, "marg_mm": 0.0, "ctx1": 0.0, "ctx2": 0.0,
                         "near_fair": 0, "forced": 0})
            continue
        both = ((p > 0) & (p < 1)).astype(np.float64)
        mm = np.minimum(marg + both / (2 * T * LN2), 1.0)
        rec.update(marg=float(marg.sum()), marg_mm=float(mm.sum()),
                   near_fair=int((marg >= 0.9).sum()), forced=int((marg < 0.1).sum()))
        if ctx:
            k1 = c1[lo].astype(np.int64) + 2 * c1[hi]
            k2 = k1 + 4 * c2[lo] + 16 * c2[hi]
            e1 = np.zeros(g)
            e2 = np.zeros(g)
            for s in range(0, g, chunk):
                sl = slice(s, min(s + chunk, g))
                m = S[sl].shape[0]
                base = np.arange(m, dtype=np.int64)[:, None]
                ii = (base * 8 + k1[sl] * 2 + S[sl]).ravel()
                cnt = np.bincount(ii, minlength=m * 8).reshape(m, 4, 2)
                e1[sl] = gate_entropy(cnt, T)[1]
                ii = (base * 128 + k2[sl] * 2 + S[sl]).ravel()
                cnt = np.bincount(ii, minlength=m * 128).reshape(m, 64, 2)
                e2[sl] = gate_entropy(cnt, T)[1]
            rec.update(ctx1=float(e1.sum()), ctx2=float(e2.sum()))
            nb = c1[lo].astype(np.uint8) + 2 * c1[hi]
            sb = S.astype(np.uint8)
            c1[lo], c1[hi] = sb, sb
            c2[lo], c2[hi] = nb, nb
        u, v = X[lo], X[hi]
        X[lo], X[hi] = np.minimum(u, v), np.maximum(u, v)
        rows.append(rec)
    return X, rows


def lehmer(Y):
    """Lehmer codes of the columns of Y (n x T): r_w = #{j > w : Y_j < Y_w}.
    Fenwick tree run in parallel across the T samples."""
    n, T = Y.shape
    tree = np.zeros((n + 2, T), np.int32)
    col = np.arange(T)
    out = np.empty((n, T), np.int32)
    for w in range(n - 1, -1, -1):
        v = Y[w].astype(np.int64)            # count of inserted values < v
        i = v.copy()
        c = np.zeros(T, np.int32)
        while True:
            m = i > 0
            if not m.any():
                break
            c[m] += tree[i[m], col[m]]
            i[m] -= i[m] & -i[m]
        out[w] = c
        i = v + 1
        while True:
            m = i <= n
            if not m.any():
                break
            tree[i[m], col[m]] += 1
            i[m] += i[m] & -i[m]
    return out


def sum_marginal_entropy(A, T):
    """Sum over rows of the Miller-Madow entropy of the row's empirical law."""
    plug = mmv = 0.0
    for row in A:
        _, c = np.unique(row, return_counts=True)
        q = c / T
        h = float(-(q * np.log2(q)).sum())
        plug += h
        mmv += h + (c.size - 1) / (2 * T * LN2)
    return plug, mmv


def residual(X, n, T):
    i = np.arange(n, dtype=np.int32)
    wrong = float((X != i[:, None]).sum()) / (n * T)
    exact = float((X == i[:, None]).all(0).mean())
    d_plug, d_mm = sum_marginal_entropy(X - i[:, None], T)
    l_plug, l_mm = sum_marginal_entropy(lehmer(X), T)
    return dict(exact_sorted=exact, wrong_wires=wrong, H_disp_plug=d_plug, H_disp_mm=d_mm,
                H_lehmer_plug=l_plug, H_lehmer_mm=l_mm)


def summarize(name, d, n, D, L, rows, res, T, seed, rel=None):
    M, need, fw = forced(n, D)
    G = sum(r["G"] for r in rows)
    mm = sum(r["marg_mm"] for r in rows)
    raw = sum(r["marg"] for r in rows)
    c1 = sum(r.get("ctx1", 0.0) for r in rows)
    c2 = sum(r.get("ctx2", 0.0) for r in rows)
    H_up = min(res["H_disp_mm"], res["H_lehmer_mm"]) if res else None
    out = {"mode": "screen", "sched": name, "d": d, "D": D, "n": n, "lg_n": round(math.log2(n), 3),
           "D/lg_n": round(D / math.log2(n), 3), "T": T, "seed": seed, "M": M, "G": G,
           "idle": M - G, "lg_n!": round(need, 1), "forced_waste": round(fw, 1),
           "forced_frac": round(fw / M, 4),
           "sum_H_raw": round(raw, 1), "sum_H_mm": round(mm, 1),
           "W_marg_incl_idle": round(M - mm, 1), "W_marg/M": round((M - mm) / M, 4),
           "W_gates_only": round(G - mm, 1), "W_gates/G": round((G - mm) / G, 4),
           "sum_H_ctx1": round(c1, 1), "sum_H_ctx2": round(c2, 1),
           "surplus_marg": round(mm - need, 1), "surplus_marg/need": round(mm / need - 1, 4),
           "surplus_ctx2": round(c2 - need, 1), "surplus_ctx2/need": round(c2 / need - 1, 4),
           "visible_share_of_forced": round((M - mm) / fw, 4),
           "visible_share_ctx2": round((M - c2) / fw, 4),
           "threshold_0.02nd": round(0.02 * n * d, 1)}
    if res:
        out.update({k: round(v, 5) if abs(v) < 10 else round(v, 1) for k, v in res.items()})
        out["H_final_upper_per_wire"] = round(H_up / n, 4)
        out["H_final_upper/0.02nd"] = round(H_up / (0.02 * n * d), 4)
    if rel:
        out.update(rel)
    out["stage"] = [[r["t"], r["G"], round(r["marg_mm"], 1), round(r.get("ctx1", 0.0), 1),
                     round(r.get("ctx2", 0.0), 1), r["near_fair"], r["forced"]] for r in rows]
    print(json.dumps(out), flush=True)


def cmd_screen(a):
    for d in a.depths:
        n = arity(d)
        for name in a.sched.split(","):
            K = tr_K(d) if name == "tr" else 0
            L = build(d, n, "tr", 0, "oet", K, 1.0) if name == "tr" else build(d, n, "barrier")
            rel = check_relaxations(L, n)
            X, rows = run_network(L, n, a.T, a.seed)
            res = residual(X, n, a.T)
            del X
            summarize(name, d, n, len(L), L, rows, res, a.T, a.seed,
                      {"heights_ok": rel["heights_ok"], "wire_ok": rel["wire_ok"]})


def cmd_control(a):
    for d in a.depths:
        n = arity(d)
        L, _ = batcher(n)
        D = d + 2
        if len(L) > D:
            print(json.dumps({"mode": "control", "d": d, "n": n, "batcher_depth": len(L),
                              "note": "Batcher deeper than d + 2; same-size comparison only"}),
                  flush=True)
        X, rows = run_network(L, n, a.T, a.seed)
        res = residual(X, n, a.T)
        del X
        summarize("batcher", d, n, max(D, len(L)), L, rows, res, a.T, a.seed)


def cmd_butterfly(a):
    from kahale_pair_union_rate import step_heights
    for t in a.depths:
        n = 1 << t
        L = butterfly_layers(t)
        z, o = np.zeros(n, np.int64), np.zeros(n, np.int64)
        balanced = True
        for lo, hi in L:
            balanced &= bool(np.all(z[lo] == z[hi]) and np.all(o[lo] == o[hi]))
            step_heights(z, o, lo, hi)
        _, rows = run_network(L, n, a.T, a.seed, ctx=False)
        M, need, fw = forced(n, t)
        print(json.dumps({"mode": "butterfly", "t": t, "n": n, "M": M, "G": sum(r["G"] for r in rows),
                          "equal_heights_every_gate": balanced,
                          "sum_H_raw": round(sum(r["marg"] for r in rows), 2),
                          "expected_bias": round(M / (2 * a.T * LN2), 2),
                          "sum_H_mm": round(sum(r["marg_mm"] for r in rows), 2)}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("exact")
    s.add_argument("ns", type=int, nargs="+")
    s = sub.add_parser("blocks")
    s.add_argument("--kmax", type=int, default=10)
    for name in ("screen", "control", "butterfly"):
        s = sub.add_parser(name)
        s.add_argument("depths", type=int, nargs="+")
        s.add_argument("--T", type=int, default=4096)
        s.add_argument("--seed", type=int, default=1)
        s.add_argument("--sched", default="barrier,tr")
    a = ap.parse_args()
    {"exact": cmd_exact, "blocks": cmd_blocks, "screen": cmd_screen, "control": cmd_control,
     "butterfly": cmd_butterfly}[a.mode](a)


if __name__ == "__main__":
    main()
