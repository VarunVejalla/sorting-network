"""LB-08 screen: signed quadratic cross-image witness charges at central ranks.

Family Q(n, C), for a set C of ranks (output Hamming weights):

    Phi(R) = sum w_pq F_p(R) F_q(R),   p, q rank-specific inversion witnesses,
             rank(p), rank(q) in C,  |rank(p) - rank(q)| <= 1,  w_pq signed,

where F_(k,a,b)(R) = 1 iff some x in R has weight k, x_a = 1, x_b = 0, a < b.
Requirement: Phi(R) - Phi(L(R)) <= 1 for every reachable image R and every
parallel layer L of ascending comparators.  Phi(sorted) = 0 holds automatically.
Value V(n, C) = max Phi(cube).

Images are bitmasks over {0,1}^n stored as (lo, hi) uint64 pairs (n <= 7).
"""
import argparse
import json
import sys
import time
from fractions import Fraction
from itertools import combinations
from math import isqrt

import numpy as np
import scipy.sparse as sp

KNOWN_D = {1: 0, 2: 1, 3: 3, 4: 3, 5: 5, 6: 5, 7: 6, 8: 6, 9: 7, 10: 7, 11: 8, 12: 8, 16: 9}


# ---------------------------------------------------------------- catalogue

def point_mask(n, pred):
    lo = hi = 0
    for x in range(1 << n):
        if pred(x):
            if x < 64:
                lo |= 1 << x
            else:
                hi |= 1 << (x - 64)
    return lo, hi


def apply_comparator(n, img, a, b, cache={}):
    """img: (m, 2) uint64 array. Comparator (a, b): min to a, max to b."""
    key = (n, a, b)
    if key not in cache:
        ml, mh = point_mask(n, lambda x: (x >> a) & 1 and not (x >> b) & 1)
        cache[key] = np.uint64(ml), np.uint64(mh), (1 << b) - (1 << a)
    ml, mh, s = cache[key]
    lo, hi = img[:, 0], img[:, 1]
    mvl, mvh = lo & ml, hi & mh
    nl, nh = lo & ~ml, hi & ~mh
    if s < 64:
        nl = nl | (mvl << np.uint64(s))
        nh = nh | (mvh << np.uint64(s)) | (mvl >> np.uint64(64 - s))
    elif s == 64:
        nh = nh | mvl
    else:
        nh = nh | (mvl << np.uint64(s - 64))
    return np.stack([nl, nh], 1)


def unique_rows(a):
    return np.unique(a, axis=0)


def catalogue(n):
    """All images reachable by ascending comparators, and the successor table."""
    full = point_mask(n, lambda x: True)
    seen = np.array([full], dtype=np.uint64)
    frontier = seen
    comps = list(combinations(range(n), 2))
    while len(frontier):
        cat = unique_rows(np.concatenate([apply_comparator(n, frontier, a, b) for a, b in comps]))
        both = np.concatenate([seen, cat])
        u, idx = np.unique(both, axis=0, return_index=True)
        frontier = u[idx >= len(seen)]
        seen = u
    return seen


def index_of(images, query):
    """Row lookup in the lexicographically sorted (lo, hi) table."""
    # np.unique(axis=0) sorts by column 0 then column 1.
    lo = images[:, 0]
    start = np.searchsorted(lo, query[:, 0], side="left")
    end = np.searchsorted(lo, query[:, 0], side="right")
    out = start.copy()
    todo = np.nonzero(end - start > 1)[0]
    # Binary search inside the groups with more than one hi value.
    a, b = start[todo].copy(), end[todo].copy()
    q = query[todo, 1]
    hi = images[:, 1]
    while len(todo) and (b - a > 1).any():
        mid = (a + b) // 2
        left = hi[mid] <= q
        a = np.where(left, mid, a)
        b = np.where(left, b, mid)
    out[todo] = a
    assert (images[out] == query).all()
    return out


def successor_table(n, images):
    comps = list(combinations(range(n), 2))
    succ = np.empty((len(images), len(comps)), dtype=np.int32)
    for j, (a, b) in enumerate(comps):
        succ[:, j] = index_of(images, apply_comparator(n, images, a, b))
    return comps, succ


def matchings(n):
    """All nonempty parallel layers as tuples of comparator pairs."""
    out = []

    def rec(free, cur):
        if not free:
            if cur:
                out.append(tuple(cur))
            return
        a = free[0]
        rest = free[1:]
        rec(rest, cur)
        for i, b in enumerate(rest):
            rec(rest[:i] + rest[i + 1:], cur + [(a, b)])

    rec(list(range(n)), [])
    return out


# ---------------------------------------------------------------- features

def base_features(n, ranks):
    return [(k, a, b) for k in sorted(ranks) for a, b in combinations(range(n), 2)
            if 1 <= k <= n - 1]


def signatures(n, images, base):
    """Boolean matrix images x base features."""
    F = np.zeros((len(images), len(base)), dtype=bool)
    for j, (k, a, b) in enumerate(base):
        ml, mh = point_mask(n, lambda x: x.bit_count() == k and (x >> a) & 1 and not (x >> b) & 1)
        F[:, j] = ((images[:, 0] & np.uint64(ml)) | (images[:, 1] & np.uint64(mh))) != 0
    return F


def quotient(F):
    """Unique signatures and the signature id of each image."""
    packed = np.packbits(F, axis=1)
    key = np.frombuffer(packed.tobytes(), dtype=np.dtype((np.void, packed.shape[1])))
    _, first, sid = np.unique(key, return_index=True, return_inverse=True)
    return F[first], sid


def layer_targets(succ, comps, layer, ids=None):
    pos = {c: j for j, c in enumerate(comps)}
    cur = np.arange(len(succ)) if ids is None else ids
    for c in layer:
        cur = succ[cur, pos[c]]
    return cur


def quad_columns(base, adjacent=True):
    """Index pairs i <= j of base features with rank separation <= 1."""
    pairs = []
    for i in range(len(base)):
        for j in range(i, len(base)):
            if not adjacent or abs(base[i][0] - base[j][0]) <= 1:
                pairs.append((i, j))
    return pairs


def rank_sets(n):
    """Central rank windows, widest last."""
    out = []
    for w in range(0, n):
        c = [k for k in range(1, n) if abs(2 * k - n) <= 2 * w + (n % 2)]
        if c and (not out or c != out[-1]):
            out.append(c)
    return out


class Graph:
    """Complete image catalogue of n wires with successors and BFS parents."""

    def __init__(self, n):
        self.n = n
        self.images = catalogue(n)
        self.comps, self.succ = successor_table(n, self.images)
        self.layers = matchings(n)
        start = np.array([point_mask(n, lambda x: True)], dtype=np.uint64)
        self.i0 = int(index_of(self.images, start)[0])
        m = len(self.images)
        self.parent = np.full(m, -1, dtype=np.int32)
        self.via = np.full(m, -1, dtype=np.int8)
        self.parent[self.i0] = self.i0
        frontier = np.array([self.i0])
        while len(frontier):
            new = []
            for j in range(len(self.comps)):
                t = self.succ[frontier, j]
                fresh = self.parent[t] < 0
                self.parent[t[fresh]] = frontier[fresh]
                self.via[t[fresh]] = j
                new.append(t[fresh])
            frontier = np.unique(np.concatenate(new))

    def prefix(self, i):
        """Comparator prefix (one comparator per layer) reaching image i."""
        out = []
        while i != self.i0:
            out.append(list(self.comps[self.via[i]]))
            i = int(self.parent[i])
        return out[::-1]


def separate(g, F, W, tol, per_layer=40):
    """Most violated layer rows for the quadratic form W (symmetric-free dense)."""
    n_img = len(F)
    phi = np.empty(n_img)
    Ff = None
    for lo in range(0, n_img, 200000):
        Ff = F[lo:lo + 200000].astype(np.float64)
        phi[lo:lo + 200000] = ((Ff @ W) * Ff).sum(1)
    worst, cuts = -np.inf, []
    for layer in g.layers:
        tgt = layer_targets(g.succ, g.comps, layer)
        drop = phi - phi[tgt]
        m = float(drop.max())
        worst = max(worst, m)
        if m > 1 + tol:
            k = min(per_layer, n_img - 1)
            top = np.argpartition(-drop, k)[:k]
            for i in top[drop[top] > 1 + tol]:
                cuts.append((int(i), int(tgt[i])))
    return phi, worst, cuts


def quotient_bfs(g, sid, goal):
    """Shortest path to the goal signature in the signature quotient.

    Returns (length, steps); each step (image, layer index, target image) is a
    real layer on a real image, and consecutive steps are joined by equal
    signature. The length bounds the range of EVERY function of the signature.
    """
    S = int(sid.max()) + 1
    seen = np.zeros(S, dtype=bool)
    from_img = np.full(S, -1, dtype=np.int32)
    from_tgt = np.full(S, -1, dtype=np.int32)
    from_layer = np.full(S, -1, dtype=np.int32)
    start = int(sid[g.i0])
    seen[start] = True
    frontier = np.zeros(S, dtype=bool)
    frontier[start] = True
    d = 0
    while not seen[goal]:
        d += 1
        ids = np.nonzero(frontier[sid])[0]
        if not len(ids):
            return None, None
        next_frontier = np.zeros(len(seen), dtype=bool)
        for li, layer in enumerate(g.layers):
            tgt = layer_targets(g.succ, g.comps, layer, ids)
            st = sid[tgt]
            mask = ~seen[st]
            if mask.any():
                u, first = np.unique(st[mask], return_index=True)
                seen[u] = True
                next_frontier[u] = True
                from_img[u] = ids[mask][first]
                from_tgt[u] = tgt[mask][first]
                from_layer[u] = li
        frontier = next_frontier
    path, cur = [], goal
    while cur != start:
        path.append((int(from_img[cur]), int(from_layer[cur]), int(from_tgt[cur])))
        cur = int(sid[from_img[cur]])
    return d, path[::-1]


def merged_pairs(F, pairs, seed=7):
    """Group quadratic columns that agree on all images; drop all-zero columns.

    Uses a random linear hash. A false merge could only shrink the family; the
    independent checker works on raw columns, so it would be caught there.
    """
    rng = np.random.default_rng(seed)
    r1, r2 = rng.random(len(F)), rng.random(len(F))
    m = F.shape[1]
    H1, H2 = np.zeros((m, m)), np.zeros((m, m))
    for lo in range(0, len(F), 200000):
        X = F[lo:lo + 200000].astype(np.float64)
        H1 += X.T @ (X * r1[lo:lo + 200000, None])
        H2 += X.T @ (X * r2[lo:lo + 200000, None])
    groups = {}
    for i, j in pairs:
        if H1[i, j] == 0:
            continue
        groups.setdefault((round(H1[i, j], 5), round(H2[i, j], 5)), []).append((i, j))
    return [v[0] for v in groups.values()], {v[0]: v for v in groups.values()}


def reflection_orbits(n, base, pairs, groups):
    """Orbits of merged columns under wire reversal + complement.

    (k, a, b) -> (n-k, n-1-b, n-1-a) maps reachable images to reachable images,
    so an averaged optimal charge is reflection invariant.
    """
    idx = {f: i for i, f in enumerate(base)}
    ref = [idx[(n - k, n - 1 - b, n - 1 - a)] for k, a, b in base]
    owner = {}
    for rep_, members in groups.items():
        for m in members:
            owner[m] = rep_
    pos = {p: i for i, p in enumerate(pairs)}
    orbit = [-1] * len(pairs)
    count = 0
    for i, (a, b) in enumerate(pairs):
        if orbit[i] >= 0:
            continue
        ra, rb = sorted((ref[a], ref[b]))
        j = pos[owner[(ra, rb)]]
        orbit[i] = count
        orbit[j] = count
        count += 1
    return np.array(orbit), count


def cp_highs(g, C, adjacent=True, signed=True, box=1024.0, tol=1e-7, seed_rows=4000, log=print,
             max_rows_round=5000, stop_below=None, max_seconds=3600, symmetric=True):
    """Constraint generation with warm-started dual simplex over all (image, layer)."""
    import highspy
    n = g.n
    t0 = time.time()
    base = base_features(n, C)
    F = signatures(n, g.images, base)
    raw = quad_columns(base, adjacent)
    pairs, groups = merged_pairs(F, raw)
    I = np.array([p[0] for p in pairs])
    J = np.array([p[1] for p in pairs])
    ncol = len(pairs)
    log(f"  base={len(base)} raw_cols={len(raw)} merged={ncol}")
    c = (F[g.i0, I] & F[g.i0, J]).astype(float)
    if symmetric:
        orbit, norb = reflection_orbits(n, base, pairs, groups)
    else:
        orbit, norb = np.arange(ncol), ncol
    O = sp.csr_matrix((np.ones(ncol), (np.arange(ncol), orbit)), shape=(ncol, norb))
    c_orb = O.T @ c
    log(f"  orbits={norb}")
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("threads", 2)
    h.setOptionValue("solver", "simplex")
    inf = highspy.kHighsInf
    lb = -box if signed else 0.0
    for j in range(norb):
        h.addVar(lb, box)
        h.changeColCost(j, -float(c_orb[j]))
    rng = np.random.default_rng(1)
    rows, seen, active = [], set(), []
    for layer in g.layers:
        ids = rng.integers(0, len(g.images), max(1, seed_rows // len(g.layers)))
        tgt = layer_targets(g.succ, g.comps, layer, ids)
        rows += [(int(a), int(b)) for a, b in zip(ids, tgt)]
    rnd, freed = 0, False
    while True:
        fresh = []
        for r in rows:
            if r in seen:
                continue
            seen.add(r)
            if (F[r[0]] != F[r[1]]).any():
                fresh.append(r)
        if fresh:
            s = np.array([a for a, b in fresh])
            t = np.array([b for a, b in fresh])
            D = sp.csr_matrix((F[s][:, I] & F[s][:, J]).astype(np.int8), dtype=np.int32)                 - sp.csr_matrix((F[t][:, I] & F[t][:, J]).astype(np.int8), dtype=np.int32)
            D = (D @ O.astype(np.int32)).tocsr()
            D.eliminate_zeros()
            for k, r in enumerate(fresh):
                lo, hi = D.indptr[k], D.indptr[k + 1]
                if hi > lo:
                    h.addRow(-inf, 1.0, int(hi - lo), D.indices[lo:hi].astype(np.int32), D.data[lo:hi].astype(float))
                    active.append(r)
        h.run()
        status = h.getModelStatus()
        if status != highspy.HighsModelStatus.kOptimal:
            raise RuntimeError(h.modelStatusToString(status))
        sol = h.getSolution()
        w_orb = np.array(sol.col_value)
        w = O @ w_orb
        value = float(c @ w)
        W = np.zeros((len(base), len(base)))
        W[I, J] = w
        phi, worst, cuts = separate(g, F, W, tol)
        cuts = list(dict.fromkeys(cuts))
        if len(cuts) > max_rows_round:
            pick = rng.choice(len(cuts), max_rows_round, replace=False)
            cuts = [cuts[i] for i in pick]
        binding = int((np.abs(w) > box - 1e-7).sum())
        log(f"  round {rnd} rows={len(active)} value={value:.8f} worst={worst:.6f} cuts={len(cuts)} "
            f"box={binding} status={h.modelStatusToString(status)} t={time.time()-t0:.0f}")
        rnd += 1
        done = not cuts
        if done and binding and not freed:
            # Remove the temporary box: the certificate must hold for free weights.
            freed, done = True, False
            for j in range(norb):
                h.changeColBounds(j, -inf if signed else 0.0, inf)
            rows = []
            box = float("inf")
            continue
        if done or (stop_below is not None and value <= stop_below and binding == 0) or time.time() - t0 > max_seconds:
            break
        rows = cuts
    y = np.array(sol.row_dual)
    return dict(base=base, pairs=pairs, groups=groups, F=F, c=c, active=active, w=w, y=y, value=value,
                worst=worst, converged=done, box_binding=binding, O=O, c_orb=c_orb)


def mosek_lp(A, c, box, threads=3):
    """max c w, A w <= 1, by interior point with basis identification."""
    import mosek
    A = A.tocsc()
    m, k = A.shape
    with mosek.Env() as env, env.Task() as t:
        t.putintparam(mosek.iparam.num_threads, threads)
        t.putintparam(mosek.iparam.optimizer, mosek.optimizertype.intpnt)
        t.putintparam(mosek.iparam.intpnt_basis, mosek.basindtype.always)
        t.appendvars(k)
        t.appendcons(m)
        t.putobjsense(mosek.objsense.maximize)
        t.putclist(list(range(k)), c.tolist())
        for j in range(k):
            lo, hi = A.indptr[j], A.indptr[j + 1]
            if hi > lo:
                t.putacol(j, A.indices[lo:hi].tolist(), A.data[lo:hi].tolist())
        if box is None:
            t.putvarboundsliceconst(0, k, mosek.boundkey.fr, 0.0, 0.0)
        else:
            t.putvarboundsliceconst(0, k, mosek.boundkey.ra, -box, box)
        t.putconboundsliceconst(0, m, mosek.boundkey.up, 0.0, 1.0)
        t.optimize()
        if t.getsolsta(mosek.soltype.bas) != mosek.solsta.optimal:
            raise RuntimeError(str(t.getsolsta(mosek.soltype.bas)))
        return np.array(t.getxx(mosek.soltype.bas)), np.array(t.getsuc(mosek.soltype.bas))


def cp_mosek(g, C, box=1024.0, per_round=4000, log=print, max_seconds=4000):
    """Constraint generation for n = 7: simplex re-solves are too slow there."""
    n = g.n
    t0 = time.time()
    base = base_features(n, C)
    F = signatures(n, g.images, base)
    pairs, groups = merged_pairs(F, quad_columns(base))
    I = np.array([p[0] for p in pairs])
    J = np.array([p[1] for p in pairs])
    c = (F[g.i0, I] & F[g.i0, J]).astype(float)
    orbit, norb = reflection_orbits(n, base, pairs, groups)
    O = sp.csr_matrix((np.ones(len(pairs)), (np.arange(len(pairs)), orbit)), shape=(len(pairs), norb))
    c_orb = O.T @ c
    log(f"  merged={len(pairs)} orbits={norb}")
    rng = np.random.default_rng(1)
    rows = []
    for layer in g.layers:
        ids = rng.integers(0, len(g.images), 20)
        rows += [(int(a), int(b)) for a, b in zip(ids, layer_targets(g.succ, g.comps, layer, ids))]
    seen, active, A = set(), [], None
    freed, rnd, done = False, 0, False
    while True:
        fresh = []
        for r in rows:
            if r not in seen:
                seen.add(r)
                if (F[r[0]] != F[r[1]]).any():
                    fresh.append(r)
        if fresh:
            s = np.array([a for a, b in fresh])
            t = np.array([b for a, b in fresh])
            D = sp.csr_matrix((F[s][:, I] & F[s][:, J]).astype(np.float64)) \
                - sp.csr_matrix((F[t][:, I] & F[t][:, J]).astype(np.float64))
            active += fresh
            A = (D @ O).tocsr() if A is None else sp.vstack([A, (D @ O).tocsr()], format="csr")
        wo, y = mosek_lp(A, c_orb, None if freed else box)
        w = O @ wo
        value = float(c_orb @ wo)
        W = np.zeros((len(base), len(base)))
        W[I, J] = w
        _, worst, cuts = separate(g, F, W, 2e-6, per_layer=20)
        cuts = list(dict.fromkeys(cuts))
        if len(cuts) > per_round:
            cuts = [cuts[i] for i in rng.choice(len(cuts), per_round, replace=False)]
        binding = 0 if freed else int((np.abs(wo) > box - 1e-6).sum())
        log(f"  round {rnd} rows={A.shape[0]} value={value:.8f} worst={worst:.6f} cuts={len(cuts)} box={binding} t={time.time()-t0:.0f}")
        rnd += 1
        if not cuts:
            if binding and not freed:
                freed, rows = True, []
                continue
            done = True
            break
        if time.time() - t0 > max_seconds:
            break
        rows = cuts
    return dict(base=base, pairs=pairs, groups=groups, F=F, c=c, active=active, w=w, y=y, value=value,
                worst=worst, converged=done, box_binding=binding, O=O, c_orb=c_orb)


# ---------------------------------------------------------------- exact solve

P = 8388593  # prime just below 2^23: sums of 2^12 products stay inside int64


def rational_reconstruct(a, mod):
    bound = isqrt(mod // 2)
    r0, r1, s0, s1 = mod, a % mod, 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1)


def gauss_inverse(B):
    k = len(B)
    aug = np.concatenate([np.mod(B, P), np.eye(k, dtype=np.int64)], axis=1)
    for col in range(k):
        piv = col + int(np.nonzero(aug[col:, col])[0][0])
        if piv != col:
            aug[[col, piv]] = aug[[piv, col]]
        aug[col] = (aug[col] * pow(int(aug[col, col]), P - 2, P)) % P
        f = aug[:, col].copy()
        f[col] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            aug[nz] = (aug[nz] - (f[nz, None] * aug[col]) % P) % P
    return aug[:, k:]


def solve_exact(M, b):
    """Exact rational solution of M x = b, M integer (rows >= cols), full column rank.

    Dixon p-adic lifting on a nonsingular square block chosen mod P; every
    equation of the original system is then verified in integers.
    """
    M = np.asarray(M, dtype=np.int64)
    m, k = M.shape
    rows_left = np.ones(m, dtype=bool)
    W = np.mod(M, P)
    perm = []
    for col in range(k):
        cand = np.nonzero(rows_left & (W[:, col] != 0))[0]
        if not len(cand):
            raise ValueError("column rank deficient mod P")
        r = int(cand[0])
        rows_left[r] = False
        perm.append(r)
        W[r] = (W[r] * pow(int(W[r, col]), P - 2, P)) % P
        f = W[:, col].copy()
        f[r] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            W[nz] = (W[nz] - (f[nz, None] * W[r]) % P) % P
    B = M[perm]
    Binv = gauss_inverse(B)
    r = np.array([int(b[i]) for i in perm], dtype=np.int64)
    total = [0] * k
    mod, step = 1, 0
    while step < 4000:
        x = (Binv @ (r % P)) % P
        r = r - B @ x
        assert not (r % P).any()
        r //= P
        total = [t + int(v) * mod for t, v in zip(total, x)]
        mod *= P
        step += 1
        if step % 8:
            continue
        den, ok = 1, True
        for v in total:
            f = rational_reconstruct(v * den % mod, mod)
            if f is None:
                ok = False
                break
            den *= f.denominator
        if not ok:
            continue
        ints = []
        for v in total:
            u = v * den % mod
            ints.append(u - mod if u > mod // 2 else u)
        res = [sum(int(a) * q for a, q in zip(row, ints) if a) for row in M.tolist()]
        if all(rr == int(b[i]) * den for i, rr in enumerate(res)):
            return [Fraction(u, den) for u in ints]
    raise ValueError("lifting did not terminate")


def exact_dual(g, res):
    """Exact dual multipliers on the support of the LP dual."""
    pairs, F = res["pairs"], res["F"]
    I = np.array([p[0] for p in pairs])
    J = np.array([p[1] for p in pairs])
    supp = np.nonzero(np.abs(res["y"]) > 1e-9)[0]
    rows = [res["active"][i] for i in supp]
    s = np.array([a for a, b in rows])
    t = np.array([b for a, b in rows])
    A = (F[s][:, I] & F[s][:, J]).astype(np.int64) - (F[t][:, I] & F[t][:, J]).astype(np.int64)
    O = res["O"].astype(np.int64)
    A = A @ O.toarray()
    return rows, solve_exact(A.T, res["c_orb"].astype(np.int64).tolist())


def certificate(g, res, rows, ex):
    """Rows plus their reflections at half weight (the LP used reflection orbits)."""
    n = g.n
    refl = lambda cs: [[n - 1 - b, n - 1 - a] for a, b in cs]
    entries = []
    for (a, b), v in zip(rows, ex):
        if v == 0:
            continue
        layer = next(ly for ly in g.layers
                     if int(layer_targets(g.succ, g.comps, ly, np.array([a]))[0]) == b)
        pre, ly = g.prefix(a), [list(c) for c in layer]
        entries.append(dict(prefix=pre, layer=ly, y=str(v / 2)))
        entries.append(dict(prefix=refl(pre), layer=refl(ly), y=str(v / 2)))
    return dict(n=n, ranks=sorted({k for k, _, _ in res["base"]}), rank_separation=1,
                value=str(sum(ex)), rows=entries)


# ---------------------------------------------------------------- sampled upper bounds, n >= 8

class WordImages:
    """Images on any n as (m, words) uint64 arrays. Only relaxations use this:
    a sampled set of true (prefix, layer) rows gives an UPPER bound on V(n, C)."""

    def __init__(self, n):
        self.n, self.words = n, max(1, (1 << n) // 64)
        self.mv = {}
        for a, b in combinations(range(n), 2):
            self.mv[a, b] = (self.mask(lambda x: (x >> a) & 1 and not (x >> b) & 1), (1 << b) - (1 << a))

    def mask(self, pred):
        out = [0] * self.words
        for x in range(1 << self.n):
            if pred(x):
                out[x // 64] |= 1 << (x % 64)
        return np.array(out, dtype=np.uint64)

    def full(self):
        return self.mask(lambda x: True)[None, :]

    def comparator(self, img, a, b):
        m, sh = self.mv[a, b]
        hit = img & m
        out = img & ~m
        ws, bs = sh // 64, sh % 64
        for w in range(self.words - ws):
            out[:, w + ws] |= hit[:, w] << np.uint64(bs)
            if bs and w + ws + 1 < self.words:
                out[:, w + ws + 1] |= hit[:, w] >> np.uint64(64 - bs)
        return out

    def layer(self, img, layer):
        for a, b in layer:
            img = self.comparator(img, a, b)
        return img

    def features(self, img, base):
        F = np.zeros((len(img), len(base)), dtype=bool)
        for j, (k, a, b) in enumerate(base):
            m = self.mask(lambda x: x.bit_count() == k and (x >> a) & 1 and not (x >> b) & 1)
            F[:, j] = (img & m).any(1)
        return F

    def points(self, one):
        return np.array([x for x in range(1 << self.n) if (int(one[x // 64]) >> (x % 64)) & 1], dtype=np.int64)


def walk_pool(W, rng, walks, layer_cap=16):
    """Trajectories: some random layers, then inversion-biased layers, until sorted."""
    n = W.n
    imgs, prefixes = [], []
    for _ in range(walks):
        cur = W.full()
        pre = []
        rand_steps = int(rng.integers(0, 6))
        for step in range(layer_cap):
            pts = W.points(cur[0])
            if not len(unsorted_points(n, pts)):
                break
            imgs.append(cur)
            prefixes.append(list(pre))
            if step < rand_steps:
                wires = rng.permutation(n)
                layer = tuple(sorted(tuple(sorted((int(wires[i]), int(wires[i + 1])))) for i in range(0, n - 1, 2)))
            else:
                layer = propose_layers(n, pts, rng, 1)[0]
            cur = W.layer(cur, layer)
            pre.append(layer)
    return np.concatenate(imgs), prefixes


def sampled_bound(n, C, rounds=30, walks=300, trials=4, box=256.0, log=print, seed=3, max_seconds=2400):
    """Upper bound on V(n, C) by constraint generation over sampled true rows."""
    import highspy
    t0 = time.time()
    rng = np.random.default_rng(seed)
    W = WordImages(n)
    base = base_features(n, C)
    idx = {f: i for i, f in enumerate(base)}
    raw = quad_columns(base)
    pos = {p: i for i, p in enumerate(raw)}
    I = np.array([p[0] for p in raw])
    J = np.array([p[1] for p in raw])
    orbit, count = {}, 0
    for t, (a, b) in enumerate(raw):
        if t in orbit:
            continue
        ka, x, y = base[a]
        kb, u, v = base[b]
        ra, rb = sorted((idx[(n - ka, n - 1 - y, n - 1 - x)], idx[(n - kb, n - 1 - v, n - 1 - u)]))
        orbit[t] = count
        orbit[pos[(ra, rb)]] = count
        count += 1
    O = sp.csr_matrix((np.ones(len(raw)), (np.arange(len(raw)), [orbit[t] for t in range(len(raw))])),
                      shape=(len(raw), count))
    c = W.features(W.full(), base)[0]
    c_orb = O.T @ (c[I] & c[J]).astype(float)
    log(f"  base={len(base)} raw={len(raw)} orbits={count}")
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("threads", 1)
    h.setOptionValue("solver", "simplex")
    inf = highspy.kHighsInf
    for j in range(count):
        h.addVar(-box, box)
        h.changeColCost(j, -float(c_orb[j]))
    rows, seen = [], set()
    w = np.zeros(len(raw))

    def add_rows(Fs, Ft, meta):
        D = sp.csr_matrix((Fs[:, I] & Fs[:, J]).astype(np.int8), dtype=np.int32) \
            - sp.csr_matrix((Ft[:, I] & Ft[:, J]).astype(np.int8), dtype=np.int32)
        D = (D @ O.astype(np.int32)).tocsr()
        D.eliminate_zeros()
        added = 0
        for k in range(D.shape[0]):
            lo, hi = D.indptr[k], D.indptr[k + 1]
            if hi == lo:
                continue
            key = D.indices[lo:hi].tobytes() + D.data[lo:hi].tobytes()
            if key in seen:
                continue
            seen.add(key)
            h.addRow(-inf, 1.0, int(hi - lo), D.indices[lo:hi].astype(np.int32), D.data[lo:hi].astype(float))
            rows.append(meta[k])
            added += 1
        return added

    value = binding = None
    for rnd in range(rounds):
        imgs, prefixes = walk_pool(W, rng, walks)
        Fs = W.features(imgs, base)
        Mat = np.zeros((len(base), len(base)))
        Mat[I, J] = w
        phis = ((Fs.astype(float) @ Mat) * Fs).sum(1)
        cand_s, cand_t, meta = [], [], []
        picks = rng.choice(len(imgs), 30 * trials)
        for i in picks:
            ly = propose_layers(n, W.points(imgs[i]), rng, 1)
            if not ly:
                continue
            tgt = W.layer(imgs.copy(), ly[0])
            Ft = W.features(tgt, base)
            drop = phis - ((Ft.astype(float) @ Mat) * Ft).sum(1)
            top = np.argsort(-drop)[:30]
            top = top[drop[top] > 1 + 1e-7] if rnd else top
            if len(top):
                cand_s.append(Fs[top])
                cand_t.append(Ft[top])
                meta += [(prefixes[t], ly[0]) for t in top]
        added = add_rows(np.concatenate(cand_s), np.concatenate(cand_t), meta) if cand_s else 0
        h.run()
        status = h.getModelStatus()
        if status != highspy.HighsModelStatus.kOptimal:
            raise RuntimeError(h.modelStatusToString(status))
        sol = h.getSolution()
        wo = np.array(sol.col_value)
        w = O @ wo
        value = float(c_orb @ wo)
        binding = int((np.abs(wo) > box - 1e-7).sum())
        log(f"  round {rnd} rows={len(rows)} added={added} value={value:.6f} box={binding} t={time.time()-t0:.0f}")
        if time.time() - t0 > max_seconds:
            break
    return dict(value=value, binding=binding, rows=rows, y=np.array(sol.row_dual), W=W, base=base, raw=raw,
                orbit=O, c_orb=c_orb)


# ---------------------------------------------------------------- slice sorters

def slice_points(n, C):
    pts = [x for x in range(1 << n) if x.bit_count() in C]
    return np.array(pts, dtype=np.int64)


def apply_layer_points(pts, layer):
    p = pts.copy()
    for a, b in layer:
        hit = ((p >> a) & 1 == 1) & ((p >> b) & 1 == 0)
        p[hit] ^= (1 << a) | (1 << b)
    return np.unique(p)


def unsorted_points(n, pts):
    srt = np.array([((1 << n) - 1) ^ ((1 << (n - int(k))) - 1) for k in range(n + 1)], dtype=np.int64)
    pc = np.array([int(x).bit_count() for x in pts])
    return pts[pts != srt[pc]]


def propose_layers(n, pts, rng, count):
    """Random greedy matchings biased to comparators with many inversions."""
    bad = unsorted_points(n, pts)
    bits = ((bad[:, None] >> np.arange(n)) & 1).astype(np.int32)
    M = bits.T @ (1 - bits)
    out = []
    for _ in range(count):
        score = np.triu(M, 1) * rng.random((n, n)) ** rng.choice([0.5, 2.0, 6.0])
        order = np.argsort(-score, axis=None)
        used, layer = set(), []
        for v in order[:n * n]:
            a, b = divmod(int(v), n)
            if score[a, b] <= 0 or a in used or b in used:
                continue
            used |= {a, b}
            layer.append((a, b))
        if layer:
            out.append(tuple(sorted(layer)))
    return list(dict.fromkeys(out))


def slice_beam(n, C, width=64, cand=24, depth_cap=12, seed=1):
    """Heuristic search for a shallow network sorting every input of weight in C."""
    rng = np.random.default_rng(seed)
    start = tuple((i, i + 1) for i in range(0, n - 1, 2))
    beam = [(apply_layer_points(slice_points(n, C), start), [start])]
    for d in range(1, depth_cap + 1):
        for pts, net in beam:
            if not len(unsorted_points(n, pts)):
                return net
        nxt = {}
        for pts, net in beam:
            for layer in propose_layers(n, pts, rng, cand):
                q = apply_layer_points(pts, layer)
                bad = unsorted_points(n, q)
                nxt.setdefault(q.tobytes(), (len(bad), rng.random(), q, net + [layer]))
        ranked = sorted(nxt.values(), key=lambda t: t[:2])[:width]
        beam = [(t[2], t[3]) for t in ranked]
    return None


def path_certificate(g, C, path):
    steps = []
    for image, li, _ in path:
        steps.append(dict(prefix=g.prefix(image), layer=[list(c) for c in g.layers[li]]))
    return dict(kind="path", n=g.n, ranks=C, claimed_bound=len(path), steps=steps)


def slice_depth(g, C):
    """Exact minimum depth of a network sorting every input of weight in C."""
    n = g.n
    ml, mh = point_mask(n, lambda x: x.bit_count() in C)
    key = np.stack([g.images[:, 0] & np.uint64(ml), g.images[:, 1] & np.uint64(mh)], 1)
    u, sid = np.unique(key, axis=0, return_inverse=True)
    pts = [((1 << n) - 1) ^ ((1 << (n - k)) - 1) for k in C]
    lo = sum(1 << p for p in pts if p < 64)
    hi = sum(1 << (p - 64) for p in pts if p >= 64)
    goal = int(np.nonzero((u[:, 0] == np.uint64(lo)) & (u[:, 1] == np.uint64(hi)))[0][0])
    return quotient_bfs(g, sid.ravel(), goal)


def dyadic_potential(res):
    """Round the LP charge to dyadic weights; the exact claim is start/worst drop."""
    pairs, base, w = res["pairs"], res["base"], res["w"]
    terms = []
    for (i, j), v in zip(pairs, w):
        v = Fraction(round(float(v) * 2 ** 24), 2 ** 24)
        if v:
            terms.append([list(base[i]), list(base[j]), str(v)])
    return terms


def exact_check_potential(g, res, terms):
    F = res["F"]
    den = 2 ** 24
    idx = {f: i for i, f in enumerate(res["base"])}
    I = np.array([idx[tuple(p)] for p, q, v in terms])
    J = np.array([idx[tuple(q)] for p, q, v in terms])
    val = np.array([int(Fraction(v) * den) for p, q, v in terms], dtype=np.int64)
    sigs, sid = quotient(F)
    phi = (sigs[:, I] & sigs[:, J]).astype(np.int64) @ val
    worst = 0
    for layer in g.layers:
        worst = max(worst, int((phi[sid] - phi[sid[layer_targets(g.succ, g.comps, layer)]]).max()))
    return Fraction(int(phi[sid[g.i0]]), den), Fraction(worst, den)


def half_cleaner_selector(m, sorter):
    """Sort each half, then the mirror layer: sorts every input of weight m on 2m wires."""
    high = [[(a + m, b + m) for a, b in ly] for ly in sorter]
    net = [list(x) + list(y) for x, y in zip(sorter, high)]
    net.append([(a, 2 * m - 1 - a) for a in range(m)])
    return net


BATCHER_8 = [[(0, 1), (2, 3), (4, 5), (6, 7)], [(0, 2), (1, 3), (4, 6), (5, 7)], [(1, 2), (5, 6)],
             [(0, 4), (1, 5), (2, 6), (3, 7)], [(2, 4), (3, 5)], [(1, 2), (3, 4), (5, 6)]]


def main(args):
    out = open(args.output, "a" if args.resume else "w", encoding="utf-8")

    def log(*a):
        line = " ".join(str(x) for x in a)
        print(line, flush=True)
        out.write(line + "\n")
        out.flush()

    certs = {}
    if args.resume and args.certs:
        with open(args.certs, encoding="utf-8") as handle:
            certs = json.load(handle)["certificates"]

    def save():
        with open(args.certs, "w", encoding="utf-8") as handle:
            json.dump(dict(note="LB-08 certificates; check with kahale_signed_charge_check.py",
                           certificates=certs), handle)

    for n in args.wires:
        t0 = time.time()
        g = Graph(n)
        log(f"== n={n} images={len(g.images)} layers={len(g.layers)} D={KNOWN_D[n]} needs value > {KNOWN_D[n]-1}")
        for C in rank_sets(n):
            base = base_features(n, C)
            sigs, sid = quotient(signatures(n, g.images, base))
            zero = int(np.nonzero(~sigs.any(1))[0][0])
            q, path = quotient_bfs(g, sid, zero)
            dc, _ = slice_depth(g, C)
            log(f"n={n} ranks={C} signatures={len(sigs)} quotient_distance={q} slice_sort_depth={dc} t={time.time()-t0:.0f}")
            certs[f"path_{n}_{C}"] = path_certificate(g, C, path)
            if n in args.lp_wires and (n, len(C)) not in args.skip:
                solve = cp_mosek if args.solver == "mosek" else cp_highs
                r = solve(g, C, log=lambda m: print(m, flush=True), max_seconds=args.lp_seconds)
                log(f"n={n} ranks={C} LP value={r['value']:.8f} converged={r['converged']} worst_drop={r['worst']:.9f} box={r['box_binding']} rows={len(r['active'])}")
                rows, ex = exact_dual(g, r)
                assert min(ex) >= 0
                c = certificate(g, r, rows, ex)
                c.update(kind="farkas", claimed_bound=c.pop("value"))
                certs[f"farkas_{n}_{C}"] = c
                v = Fraction(c["claimed_bound"])
                log(f"n={n} ranks={C} exact family upper bound {v if v.denominator < 10**6 else float(v)} (float {float(v):.6f}) dual_rows={len(c['rows'])}")
                if float(v) > KNOWN_D[n] - 1 and r["converged"]:
                    terms = dyadic_potential(r)
                    start, drop = exact_check_potential(g, r, terms)
                    log(f"n={n} ranks={C} dyadic potential: start={float(start):.7f} worst_drop={float(drop):.9f} ratio={float(start/drop):.7f} terms={len(terms)}")
                    certs[f"primal_{n}_{C}"] = dict(kind="primal", n=n, ranks=C, rank_separation=1, terms=terms,
                                                    claimed_start=str(start), claimed_drop=str(drop),
                                                    needs_above=KNOWN_D[n] - 1)
            save()
    if args.selectors:
        for m, sorter, name in ((4, [[(0, 1), (2, 3)], [(0, 2), (1, 3)], [(1, 2)]], "8 wires"),
                                (8, BATCHER_8, "16 wires")):
            net = half_cleaner_selector(m, sorter)
            certs[f"selector_{2*m}"] = dict(kind="sorter", n=2 * m, ranks=[m], claimed_bound=len(net),
                                            network=[[list(c) for c in ly] for ly in net])
            log(f"half-cleaner selector on {name}: depth {len(net)} sorts weight {m}; D({2*m}) = {KNOWN_D.get(2*m, 9)}")
        for n, C in ((6, [3]), (8, [4]), (10, [5]), (12, [6]), (8, [3, 4, 5]), (10, [4, 5, 6]), (12, [5, 6, 7])):
            net = None
            for seed in range(4):
                cand = slice_beam(n, C, seed=seed, width=400, cand=40)
                if cand and (net is None or len(cand) < len(net)):
                    net = cand
            certs[f"beam_{n}_{C}"] = dict(kind="sorter", n=n, ranks=C, claimed_bound=len(net),
                                          network=[[list(c) for c in ly] for ly in net])
            log(f"beam: n={n} ranks={C} depth {len(net)}; D({n}) = {KNOWN_D[n]}")
    save()


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", required=True)
    ap.add_argument("--certs", required=True)
    ap.add_argument("--wires", type=int, nargs="+", default=[4, 5, 6])
    ap.add_argument("--lp-wires", type=int, nargs="*", default=[4, 5, 6])
    ap.add_argument("--lp-seconds", type=float, default=3600)
    ap.add_argument("--solver", choices=["highs", "mosek"], default="highs")
    ap.add_argument("--selectors", action="store_true")
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    a.skip = set()
    main(a)
