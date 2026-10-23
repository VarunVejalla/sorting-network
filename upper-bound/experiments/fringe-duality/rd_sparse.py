#!/usr/bin/env python3
"""Route (d), regime (A): j <= C J ln n, for every n >= n0 at once (ROUND1-ENERGY.md, "Regime (A)").

Only collision-type terms are used (the Kingman branches pay ln n entropy over a fixed t and are not
n-uniform). Each n-dependent term is replaced by its sup over n >= n0:
  * entropies: ent(n) = E0 + Lc ln n with Lc = s2 + 1 (lbinom(n, s2) <= s2 ln(e n/s2), plus the ln n term);
  * A_coll: x_D(n) <= R [g0 + E0 + Lc (ln n0 + x)] / (s* + x/2), x = ln(n/n0), s(n) = s* + x/2 keeps
    n (q e^s)^2 constant (q = e R u/(lam n)), and n ln(1 + y) <= n y; sup over x >= 0 of this Moebius map is
    max(value at x = 0, 2 R Lc);
  * mult_excess: P_n(M = k) <= binom(H, k) (s2/n)^k; t(n) = t* + x makes the n-term <= its n0 value
    times (n/n0)^{1-c} <= 1 (c >= 1), so sup = max(value at n0, Lc);
  * b = j/n <= j/n0 =: b0: levels use the j-interval conventions with b in [0, b0] (cap R = ceil(hi),
    floor d = floor(lo + 1 - b0), free rows L0 = ceil(b0) + x).
Floats (as route_d_rigorous). Usage: python -I rd_sparse.py sweep J f j_from j_to [n0_log2]
"""
import math
import sys

import route_d_rigorous as RD

ETA = RD.ETA


def a_coll_sup(j, R, u, n0, E0, Lc):
    best = math.inf
    for lam in (0.6, 0.75, 1.0, 1.5, 2.0, 3.0):
        q0 = math.e * R * u / (lam * n0)
        if q0 >= 1:
            continue
        for s in [0.05 * 1.1 ** i for i in range(160)]:
            qe = q0 * math.exp(min(s, 700))
            if qe >= 1:
                break
            g0 = n0 * qe * qe / ((1 - q0) * (1 - qe))
            v0 = R * (g0 + E0 + Lc * math.log(n0)) / s
            xD = max(v0, 2 * R * Lc)
            best = min(best, (lam * j + xD) / (1 - 1 / (2 * lam)))
    return best


def mult_sup(Hh, s2, n0, E0, Lc, c):
    """sup over n >= n0 of max_S sum_u (M_u - c)_+, M_u ~ Bin(Hh, s2/n), with P(M = k) <= binom(Hh, k)(s2/n)^k."""
    if Hh <= c:
        return 0.0
    lp0 = math.log(s2 / n0)
    K = min(Hh, c + 400)
    best = math.inf
    for t in [0.02 * 1.12 ** i for i in range(120)]:
        if t > 600:
            break
        # Y0 = n0 sum_{k>c} binom(H,k) (s2/n0)^k e^{t(k-c)}; tail beyond K by a geometric bound
        terms = [RD.lbinom(Hh, k) + k * lp0 + t * (k - c) for k in range(c + 1, K + 1)]
        mx = max(terms)
        lse = mx + math.log(sum(math.exp(x - mx) for x in terms))
        if K < Hh:
            r = (Hh - K) / (K + 1) * (s2 / n0) * math.exp(t)
            if r >= 1:
                continue
            lse = max(lse, terms[-1] + math.log(r / (1 - r))) + math.log1p(math.exp(-abs(lse - (terms[-1] + math.log(r / (1 - r))))))
        if lse + math.log(n0) > 600:
            continue
        Y0 = n0 * math.exp(lse)
        v0 = (Y0 + E0 + Lc * math.log(n0)) / t
        best = min(best, max(v0, Lc))
    return best


def kmax_sup(j, n0):
    R = int(3 * math.sqrt(j)) + 10
    A = a_coll_sup(j, R, 1, n0, math.log(1 / ETA), 1.0)
    return min(float(j), math.sqrt(A)) if A < R * R else float(j)


def escapes_A(j, f, s2, n0, L0x=0, ratio=1.6, s2_lo=None, j_lo=None):
    if s2_lo is None:
        s2_lo = s2
    if j_lo is None:
        j_lo = j
    b0 = j / n0
    K = kmax_sup(j, n0)
    top = b0 + K + 1
    L0 = math.ceil(b0) + L0x
    Lc = s2 + 1.0
    E0 = s2 * (1 - math.log(s2)) + 2 * math.log(top + 2) + math.log(1 / ETA) + 4 + math.log(len(RD.CS))
    total = 0.0
    lo = L0
    while lo < top:
        off = lo
        hi = min(math.ceil(top), max(lo + 1, math.ceil(max(off + 8, off * ratio))))
        R = math.ceil(hi)                       # b >= 0: cap hi - b <= hi
        u = (hi - lo) * s2
        Ac = a_coll_sup(math.ceil(j), hi, u, n0, E0, Lc)
        k = RD.kmax_sources(Ac, lo + 1 - math.ceil(b0), s2) if lo + 1 - math.ceil(b0) >= 1 else math.inf
        cnt = min(k * c + mult_sup(hi - lo, s2, n0, E0, Lc, c) for c in RD.CS if c <= hi - lo or c == 1)
        total += min(s2 * (hi - lo), cnt)
        lo = hi
    return total - (f - L0) * s2_lo


def load_A(jb, f, s, n0, ja):
    return min(escapes_A(jb, f, s, n0, L0x, r, s, ja) + f * s for L0x in (0, 50, 200) for r in (1.3, 1.6, 2.0))


def worst_A(ja, jb, f, n0, smax=4096):
    worst = (-math.inf, 0)
    s = 1
    while s <= smax and s <= max(1, jb / f):
        L = load_A(jb, f, s, n0, ja)
        worst = max(worst, (L - f * s, s))
        if L / s < f:
            return worst
        s += 1
        if s > 64:
            break
    sa, La = s - 1, load_A(jb, f, s - 1, n0, ja)
    while sa <= max(1, jb / f):
        sb = max(sa + 1, int(sa * 1.05))
        Lb = load_A(jb, f, sb, n0, ja)
        worst = max(worst, (min(sb * (La / sa - f), Lb - f * sa), sb))
        if Lb / sb < f:
            return worst
        sa, La = sb, Lb
    return worst


def sweep(J, f, jfrom, jto, n0, ratio=1.15):
    ja = jfrom
    while ja < jto:
        jb = min(jto, ja * ratio)
        if ja < J < jb:
            jb = J
        allowed = 1.0 if jb <= J else ja / J
        e, s = worst_A(ja, jb, f, n0)
        print(f"  j in [{ja / J:10.4g}, {jb / J:10.4g}] J: worst {e:12.1f} at s2 <= {s:7d}  allowed {allowed:10.1f}"
              f"  {'OK' if e < allowed else 'FAIL'}   (all n >= 2^{math.log2(n0):.0f})", flush=True)
        ja = jb


if __name__ == "__main__":
    if sys.argv[1] == "sweep":
        J, f, jf, jt = (float(x) for x in sys.argv[2:6])
        n0 = 2.0 ** (float(sys.argv[6]) if len(sys.argv) > 6 else 40)
        print(f"regime A sweep: J = {J:.3g}, f = {f:.0f}, j in [{jf:.3g}, {jt:.3g}], all n >= {n0:.3g}", flush=True)
        sweep(J, f, jf, jt, n0)


# ---------------------------------------------------------------------------------------------------------
# Merged form (uniform in j as well): rows below offset D counted in full; above D, levels [d_i, R_i) with
# source counts k_i <= A_i / d_i^2 (A_i: collision sup at level i, cap R_i, per-level union -- summable), and
# ONE multiplicity union over all rows [D, top): sum_i sum_u (M_u^(i) - c)_+ <= sum_u (M_u^tot - c)_+.
# Logs throughout (n0 may be astronomically large: ln_n0 given).

def a_coll_sup_ln(j, R, u, ln_n0, E0, Lc):
    best = math.inf
    for lam in (0.6, 0.75, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0):
        lq0 = math.log(math.e * R * u / lam) - ln_n0
        if lq0 >= 0:
            continue
        for s in [0.05 * 1.1 ** i for i in range(200)]:
            lqe = lq0 + s
            if lqe >= -1e-12:
                break
            q0, qe = math.exp(lq0), math.exp(lqe)
            lg0 = ln_n0 + 2 * lqe - math.log((1 - q0) * (1 - qe))
            g0 = math.exp(lg0) if lg0 < 700 else math.inf
            v0 = R * (g0 + E0 + Lc * ln_n0) / s
            xD = max(v0, 2 * R * Lc)
            best = min(best, (lam * j + xD) / (1 - 1 / (2 * lam)))
    return best


def mult_sup_ln(Hh, s2, ln_n0, E0, Lc, c):
    if Hh <= c:
        return 0.0
    lp0 = math.log(s2) - ln_n0
    K = min(Hh, c + 400)
    best = math.inf
    for t in [0.02 * 1.12 ** i for i in range(120)]:
        if t > 600:
            break
        terms = [RD.lbinom(Hh, k) + k * lp0 + t * (k - c) for k in range(c + 1, K + 1)]
        mx = max(terms)
        lse = mx + math.log(sum(math.exp(x - mx) for x in terms))
        if K < Hh:
            lr = math.log((Hh - K) / (K + 1)) + lp0 + t
            if lr >= 0:
                continue
            tail = terms[-1] + lr - math.log1p(-math.exp(lr))
            lse = max(lse, tail) + math.log1p(math.exp(-abs(lse - tail)))
        lY = ln_n0 + lse
        if lY > 600:
            continue
        v0 = (math.exp(lY) + E0 + Lc * ln_n0) / t
        best = min(best, max(v0, Lc))
    return best


def escapes_merged(j, f, s2, ln_n0, D, ratio=2.0):
    """escapes for every set of size s2 and every n >= e^{ln_n0}, at mass j (b = j/n <= j e^{-ln_n0} = b0)."""
    b0 = j * math.exp(-ln_n0) if ln_n0 < 700 else 0.0
    top = b0 + math.sqrt(2 * j) + 2           # a round-1 column has z(z+1)/2 <= j
    Lc = s2 + 1.0
    E0 = s2 * (1 - math.log(s2)) + 2 * math.log(top + 2) + math.log(1 / ETA) + 4 + math.log(len(RD.CS)) + math.log(64)
    base = math.ceil(b0) + D                  # rows below base: counted in full
    if base >= top:
        return s2 * top - f * s2
    ksum = 0.0
    d = base
    while d < top:
        R = min(math.ceil(top), int(d * ratio) + 1)
        u = (R - d) * s2
        A = a_coll_sup_ln(math.ceil(j), R, u, ln_n0, E0, Lc)
        ksum += min(A / (d - math.ceil(b0)) ** 2, s2 * (R - d))
        d = R
    Htot = int(math.ceil(top) - base)
    cnt = min(c * ksum + mult_sup_ln(Htot, s2, ln_n0, E0, Lc, c) for c in RD.CS if c <= Htot or c == 1)
    return s2 * base + min(s2 * Htot, cnt) - f * s2


def load_merged(j, f, s, ln_n0):
    return min(escapes_merged(j, f, s, ln_n0, D, r) for D in (500, 1000, 2000, 3000) for r in (1.6, 2.0, 4.0)) + f * s


def worst_merged(j, f, ln_n0, smax=10 ** 9):
    """sup over set sizes via the monotone average L(s)/s (exact s <= 64, then 1.05-geometric cells)."""
    worst = (-math.inf, 0)
    s = 1
    while s <= 64 and s <= max(1, j / f):
        L = load_merged(j, f, s, ln_n0)
        worst = max(worst, (L - f * s, s))
        if L / s < f:
            return worst
        s += 1
    sa, La = s - 1, load_merged(j, f, s - 1, ln_n0)
    while sa <= max(1, j / f) and sa <= smax:
        sb = max(sa + 1, int(sa * 1.05))
        Lb = load_merged(j, f, sb, ln_n0)
        worst = max(worst, (min(sb * (La / sa - f), Lb - f * sa), sb))
        if Lb / sb < f:
            return worst
        sa, La = sb, Lb
    return worst
