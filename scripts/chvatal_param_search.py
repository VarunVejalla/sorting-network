#!/usr/bin/env python3
"""Parameter-feasibility search for Chvatal's AKS network (DCS-TR-294), comparator-depth version.

Scope and honesty.  The script encodes the constraint set of the paper (sections 3-7) in the form in
which the Lean development uses it, and searches the parameters for the smallest slope

    slope = (depth of one stage) * (stages per level) / (bits per level)
          = (L+1)(L+2) * (x+y) / (x*z)           [log2-depth coefficient of lg N]

where k = 2^x is the tree arity, A = 2^y the capacity growth per level, nu = 2^-z the capacity
shrink per stage (A*nu > 1, i.e. y > z), and the separators are sort-scramble-sort packs on
m x n matrices with m in (2^L, 2^(L+1)], whose columns are sorted by Batcher (bitonic) networks of
depth T(p) = p(p+1)/2, p = L+1; one stage is two such sorts.  (k=64, A=4096, nu=1/64, L=59 gives
60*61*18/36 = 1830.)  The root and final-layer separators only change additive constants.

Constraints used (all named as in the paper / Lean):
  * Theorem 5.1 / Lemma 6.1: eps_B >= sqrt(2(1+ln m)/m) for the smallest m = 2^L of the window;
    (5.1): M >= 32 A^2 k^2 so 2^L >= A^2 k^2.
  * Theorem 5.1 / Lemma 6.2 (Property F): delta_F <= 1/25, f >= 10, eps_F >= 4e/f and
    eps_F >= (2/f)(1 + ln(3 e^5 f)/ln(0.12/(e eps_F))), 1/eps_F an integer; f >= m*(nu/(2Ak))*
    (1-1/(A nu k))/(1-1/(A k)^2)  (the paper's (5.3), from the smallest template).
  * Section 4: (4.2), (4.3), (4.4), (4.5) as in `AKS/Chvatal` history (with the CORRECTED (4.4)
    mu <= (delta_F/2)(A nu k - 1)/(A^2 k^2) and slack = (A nu k - 2 A nu + 1)/(2 A^2 k^2)).
Unmodelled (additive constants only): root separator (4.1), final sorters (Lemma 4.5), small bags.
NOT modelled and possibly binding: integrality/divisibility of the flow table for non-power-of-2
parameters (we only allow powers of two), the Lean formalization's current restriction eps_F =
1/(8e7), f >= 1.7e10, delta_F <= 128/4095 (mode --lean), and the exact schedule-derived t_f.

Modes:  --mode paper   (the paper's Theorem 5.1 condition on eps_F taken literally, delta_F <= 1/25)
        --mode proof   (general eps_F, but with the F-condition our Lean proof structure supports:
                        sup_u xval <= 0.3223 numerically; delta_F = 128/4095)
        --mode lean    (what the current Lean proof of Property F covers)
"""
import argparse
import math

E = math.e
LN2 = math.log(2)


def eps_B_need(L):
    """Lemma 6.1 requirement at the smallest m = 2^L of the window (2^L, 2^(L+1)]."""
    return math.sqrt(2 * (1 + L * LN2) / 2.0 ** L)


def eps_F_min(f):
    """Least eps >= 4e/f with eps >= (2/f)(1 + ln(3 e^5 f)/ln(0.12/(e eps)))."""
    lo = 4 * E / f
    eps = lo
    for _ in range(500):
        den = math.log(0.12 / (E * eps))
        if den <= 0:
            return None
        new = max(lo, (2 / f) * (1 + math.log(3 * E ** 5 * f) / den))
        if abs(new - eps) < 1e-18:
            return new
        eps = new
    return eps


X_MAX = 0.3223    # two-sided: 2*(1/100 + 1.025*x/(1-x)) < 1  <=>  x < 0.3223


def x_sup(f, eps, deltaF):
    """Sup over u = j/(f n) <= deltaF of the numeric quantity x of Lemma 6.2's proof (Lean `xval`):
         x(u) = (e^2 (f+2)^2/(4 u f))^(2/(eps f)) * (e/(2 eps u))^(2/f) * 2 e u.
       The exponent of u is 1 - 2/(eps f) - 2/f; when it is positive x is increasing in u and the
       sup is at u = deltaF (otherwise we fall back to a grid scan in u)."""
    def lx(u):
        return (2 / (eps * f)) * (2 + 2 * math.log(f + 2) - math.log(4 * u * f))             + (2 / f) * (1 + math.log(1 / (2 * eps * u))) + math.log(2 * E * u)
    if 1 - 2 / (eps * f) - 2 / f > 0:
        return math.exp(lx(deltaF))
    return math.exp(max(lx(deltaF * i / 400) for i in range(1, 401)))


_F_CACHE = {}


def eps_F_min_proof(f, deltaF):
    key = (round(math.log(f), 9), deltaF)
    if key not in _F_CACHE:
        _F_CACHE[key] = _eps_F_min_proof(f, deltaF)
    return _F_CACHE[key]


def _eps_F_min_proof(f, deltaF):
    """Least eps (>= 4e/f) with sup_u x(u) <= X_MAX, i.e. what our Lean proof structure of Lemma 6.2
       (xval <= 3/10 style numerics) actually supports; x is decreasing in eps."""
    lo, hi = 4 * E / f, 1.0
    if x_sup(f, hi, deltaF) > X_MAX:
        return None
    for _ in range(80):
        mid = math.sqrt(lo * hi)
        if x_sup(f, mid, deltaF) <= X_MAX:
            hi = mid
        else:
            lo = mid
    return hi


def f_over_m(k, A, nu):
    return (nu / (2 * A * k)) * (1 - 1 / (A * nu * k)) / (1 - 1 / (A * k) ** 2)


def evaluate(x, y, z, L, mode="paper"):
    """Return (feasible, details) for k=2^x, A=2^y, nu=2^-z, window (2^L, 2^(L+1)]."""
    if not (x >= 1 and y > z >= 1):
        return False, "need x>=1, y>z>=1"
    k, A, nu = 2 ** x, 2.0 ** y, 2.0 ** -z
    if 2.0 ** L < (A * k) ** 2:
        return False, "(5.1): 2^L < A^2 k^2"
    deltaF = 1 / 25 if mode == "paper" else 128 / 4095
    mu = min(nu / (A * k * k), 0.5 * deltaF * (A * nu * k - 1) / (A * A * k * k))      # (4.3), (4.4)
    m = 2.0 ** L
    f = m * f_over_m(k, A, nu)
    if f < 10:
        return False, "f < 10"
    if mode == "proof":
        epsF = eps_F_min_proof(f, deltaF)
        if epsF is None:
            return False, "no eps_F (xval)"
        epsF = 1 / math.floor(1 / epsF)
    elif mode == "paper":
        epsF = eps_F_min(f)
        if epsF is None:
            return False, "no eps_F"
        epsF = 1 / math.floor(1 / epsF)          # 1/eps_F integer (round the reciprocal down)
    else:                                         # what the current Lean proof of Property F covers
        if f < 1.7e10:
            return False, "lean mode: f < 1.7e10"
        epsF = 1 / 8e7
    a_, b_ = A * k / nu, epsF / (A * nu)
    disc = 1 - 4 * a_ * b_
    if disc < 0:
        return False, "(4.5) infeasible for this eps_F"
    delta = (1 - math.sqrt(disc)) / (2 * a_)                                           # (4.5) smallest delta
    if delta * k * A >= 1:
        return False, "delta k A >= 1"
    sib = delta * k * A * A / (1 - (delta * k * A) ** 2)
    slack = (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
    epsB_max = mu * (A * nu - 1 - (k - 1) * sib - delta * A * A * k) - slack         # (4.2)
    need = eps_B_need(L)
    ok = need <= epsB_max
    slope = (L + 1) * (L + 2) * (x + y) / (x * z)
    return ok, dict(slope=slope, mu=mu, delta=delta, epsF=epsF, epsB_need=need, epsB_max=epsB_max,
                    f=f, margin=epsB_max / need)


def best_for(x, y, z, mode):
    for L in range(2 * (x + y), 400):
        ok, d = evaluate(x, y, z, L, mode)
        if ok:
            return L, d
    return None


def search(mode, xs, ys, zs, top=15):
    rows = []
    for x in xs:
        for z in zs:
            for y in ys:
                if y <= z:
                    continue
                r = best_for(x, y, z, mode)
                if r:
                    rows.append((r[1]["slope"], x, y, z, r[0], r[1]))
    rows.sort(key=lambda t: t[0])
    return rows[:top]


def relaxed_lower_bound(step=0.1):
    """Continuous relaxation using only NECESSARY consequences of the constraints:
         (a) eps_B >= eps_B_need(L), L real, 2^L >= (A k)^2          [Thm 5.1 / 6.1, (5.1)]
         (b) eps_B < mu*(A nu - 1) - slack(A,nu,k)  [(4.2) with its other positive terms dropped]
         (c) mu <= min(nu/(A k^2), (1/2)(1/25)(A nu k - 1)/(A k)^2)  [(4.3), (4.4), delta_F <= 1/25]
         (d) k >= 2, A nu > 1.
       Minimises (L+1)(L+2)(x+y)/(x z) over real x>=1, 0<z<y, with L the least real value allowed.
       (x, y, z) are real, so this bounds every integer choice from below (up to float rounding)."""
    import numpy as np
    need = lambda L: np.sqrt(2 * (1 + L * LN2) / 2.0 ** L)
    best = (float("inf"), None)
    Y, Z = np.meshgrid(np.arange(step, 80, step), np.arange(step, 60, step), indexing="ij")
    A, nu = 2.0 ** Y, 2.0 ** -Z
    for x in np.arange(1, 40, step):
        k = 2.0 ** x
        with np.errstate(all="ignore"):
            mu = np.minimum(nu / (A * k * k), 0.5 / 25 * (A * nu * k - 1) / (A * k) ** 2)
            slack = (A * nu * k - 2 * A * nu + 1) / (2 * (A * k) ** 2)
            B = mu * (A * nu - 1) - slack
            lo, hi = np.ones_like(B), np.full_like(B, 800.0)
            for _ in range(60):
                mid = (lo + hi) / 2
                good = need(mid) <= B
                hi = np.where(good, mid, hi)
                lo = np.where(good, lo, mid)
            L = np.maximum(hi, 2 * (x + Y))
            slope = (L + 1) * (L + 2) * (x + Y) / (x * Z)
            slope = np.where((Y > Z) & (B > 0) & (need(800.0) <= B), slope, np.inf)
        i = np.unravel_index(np.argmin(slope), slope.shape)
        if slope[i] < best[0]:
            best = (float(slope[i]), (float(x), float(Y[i]), float(Z[i]), float(L[i])))
    return best


def feasible_real(x, y, z, L, deltaF=128 / 4095):
    """Real-parameter version of evaluate(mode='proof') (no power-of-two or integrality
       restrictions): returns epsB_max / epsB_need (>= 1 means feasible) or 0."""
    k, A, nu = 2.0 ** x, 2.0 ** y, 2.0 ** -z
    if A * nu <= 1 or L < 2 * (x + y):
        return 0.0
    mu = min(nu / (A * k * k), 0.5 * deltaF * (A * nu * k - 1) / (A * A * k * k))
    f = 2.0 ** L * f_over_m(k, A, nu)
    if f < 10:
        return 0.0
    epsF = eps_F_min_proof(f, deltaF)
    if epsF is None:
        return 0.0
    a_, b_ = A * k / nu, epsF / (A * nu)
    disc = 1 - 4 * a_ * b_
    if disc < 0:
        return 0.0
    delta = (1 - math.sqrt(disc)) / (2 * a_)
    if delta * k * A >= 1:
        return 0.0
    sib = delta * k * A * A / (1 - (delta * k * A) ** 2)
    slack = (A * nu * k - 2 * A * nu + 1) / (2 * A * A * k * k)
    emax = mu * (A * nu - 1 - (k - 1) * sib - delta * A * A * k) - slack
    return emax / eps_B_need(L) if emax > 0 else 0.0


def relaxed_proof_bound(step=0.25):
    """Continuous optimum of the slope with real x, y, z, L under the constraints of mode 'proof'
       (F-condition = what our Lean proof structure supports); no integrality, no power of two."""
    best = (float("inf"), None)
    x = 2.0
    while x <= 9.0:
        z = 1.0
        while z <= 9.0:
            y = z + 0.5
            while y <= z + 14:
                lo, hi = 2 * (x + y), 200.0
                if feasible_real(x, y, z, hi) >= 1:
                    for _ in range(30):
                        mid = (lo + hi) / 2
                        if feasible_real(x, y, z, mid) >= 1:
                            hi = mid
                        else:
                            lo = mid
                    sl = (hi + 1) * (hi + 2) * (x + y) / (x * z)
                    if sl < best[0]:
                        best = (sl, (x, y, z, hi))
                y += step
            z += step
        x += step
    return best


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mode", choices=["paper", "proof", "lean"], default="proof")
    ap.add_argument("--xmax", type=int, default=12)
    ap.add_argument("--ymax", type=int, default=40)
    ap.add_argument("--zmax", type=int, default=24)
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--relax", action="store_true", help="also compute the continuous lower bound")
    ap.add_argument("--check", action="store_true", help="reproduce the current parameters (k=64)")
    a = ap.parse_args()
    if a.check:
        for mode in ("lean", "paper"):
            r = best_for(6, 12, 6, mode)
            print(mode, "(x,y,z)=(6,12,6): L =", r[0], r[1])
    rows = search(a.mode, range(1, a.xmax + 1), range(2, a.ymax + 1), range(1, a.zmax + 1), a.top)
    print(f"mode={a.mode}: best integer (x,y,z) with power-of-two k=2^x, A=2^y, nu=2^-z")
    print("slope    x  y  z   L   mu        delta     epsF      epsB_need epsB_max  f")
    for s, x, y, z, L, d in rows:
        print(f"{s:7.1f} {x:2d} {y:2d} {z:2d} {L:3d}  {d['mu']:.2e}  {d['delta']:.2e}  {d['epsF']:.2e}  "
              f"{d['epsB_need']:.2e}  {d['epsB_max']:.2e}  {d['f']:.2e}")
    if a.relax:
        sp, pp = relaxed_proof_bound()
        print(f"continuous optimum, proof-mode F-condition: slope >= {sp:.1f} at (x,y,z,L) = "
              f"{tuple(round(v, 2) for v in pp)}")
        s, p = relaxed_lower_bound()
        print(f"continuous relaxation lower bound: slope >= {s:.1f} at (x,y,z,L) = {tuple(round(v, 2) for v in p)}")


if __name__ == "__main__":
    main()
