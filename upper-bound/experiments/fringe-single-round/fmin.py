#!/usr/bin/env python3
"""f_min for the ONE-round Property F existence proof (AKS/Chvatal Lemma 6.2 structure).

Reconstructed from Lemma62FailE/Ratio/Numerics/Round.lean.  Generalised by
  theta : discard height g = theta*f (Lean: theta = 1/2, `f/2`, `topRows m (f/2)`)
  eps   : contract epsilon (Lean: 1/86e6);  J = 1/eps is the rounding grid (forced by integrality)
  delta : supported rank fraction j <= delta f n (Lean: 128/4095, rounded to 1/31 in Lemma62Params)

Per-E bound  P(bad at E) <= 1.025 * x^E,  ln x = ln(tops)/E + ln G1(b)/E:
  ln x = [2+2ln(g+1)-ln f-ln u]/(eps(g+1)) + [1+ln(1-theta)-ln eps-ln u]/(f-g) + 1+ln u-ln(1-theta),
  u = j/(f n).   (theta=1/2 reproduces Lemma62Numerics.xval, up to f+2 vs f.)
"""
import math
LN = math.log
E1 = math.e

def lnx(f, eps, u, theta=0.5, lean=False):
    g = theta * f
    if lean:   # exactly as in Lemma62Numerics (a = 2/(eps f); -ln eps replaced by 86e6)
        a = 2 / (eps * f); b = 2 / f
        lneps = -86e6 * (eps * 86e6)  # -ln(eps) <= 1/eps (artifact)
        return (a * (2 + 2 * LN(f + 2) - 2 * LN(2) - LN(f) - LN(u))
                + b * (1 - LN(2) + (1 / eps) - LN(u)) + LN(2) + 1 + LN(u))
    a = 1 / (eps * (g + 1))
    return (a * (2 + 2 * LN(g + 1) - LN(f) - LN(u))
            + (1 + LN(1 - theta) - LN(eps) - LN(u)) / (f - g)
            + 1 + LN(u) - LN(1 - theta))

def coef(f, eps, theta):  # exponent of u (needs > 0 for x increasing in u)
    return 1 - 1 / (eps * (theta * f + 1)) - 1 / ((1 - theta) * f)

def xsup(f, eps, u, theta=0.5, lean=False):
    return math.exp(lnx(f, eps, u, theta, lean))

def bisect_f(pred, lo=1e5, hi=1e13):
    """smallest f with pred(f) true (assumes monotone)."""
    if not pred(hi): return None
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if pred(mid): hi = mid
        else: lo = mid
    return hi

def fmin_sup(eps, delta, xmax=0.3223, theta=0.5, lean=False, uex=None):
    u = delta if uex is None else uex
    def pred(f):
        if coef(f, eps, theta) <= 0: return False
        return xsup(f, eps, u, theta, lean) <= xmax
    return bisect_f(pred)

def best_theta(eps, delta, xmax=0.3223, uex=None):
    best = None
    for th in [i / 200 for i in range(2, 199)]:
        f = fmin_sup(eps, delta, xmax, th, False, uex)
        if f and (best is None or f < best[0]): best = (f, th)
    return best

# ---- exact sum over E (worst n >= 16) -------------------------------------------------
def S_total(f, eps, delta, n, theta=0.5, cap=True, C=1.025, E0=3000):
    """sum_{E=1}^{ceil(eps*delta*f*n)} C*x_E^E, x_E evaluated at mass j'_E and eps_eff=E/j'."""
    J = 1 / eps
    jmax = delta * f * n
    K = math.ceil(eps * jmax)
    tot = 0.0
    top = min(K, E0)
    for E in range(1, top + 1):
        jp = min(E * J, jmax) if cap else E * J
        u = jp / (f * n)
        ee = E / jp
        t = E * lnx(f, ee, u, theta)
        if t < -700: continue
        if t > 600: return float("inf")
        tot += C * math.exp(t)
    if K > top:
        xs = xsup(f, eps, jmax / (f * n) if cap else delta + J / (f * n), theta)
        if xs >= 1: return float('inf')
        tot += C * xs ** top * xs / (1 - xs)
    return tot

def worst_n(f, eps, delta, theta=0.5, cap=True, ns=None):
    ns = ns or sorted(set([16, 17, 20, 24, 32, 48, 64, 100, 128, 256, 512, 1024, 4096, 1 << 14, 1 << 17, 1 << 20, 1 << 24]))
    best = (0, None)
    for n in ns:
        s = S_total(f, eps, delta, n, theta, cap)
        if s > best[0]: best = (s, n)
    return best

def fmin_sum(eps, delta, budget=0.49, theta=0.5, cap=True):
    def pred(f):
        if coef(f, eps, theta) <= 0: return False
        return worst_n(f, eps, delta, theta, cap)[0] <= budget
    return bisect_f(pred, 1e6, 1e13)

if __name__ == "__main__":
    eps = 1 / 86e6; d = 128 / 4095
    print("Lean-as-written, u=1/31, xmax=.3223:", fmin_sup(eps, d, uex=1/31, lean=True))
    print("Lean-as-written, u=delta:", fmin_sup(eps, d, lean=True))
    print("exact logs, theta=.5, u=1/31:", fmin_sup(eps, d, uex=1/31))
    print("exact logs, theta=.5, u=delta, x<=.32:", fmin_sup(eps, d))
    print("x<1 theta=.5:", fmin_sup(eps, d, xmax=1.0))
    print("best theta xmax=.3223:", best_theta(eps, d))
    print("best theta x<=1:", best_theta(eps, d, xmax=1.0))
