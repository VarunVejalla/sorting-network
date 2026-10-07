"""Search Paterson bag parameters for a smaller *full* sorting constant.

Objective (limsup coefficient, base 2):
    C = d_sep * (m/2) + d_root + 1
where d_sep = p-level separator depth (ceil per level),
      m     = min stages per 2 levels with (2A)^2 * nu^m < 1,
      d_root= bitonic triangle k(k+1)/2 for the root region (< 2^k),
      +1    = known-permutation correction.

Usage:
    python scripts/paterson_search.py --p 5 [--draws N] [--top K] [--seed S]
    python scripts/paterson_search.py --p 6 --draws 120000 --top 20

This is a *search heuristic*, not a proof. Winners must be re-certified in
Lean: entropy numerics (PatersonNumerics), Params (FastParams), root budget
(Root/RootAllocationBudget), accounting, and the tight bound. Float entropy
estimates may differ from Lean ceil certificates by ~1 per level.

Mirrors (generalized to free p/mu/delta/deltas):
  AKS/Paterson/BagParams.lean  (geometric, capacity, tail, first, firstRounded)
  AKS/Bags/PatersonNumerics.lean (entropy depth C(alpha,eps), separator sum)
  AKS/Paterson/FastParams.lean + Accounting.lean (stage cert, depth budget)
  AKS/Paterson/Root.lean (rootCeiling, region budget -> 2^k -> 561-style cost)

p=6 GENERALIZATIONS (assumptions, NOT kernel-checked -- verify before Lean):
  (G1) eta has the same form: 4*mu*delta*A^2/(1-4*delta^2*A^2) + 1/(4A^2-1).
  (G2) Shrink cert keeps the form (2A)^2 * nu^m < 1 (m minimized, not fixed 13).
  (G3) Root region keeps levels {cold,0,2,4} (even levels below p); a p=6
       rebuild touching deeper levels would cost MORE than estimated here.
  (G4) Separator support stays 1/50, so mu < 1/50 is still required; p=6 also
       needs 2^p*mu <= 1 (else the deepest alpha exceeds 1 and C is invalid).
Status of p=5 baseline: kernel-checked 6990.5 (see AKS/Bounds/PatersonTight).
Status of any p=6 candidate: search lead only, even if exact rational checks
pass here -- the separator/bag/root Lean proofs are all p=5-specific.
"""

import argparse
import math
import random
from fractions import Fraction


def entropy(x: float) -> float:
    return -x * math.log(x) - (1.0 - x) * math.log(1.0 - x)


def halver_depth_float(alpha: float, eps: float) -> float:
    p = eps * alpha
    q = (1.0 - eps) * alpha
    return 1.0 + (entropy(p) + entropy(q)) / (-p * math.log(q))


def separator_levels(mu, deltas, A, delta):
    """deltas = [d0, d1, ..., dp]; returns (a0, eta, [(alpha, eps)...])."""
    p = len(deltas) - 1
    eta = (4 * mu * delta * A * A / (1 - 4 * delta * delta * A * A)
           + 1.0 / (4 * A * A - 1))
    a0 = 1 - eta - 2 * mu
    levels = [(a0, deltas[0])] + [((2 ** i) * mu, deltas[i]) for i in range(1, p + 1)]
    return a0, eta, levels


def eval_float(A, mu, delta, nu, deltas, mincap, allow=10.0):
    """Float evaluation. deltas = (d0..dp). Returns None if invalid/infeasible."""
    p = len(deltas) - 1
    if not (1.0 < A and 0 < mu < 0.02 and 0 < delta < 1 and 0 < nu < 1):
        return None
    if not all(0 < d < 0.5 for d in deltas):
        return None
    if 4 * delta * delta * A * A >= 1:
        return None
    if (2 ** p) * mu > 1:
        return None
    tail = sum(deltas[1:])
    if not (2 * A * A * delta * delta + tail < nu * A * delta):
        return None
    a0, eta, levels = separator_levels(mu, deltas, A, delta)
    if not (0 < a0 < 1):
        return None
    if not all(0 < a and a <= 1 and 0 < e < 0.5 for (a, e) in levels):
        return None
    d0 = deltas[0]
    first_lhs = (2 * mu * delta * A * A
                 + 2 * mu * delta * A * A / (1 - 4 * delta * delta * A * A)
                 + 1 / (8 * A * A - 2) + mu + d0 / 2)
    if not (first_lhs < nu * mu * A):
        return None
    fresh = (1 - a0 + d0) / (2 * A) + tail * mu / A
    if not (2 * mu * delta * A + fresh + allow / mincap <= nu * mu):
        return None
    if not (1 / (2 * A) < nu < 2 * A):
        return None
    lam = (nu - 1 / (2 * A)) / (2 * A - 1 / (2 * A))
    if not (0 < lam < 1):
        return None
    try:
        floats = [halver_depth_float(a, e) for (a, e) in levels]
    except ValueError:
        return None
    ceils = [math.ceil(v) for v in floats]
    d_sep = max(ceils[0], ceils[1]) + sum(ceils[2:])
    m = None
    for cand in range(1, 31):
        if (2 * A) ** 2 * nu ** cand < 1:
            m = cand
            break
    if m is None:
        return None
    root = mincap / nu / nu
    reserve = root / (4 * A * A - 1)
    region = reserve + (root + 32) + 4 * (root * A * A + 32) + 16 * (root * A ** 4 + 32)
    k_root = 0 if region <= 1 else int(math.ceil(math.log2(region)))
    while 2.0 ** k_root < region:
        k_root += 1
    while k_root > 0 and region <= 2.0 ** (k_root - 1):
        k_root -= 1
    d_root = k_root * (k_root + 1) // 2
    C = d_sep * (m / 2) + d_root + 1
    s_ideal = math.log(2 * A) / -math.log(nu)
    return {
        "C": C, "d_sep": d_sep, "ceils": ceils, "floats": floats,
        "m": m, "s_ideal": s_ideal, "k_root": k_root, "d_root": d_root,
        "region": region, "root": root, "lam": lam, "eta": eta, "a0": a0,
        "tail": tail, "fresh": fresh, "p": p,
        "slack_tail": nu * A * delta - (2 * A * A * delta * delta + tail),
        "slack_first": nu * mu * A - first_lhs,
        "slack_rounded": nu * mu - (2 * mu * delta * A + fresh + allow / mincap),
    }


def exact_recheck(Af, muf, deltaf, nuf, deltas_f, mincap, allow=10):
    """Exact rational recheck of the non-log constraints + stage/root certs."""
    A = Fraction(Af).limit_denominator(1000000)
    mu = Fraction(muf).limit_denominator(1000000)
    delta = Fraction(deltaf).limit_denominator(1000000)
    nu = Fraction(nuf).limit_denominator(1000000)
    ds = [Fraction(d).limit_denominator(1000000) for d in deltas_f]
    p = len(ds) - 1
    d0 = ds[0]
    tail = sum(ds[1:])
    mc, al = Fraction(mincap), Fraction(allow)
    checks = {}
    checks["geometric"] = 4 * delta * delta * A * A < 1
    eta = (Fraction(4) * mu * delta * A * A / (1 - 4 * delta * delta * A * A)
           + Fraction(1, 1) / (4 * A * A - 1))
    a0 = 1 - eta - 2 * mu
    checks["a0_range"] = Fraction(0) < a0 < 1
    checks["tail"] = 2 * A * A * delta * delta + tail < nu * A * delta
    first_lhs = (2 * mu * delta * A * A
                 + 2 * mu * delta * A * A / (1 - 4 * delta * delta * A * A)
                 + Fraction(1, 1) / (8 * A * A - 2) + mu + d0 / 2)
    checks["first"] = first_lhs < nu * mu * A
    fresh = (1 - a0 + d0) / (2 * A) + tail * mu / A
    checks["firstRounded"] = 2 * mu * delta * A + fresh + al / mc <= nu * mu
    lam = (nu - Fraction(1, 1) / (2 * A)) / (2 * A - Fraction(1, 1) / (2 * A))
    checks["lambda"] = Fraction(0) < lam < 1
    checks["mu_support"] = mu < Fraction(1, 50)
    checks["deep_alpha"] = (2 ** p) * mu <= 1
    m = None
    for cand in range(1, 31):
        if (2 * A) ** 2 * nu ** cand < 1:
            m = cand
            break
    checks["stage_cert"] = m is not None
    root = mc / nu / nu
    reserve = root / (4 * A * A - 1)
    region = (reserve + (root + 32) + 4 * (root * A * A + 32)
              + 16 * (root * A ** 4 + 32))
    k_root = max(0, math.ceil(math.log2(float(region)))) if region > 1 else 0
    while Fraction(2) ** k_root < region:
        k_root += 1
    while k_root > 0 and region <= Fraction(2) ** (k_root - 1):
        k_root -= 1
    checks["root_pow2"] = region < Fraction(2) ** k_root or region <= 1
    return checks, {"m": m, "k_root": k_root,
                    "d_root": k_root * (k_root + 1) // 2,
                    "lam": lam, "eta": eta, "a0": a0, "fresh": fresh,
                    "region": region}


def random_point(rng, p):
    if p == 4:  # small-A regime: nu=2*lambda*A+(1-lambda)/2A needs A~2 for nu<1
        A = float(rng.choice([Fraction(7, 4), Fraction(2, 1), Fraction(9, 4),
                              Fraction(5, 2)])) + rng.uniform(-0.2, 0.2)
        mu = rng.randint(100, 199) / 10000
        delta = 1 / rng.randint(50, 66)
        deltas = (1 / rng.randint(55, 78), 1 / rng.randint(120, 260),
                  1 / rng.randint(90, 160), 1 / rng.randint(90, 160),
                  1 / rng.randint(70, 140))
        nu = rng.randint(600, 900) / 1000
    elif p == 5:
        A = float(rng.choice([Fraction(17, 4), Fraction(9, 2), Fraction(19, 4),
                              Fraction(5, 1), Fraction(21, 4)])) + rng.uniform(-0.3, 0.3)
        mu = rng.randint(150, 199) / 10000
        delta = 1 / rng.randint(50, 66)
        deltas = (1 / rng.randint(55, 78), 1 / rng.randint(150, 260),
                  1 / rng.randint(90, 135), 1 / rng.randint(90, 135),
                  1 / rng.randint(85, 130), 1 / rng.randint(70, 115))
        nu = rng.randint(688, 748) / 1000
    else:  # p == 6: smaller mu (64mu<=1), stronger deltas, wider nu
        A = float(rng.choice([Fraction(17, 4), Fraction(9, 2), Fraction(19, 4),
                              Fraction(5, 1), Fraction(21, 4)])) + rng.uniform(-0.3, 0.3)
        mu = rng.randint(90, 156) / 10000
        delta = 1 / rng.randint(50, 70)
        deltas = (1 / rng.randint(55, 85), 1 / rng.randint(150, 380),
                  1 / rng.randint(150, 350), 1 / rng.randint(140, 320),
                  1 / rng.randint(110, 280), 1 / rng.randint(90, 240),
                  1 / rng.randint(70, 200))
        nu = rng.randint(380, 730) / 1000
    mincap = rng.choice([300000, 1000000, 3000000, 10000000])
    return (A, mu, delta, nu, deltas, mincap)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=5, choices=[4, 5, 6])
    ap.add_argument("--draws", type=int, default=80000)
    ap.add_argument("--seed", type=int, default=20261003)
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    p = args.p

    if p == 5:
        base = (19 / 4, 199 / 10000, 1 / 57, 707 / 1000,
                (1 / 62, 1 / 199, 1 / 110, 1 / 109, 1 / 106, 1 / 90), 300000)
        rb = eval_float(*base)
        print(f"baseline fastParams: C={rb['C']:.1f} d_sep={rb['d_sep']} "
              f"ceils={rb['ceils']} m={rb['m']} k_root={rb['k_root']} "
              f"d_root={rb['d_root']} s_ideal={rb['s_ideal']:.3f}")
    if p != 5:
        print(f"p={p}: NO kernel-checked baseline; all results are search leads "
              "under G1-G4 (see module docstring).")

    best = []
    seen = 0
    for _ in range(args.draws):
        pt = random_point(rng, p)
        r = eval_float(*pt)
        if r is None:
            continue
        seen += 1
        best.append((r["C"], pt, r))
    best.sort(key=lambda t: t[0])
    print(f"feasible: {seen}/{args.draws}")
    for C, pt, r in best[:args.top]:
        (A, mu, delta, nu, deltas, mincap) = pt
        ds = ",".join(f"1/{1 / d:.0f}" for d in deltas)
        print(f"C={C:.1f} d_sep={r['d_sep']}{r['ceils']} m={r['m']} "
              f"d_root={r['d_root']}(2^{r['k_root']}) s={r['s_ideal']:.3f} "
              f"A={A:.3f} mu={mu:.5f} d={delta:.5f} nu={nu:.3f} "
              f"deltas={ds} cap={mincap} "
              f"slacks(t/f/r)={r['slack_tail']:.2e}/{r['slack_first']:.2e}/"
              f"{r['slack_rounded']:.2e}")
    if best:
        C, pt, r = best[0]
        (A, mu, delta, nu, deltas, mincap) = pt
        checks, ex = exact_recheck(A, mu, delta, nu, deltas, mincap)
        print("best exact recheck:", {k: bool(v) for k, v in checks.items()},
              "m =", ex["m"], "k_root =", ex["k_root"],
              "lam =", float(ex["lam"]))


if __name__ == "__main__":
    main()
