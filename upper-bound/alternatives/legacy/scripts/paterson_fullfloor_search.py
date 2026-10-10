"""Full-floor Paterson search: BagParams + every downstream numeric floor.

Fixed separator (paper deltas/mu): d_sep = 989 always, so C is FULLY EXACT:
    C = 989*(m/2) + d_root + 1,  m = min with (2A)^2*nu^m < 1 (exact),
    d_root from exact root-region < 2^k_root.

Floors encoded (all must hold; each mirrors a kernel-checked Lean lemma):
  BagParams (FastParams fields): geometric, tail, first, firstRounded,
    lambda-range -- mirror AKS/Paterson/BagParams.lean.
  C1 fringe/lattice: cap*(lam/2 - 1/32) >= 40, lam > 1/16
    -- AKS/Paterson/Schedule.lean fast_scheduled_fringe_bounds: the n/32
    lattice fringe must cover the ideal lam/2 fringe with rounding room.
  C2 cohort: Rmax + I*cap + mu*cap <= (1-alpha0)*(cap/2-64) at cap = mincap,
    Rmax = cap/(4A^2-1)/2 + 32, I = 2*mu*delta*A^2/(1-4*delta^2*A^2)
    -- AKS/Paterson/Balance.lean fast_cohort_slack (box worst corner; exact).
  F7 rebuild lock: A*delta = 1/12 exactly
    -- AKS/Paterson/RootRebuildNumerics.lean identities (32/35, 2/315) are
    A-independent GIVEN delta*A = 1/12; grid uses (A,delta) = (N/12, 1/N).
  F8 growth: nu*A >= 1 -- AKS/Paterson/ScheduledInvariant.lean.
  F11/F12 ceil margins: lam*cap/2 >= 64, (1-lam)*cap/2 >= 128
    -- AKS/Paterson/Schedule.lean hdiff, BoundarySchedule/ClippedRouting
    middle-ceil analogues (generous sufficient margins).

Search lead only until Lean-certified. Prefer robust points (slack tiebreak).
"""

import argparse
import math
from fractions import Fraction

MU = Fraction(199, 10000)
D0 = Fraction(1, 62)
TAIL = Fraction(1, 199) + Fraction(1, 110) + Fraction(1, 109) + Fraction(1, 106) + Fraction(1, 90)
ALPHA0 = Fraction(81773, 89250)
ONE_MA0 = Fraction(1, 1) - ALPHA0
ALLOW = Fraction(10)


def floors(A, delta, nu, cap):
    """Exact check of every floor. Returns (ok_dict, info)."""
    ok = {}
    ok["geometric"] = 4 * delta * delta * A * A < 1
    ok["tail"] = 2 * A * A * delta * delta + TAIL < nu * A * delta
    first_lhs = (2 * MU * delta * A * A
                 + 2 * MU * delta * A * A / (1 - 4 * delta * delta * A * A)
                 + Fraction(1, 1) / (8 * A * A - 2) + MU + D0 / 2)
    ok["first"] = first_lhs < nu * MU * A
    fresh = (1 - ALPHA0 + D0) / (2 * A) + TAIL * MU / A
    ok["firstRounded"] = 2 * MU * delta * A + fresh + ALLOW / cap <= nu * MU
    lam = (nu - Fraction(1, 1) / (2 * A)) / (2 * A - Fraction(1, 1) / (2 * A))
    ok["lambda"] = Fraction(0) < lam < 1
    ok["F7_rebuild_lock"] = A * delta == Fraction(1, 12)
    ok["F8_growth"] = nu * A >= 1
    # C1 fringe/lattice
    ok["C1_fringe"] = lam > Fraction(1, 16) and cap * (lam / 2 - Fraction(1, 32)) >= 40
    # C2 cohort worst corner at cap
    rmax = cap / (4 * A * A - 1) / 2 + 32
    intr = (Fraction(2) * MU * delta * A * A
            / (1 - 4 * delta * delta * A * A) * cap)
    ok["C2_cohort"] = rmax + intr + MU * cap <= ONE_MA0 * (cap / 2 - 64)
    # F11/F12 ceil margins
    ok["F11_deep_fringe"] = lam * cap / 2 >= 64
    ok["F12_middle"] = (1 - lam) * cap / 2 >= 128
    m = next((c for c in range(1, 31) if (2 * A) ** 2 * nu ** c < 1), None)
    ok["stage"] = m is not None
    root = cap / nu / nu
    region = (root / (4 * A * A - 1) + (root + 32) + 4 * (root * A * A + 32)
              + 16 * (root * A ** 4 + 32))
    k_root = max(0, math.ceil(math.log2(float(region)))) if region > 1 else 0
    while Fraction(2) ** k_root < region:
        k_root += 1
    while k_root > 0 and region <= Fraction(2) ** (k_root - 1):
        k_root -= 1
    C = Fraction(989) * Fraction(m, 2) + k_root * (k_root + 1) // 2 + 1 if m else None
    info = {"m": m, "k_root": k_root,
            "d_root": k_root * (k_root + 1) // 2, "C": C, "lam": lam,
            "fresh": fresh, "region": region,
            "s_tail": nu * A * delta - (2 * A * A * delta * delta + TAIL),
            "s_first": nu * MU * A - first_lhs,
            "s_round": nu * MU - (2 * MU * delta * A + fresh + ALLOW / cap),
            "s_C1": cap * (lam / 2 - Fraction(1, 32)) - 40,
            "s_C2": ONE_MA0 * (cap / 2 - 64) - (rmax + intr + MU * cap)}
    return ok, info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()
    rows = []
    for N in range(50, 65):
        A = Fraction(N, 12)
        delta = Fraction(1, N)
        for nu_i in range(600, 771):
            nu = Fraction(nu_i, 1000)
            for cap in (50000, 100000, 200000, 300000, 500000):
                cap = Fraction(cap)
                ok, info = floors(A, delta, nu, cap)
                if all(ok.values()):
                    rows.append((info["C"], A, delta, nu, cap, info, ok))
    rows.sort(key=lambda t: (t[0], -min(t[5]["s_C1"], t[5]["s_C2"])))
    print(f"fully-feasible: {len(rows)}")
    for C, A, delta, nu, cap, info, ok in rows[:args.top]:
        print(f"C={C} m={info['m']} d_root={info['d_root']}(2^{info['k_root']}) "
              f"A={A} d=1/{delta.denominator} nu={nu} cap={cap} lam={info['lam']} "
              f"slacks(t/f/r)={float(info['s_tail']):.2e}/{float(info['s_first']):.2e}/"
              f"{float(info['s_round']):.2e} C1={float(info['s_C1']):.1f} "
              f"C2={float(info['s_C2']):.1f}")
    # margin landscape: best C per m
    by_m = {}
    for C, A, delta, nu, cap, info, ok in rows:
        by_m.setdefault(info["m"], []).append((C, A, delta, nu, cap))
    for m in sorted(by_m):
        cs = [c for c, _, _, _, _ in by_m[m]]
        print(f"m={m}: count={len(cs)} best={min(cs)}")


if __name__ == "__main__":
    main()
