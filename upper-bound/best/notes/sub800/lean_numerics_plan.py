#!/usr/bin/env python3
"""Planner for the Lean numerics of the walk bound (LEAN-PLAN W4.5).

Checks, in interval arithmetic, exactly the sufficient conditions that the Lean files will prove
per p-cell [pa, pb] with fixed rational parameters (lam, t, alpha[, beta]):

  rate (forward):   1 + pb (e^alpha - 1) <= e^{alpha (pa + lam)}   (=> hα for every p in the cell)
  rate (backward):  1 + (1-pa)(e^beta - 1) <= e^{beta ((1-pb) + lam)}
  round 1 budget:   lam m + (Hmax + ln Lb(t,alpha,delta) + c1)/t <= (E1/2) m        (per column)
  round 2 budget:   lam (E1 m + g') + (Hmax + ln(Lb(alpha)+Lb(beta)-1) + (ln G + c2')/16 ... )/t <= (d/2) m

with Hmax = max of the binary entropy over the cell, c1 = ln(15/eta1)/16, the round-2 union
constant (ln G + ln(15/eta2))/16, Lb(t,th,dl) = e^{t dl} (1 + (1-e^{-t dl})/(1-e^{(t-th) dl})), and
the checks done at m = M_LO (monotone in m for fixed parameters, see LEAN-PLAN W4.5). Round 2 is
symmetric in p <-> 1-p, so only p <= 1/2 is planned for it.

Run:  python -I lean_numerics_plan.py
"""
import math
import os
import sys
from fractions import Fraction as Fr

from mpmath import iv, mpf
from scipy import optimize

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "experiments", "walk-bound"))
import na_precision as NP  # noqa: E402

iv.dps = 30
M_LO = 50859009                    # ceil(2^25.6)
M_HI = 2 ** 26
ETA1, ETA2 = Fr(1, 100), Fr(1, 1000)
EPS_B = Fr(1, 105000)
DELTA_T = Fr(1, 1000)              # t * delta in the layer cake


def I(x):
    x = Fr(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


def H(q):
    return -q * math.log(q) - (1 - q) * math.log(1 - q) if 0 < q < 1 else 0.0


def Hmax_iv(pa, pb):
    def h(q):
        q = I(q)
        return -q * iv.log(q) - (1 - q) * iv.log(1 - q)
    if pb <= Fr(1, 2):
        return h(pb).b if pa > 0 else h(pb).b
    if pa >= Fr(1, 2):
        return h(pa).b
    return iv.log(2).b


def Lb_iv(t, th, dl):
    t, th, dl = I(t), I(th), I(dl)
    return iv.exp(t * dl) * (1 + (1 - iv.exp(-(t * dl))) / (1 - iv.exp((t - th) * dl)))


def rate_ok(pa, pb, lam, al):
    """1 - p + p e^al <= e^{al (p + lam)} for all p in [pa, pb], via the tangent of log at pa:
    psi(p) = ln(1 + p u) - al p <= ln(1 + pa u) + (p - pa) u/(1 + pa u) - al p   (u = e^al - 1),
    linear in p, so it suffices at p = pa and p = pb."""
    u = iv.exp(I(al)) - 1
    A, L = I(al), I(lam)
    base = iv.log(1 + I(pa) * u)
    at_a = base - A * (I(pa) + L)
    at_b = base + (I(pb) - I(pa)) * u / (1 + I(pa) * u) - A * (I(pb) + L)
    return at_a.b <= 0 and at_b.b <= 0


def rat(x, den=10 ** 8):
    return Fr(x).limit_denominator(den)


def largest_rate(pa, pb, lam, guess):
    """largest alpha (geometric search below guess) with the forward rate condition on [pa, pb]."""
    a = guess
    for _ in range(400):
        ar = rat(a, 10 ** 9)
        if ar > 0 and rate_ok(pa, pb, lam, ar):
            return ar
        a *= 0.98
    return None


# ------------------------------------------------------------------ round 1
def r1_cell(pa, pb, m, E1):
    """find (lam, t, alpha) satisfying the round-1 cell conditions; return slack (wires/column) or None."""
    pm = float((pa + pb) / 2)
    v = pm * (1 - pm)
    Hm = Hmax_iv(pa, pb)
    c1 = math.log(15 / float(ETA1)) / 16
    best = None
    sd = math.sqrt(m * v)
    scale = math.sqrt(v * (float(Hm) + c1 + 0.7) / m) if v > 0 else 1e-6
    cands = [scale * k for k in (0.3, 0.5, 0.7, 1.0, 1.4, 2.0, 3.0)]
    for lam0 in cands:
        lam = rat(lam0, 10 ** 14)
        if lam <= 0:
            continue
        if float(pb) + float(lam) < 1:
            th = NP.theta_star(float(pb), float(lam))
        else:
            th = 60.0
        al = largest_rate(pa, pb, lam, min(max(th, 1e-6) * 1.5, 60.0))
        if al is None:
            continue
        for ft in [0.3, 0.45, 0.6, 0.75, 0.85]:
            t = rat(ft * float(al), 10 ** 12)
            dl = DELTA_T / t
            lhs = (I(lam) * m + (iv.mpf(Hm) + iv.log(Lb_iv(t, al, dl)) + iv.log(I(15) / I(ETA1)) / 16) / I(t)).b
            slack = float(E1) / 2 * m - float(lhs)
            if best is None or slack > best[0]:
                best = (slack, lam, t, al, float(lhs))
    return best


def plan_round1(E1):
    """cover (0, 1) with cells; returns worst per-column lhs and the cells."""
    cells = []
    # geometric near 0 and 1, uniform in the middle
    edges = [Fr(0)]
    x = Fr(1, 10 ** 12)
    while x < Fr(1, 32):
        edges.append(x); x = rat(float(x) * 2.5, 10 ** 14)
    for k in range(1, 64):
        edges.append(Fr(k, 64))
    x = Fr(1, 32)
    tail = []
    while x > Fr(1, 10 ** 12):
        tail.append(1 - x); x = rat(float(x) / 2.5, 10 ** 14)
    edges += sorted(set(tail)) + [Fr(1)]
    edges = sorted(set(e for e in edges if 0 <= e <= 1))
    worst = 0.0
    for pa, pb in zip(edges[:-1], edges[1:]):
        r = r1_cell(max(pa, Fr(1, 10 ** 13)), min(pb, 1 - Fr(1, 10 ** 13)), M_LO, E1)
        if r is None or r[0] < 0:
            return None, (pa, pb, r)
        cells.append((pa, pb) + r[1:4])
        worst = max(worst, r[4])
    return worst, cells


def main():
    # round 1: find the smallest E1 for which every cell closes (bisection on a grid)
    lo, hi = 3.0e-4, 4.5e-4
    ok_cells = None
    for _ in range(14):
        mid = (lo + hi) / 2
        worst, cells = plan_round1(rat(mid, 10 ** 12))
        if worst is None:
            lo = mid
        else:
            hi = mid; ok_cells = cells
        print(f"  E1 = {mid:.5e}: {'closes' if worst is not None else 'fails at ' + str(cells[:2])}", flush=True)
    print(f"round 1 (Lean form): E1 = {hi:.5e} with {len(ok_cells)} cells")


# ------------------------------------------------------------------ round 2
def r2_cell(pa, pb, m, E1, gprime, lnG):
    """(lam, t, alpha, beta) for the round-2 cell; returns (slack_wires, params, lhs) or None."""
    pm = float((pa + pb) / 2)
    v = pm * (1 - pm)
    Hm = Hmax_iv(pa, pb)
    Rn = float(E1) * m + gprime
    c2 = (lnG + math.log(15 / float(ETA2))) / 16
    best = None
    scale = math.sqrt(v * (float(Hm) + c2 + 1.0) / Rn) if v > 0 else 1e-6
    for k in (0.4, 0.55, 0.7, 0.85, 1.0, 1.2, 1.5, 2.0):
        lam = rat(scale * k, 10 ** 14)
        tha = NP.theta_star(float(pb), float(lam)) if float(pb) + float(lam) < 1 else 60.0
        thb = NP.theta_star(1 - float(pa), float(lam)) if 1 - float(pa) + float(lam) < 1 else 60.0
        al = largest_rate(pa, pb, lam, min(max(tha, 1e-6) * 1.5, 60.0))
        be = largest_rate(1 - pb, 1 - pa, lam, min(max(thb, 1e-6) * 1.5, 60.0))
        if al is None or be is None:
            continue
        for ft in (0.3, 0.45, 0.6, 0.75, 0.85):
            t = rat(ft * float(min(al, be)), 10 ** 12)
            dl = DELTA_T / t
            Mc = Lb_iv(t, al, dl) + Lb_iv(t, be, dl) - 1
            lhs = (I(lam) * I(Fr(Rn).limit_denominator(10 ** 6)) +
                   (iv.mpf(Hm) + iv.log(Mc) + iv.mpf(c2)) / I(t)).b
            slack = float(EPS_B) / 2 * m - float(lhs)
            if best is None or slack > best[0]:
                best = (slack, lam, t, al, be, float(lhs))
    return best


def plan_round2(E1):
    g = 2 * math.floor(0.02 * float(E1) * M_LO / 2) + 1
    gprime = (g - 1) / 2
    lnG = math.log(M_HI / g + 2)
    edges = [Fr(0)]
    x = Fr(1, 10 ** 12)
    while x < Fr(1, 32):
        edges.append(x); x = rat(float(x) * 2.5, 10 ** 14)
    for k in range(2, 33):
        edges.append(Fr(k, 64))
    edges = sorted(set(edges))
    worst = 0.0
    cells = []
    for pa, pb in zip(edges[:-1], edges[1:]):
        r = r2_cell(max(pa, Fr(1, 10 ** 13)), pb, M_LO, E1, gprime, lnG)
        if r is None or r[0] < 0:
            return None, (pa, pb, r), g
        cells.append((pa, pb) + r[1:5])
        worst = max(worst, r[5])
    return worst, cells, g


def main2(E1):
    worst, cells, g = plan_round2(E1)
    if worst is None:
        print(f"round 2 (Lean form) FAILS at E1 = {float(E1):.5e}: {cells}")
        return
    print(f"round 2 (Lean form): worst per-column lhs {worst:.2f} wires vs (eps_B/2) m = "
          f"{float(EPS_B) / 2 * M_LO:.2f}; d = {2 * worst / M_LO:.4e} vs eps_B {float(EPS_B):.4e}; "
          f"{len(cells)} cells (p <= 1/2), grid spacing g = {g}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == 'r2':
        main2(rat(float(sys.argv[2]), 10 ** 12))
    else:
        main()
