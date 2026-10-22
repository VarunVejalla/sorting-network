#!/usr/bin/env python3
"""All-d width bound from formulas only (INDUCTION-v6.md sec. 13-14): no simulation input.

Order-0 ratio at a sender u with receiver capacity c' = A nu c (S4):
    ratio = hw/(2 mu) + D + eps_B (a/c)/(2 mu) + ROUND,            hw = inherited half-width / c
    D = delta A^2 k (k/(2(1 - (delta k A)^2)) + 1)/2               (deep terms k Delta_1/2 + mu delta A^2 k c, over mu c')
Inheritance (child hw relative to the child's capacity), sender p with half-width hw_p and fill s = a/c:
    E  (end, both sides beyond the band, S3):      mu/2 + hw_p/2 + tail s/2
    En (end, near side Property B):               mu/2 + hw_p/2 + (eps_B/2 + tail) s/4
    Eb (end, both sides Property B; S3 non-generic): mu/2 + hw_p/2 + eps_B s/4
    (end loc = (cB + cL)/(2c') = (cB + cL)/(4c))
    S  (spilled):                                 mu/2 + hw_p/2 + eps_B s/4        (sender s <= 0.00847, S4)
    I  (interior):                                mu/2 + hw_p/4 + eps_B s/8 + k Delta_1/(8c)
    T  (topRise; last width-setting send is topDesc): mu/2 + eps_B s/2 ... capped: hw_T = mu/2 + eps_B s_max/4
Fill bounds: S1 s <= 1.01595 for E, I, S, T receivers; S2 s <= 0.1735 for En, Eb receivers.
Every sender group may feed every receiver group (complete box). Exact Fractions."""
import os
from fractions import Fraction as Fr

A, k, nu = 16, 16, Fr(1, 8)
EPSB = Fr(225, 10 ** 7)
DELTA = Fr(1, 10 ** 6)
TAIL = Fr(360899, 10 ** 11)           # certified band tail at W = 2^17 (cert_tail_W2e17.out)
ROUND = Fr(1, 100)
S_DENSE = Fr(os.environ.get("AC_BOUND", "1.01595"))
S_SPARSE = Fr(os.environ.get("AC_EB", "0.1735"))
S_SPILL = Fr(847, 100000)
# mu: the order-0 budget fraction of the package (width_sim/package_point), exact value from the d=22 dump
import json
mu = Fr(json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "transbox_443_analytic_d22.json")))["mu"])

D1c = mu * DELTA * k * A * A / (1 - (DELTA * k) ** 2 * A * A)     # Delta_1 / c
Dterm = (k * D1c / 2 + mu * DELTA * A * A * k) / (mu * A * nu)    # over mu c'
fill = {"E": S_DENSE, "I": S_DENSE, "S": S_DENSE, "T": S_DENSE, "En": S_SPARSE, "Eb": S_SPARSE}
HW_T = mu / 2 + EPSB * S_DENSE / 4


def inherit(q, hwp, s):
    if q == "E":
        return mu / 2 + hwp / 2 + TAIL * s / 2
    if q == "En":
        return mu / 2 + hwp / 2 + (EPSB / 2 + TAIL) * s / 4
    if q == "Eb":
        return mu / 2 + hwp / 2 + EPSB * s / 4
    if q == "S":
        return mu / 2 + hwp / 2 + EPSB * min(s, S_SPILL) / 4
    if q == "I":
        return mu / 2 + hwp / 4 + EPSB * s / 8 + k * D1c / 8
    raise KeyError(q)


groups = list(fill)
recv = [g for g in groups if g != "T"]
hw = {g: 10 * mu for g in groups}
hw["T"] = HW_T
for _ in range(200):
    new = {q: max(inherit(q, hw[p], fill[p]) for p in groups) for q in recv}
    for q in recv:
        hw[q] = min(hw[q], new[q])
# exact post-fixed point check
ok = all(max(inherit(q, hw[p], fill[p]) for p in groups) <= hw[q] for q in recv)
worst = Fr(0)
print("mu = %.6e   D = %.6f   (all inputs are formulas; certified tail %.5e)" % (mu, Dterm, TAIL))
for g in groups:
    r = hw[g] / (2 * mu) + Dterm + EPSB * fill[g] / (2 * mu) + ROUND
    worst = max(worst, r)
    print("group %-3s fill <= %.5f  hw <= %.4f mu  ratio <= %.6f" % (g, fill[g], hw[g] / mu, r))
print("post-fixed point:", ok, "  worst ratio (formulas only): %.6f" % worst, " < 1:", worst < 1)
