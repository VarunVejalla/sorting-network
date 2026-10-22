#!/usr/bin/env python3
"""S2 / S4 schedule check (INDUCTION-v6.md sec. 13), straight from Chvatal's schedule (flowsim.Par), at a
large depth d so the top (alpha) never meets the bottom in the window checked. For every sender u at
(i, t) whose end child w1 = level i+1 was NOT a generic sender at t-1 (inactive, botRise, or botDesc:
the cases where theta_1(w1) may be capped or absent, so the near side or S3 may fail), report w1's role at
t+1 and Chvatal's alloc/cap there. S2 needs: role in {botRise (no tagged send), botDesc} and
alloc/cap <= 2^-2.5 - 2e-5 (design bag at botDesc <= alloc + 2e-5 c, S1 probe). Exact Fractions."""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "slackfree"))
from flowsim import Par  # noqa: E402

P = Par(4, 4, 3)
SPILL_AC = Fr(1, 64)   # spills only at a/c <= 0.0076 (width_sim spill_a_over_c_max); lemma S4c
d = 400
worst, bad, seen = Fr(0), 0, {}
for t in range(2, 300):
    if P.tf(d) <= t + 1:
        break
    for i in range(P.alpha(d, t), P.omega(d, t) + 1):
        if not P.active(d, i, t) or i + 1 > d:
            continue
        r_u = P.role(d, i, t)
        if r_u in ("botRise", "topDesc"):
            continue
        a_m1 = P.active(d, i + 1, t - 1)
        r_m1 = P.role(d, i + 1, t - 1) if a_m1 else "inact"
        if r_m1 == "mid" or r_m1 == "topRise":
            continue                       # generic: S3 and dB >= ~0.027 analytic
        if r_m1 == "botDesc" and P.alloc(d, i + 1, t - 1) / P.cap(d, i + 1, t - 1) > SPILL_AC:
            continue                       # botDesc without spill: theta_1 uncapped, generic
        a_p1 = P.active(d, i + 1, t + 1)
        r_p1 = P.role(d, i + 1, t + 1) if a_p1 else "inact"
        ratio = P.alloc(d, i + 1, t + 1) / P.cap(d, i + 1, t + 1) if a_p1 else Fr(0)
        key = (r_u, r_m1, r_p1)
        seen[key] = max(seen.get(key, Fr(0)), ratio)
        if r_p1 == "mid" or r_p1 == "topRise" or (r_p1 == "botDesc" and ratio > Fr(1, 8)):
            bad += 1
        if r_p1 == "botDesc":
            worst = max(worst, ratio)
for k_, v in sorted(seen.items()):
    print("u=%-8s w1(t-1)=%-8s w1(t+1)=%-8s  alloc/cap(w1,t+1) max %.6f" % (k_ + (float(v),)))
print("checked t < %d at d = %d;  botDesc receivers alloc/cap max = %s = %.6f;  violations: %d" % (t, d, worst, float(worst), bad))
print("S2 bound: a/c <= alloc/cap + 2e-5 <= %.6f  vs 2^-2.5 = %.6f" % (float(worst) + 2e-5, 2 ** -2.5))
