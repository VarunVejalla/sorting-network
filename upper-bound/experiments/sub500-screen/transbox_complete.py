#!/usr/bin/env python3
"""Complete coarse box (INDUCTION-v6.md sec. 13): ALL transitions p -> q among the groups E, En, I
(q != T: topRise nodes inherit nothing, Anc = 0), with analytic local caps
    loc(p -> q) = kappa_q * (a/c)_max(p)        (local terms are linear in the sender's a, over c' = 2c)
    kappa_E  = (2 tail)/(4 mu)                  end child, both sides beyond the band (certified tail)
    kappa_En = (eps_B/2 + tail)/(4 mu)          end child, near side at Property B
    kappa_I  = max((eps_B/2 + k D1/2 ...)/(4 mu) [interior], eps_B/(4 mu)·2 [spilled, coef 1])
taken from the dense data divided by the dense a/c max, so the caps are the data's worst case
re-expressed per unit a/c. Group a/c bounds: E, I, T <= 1.0149 (capacity), En <= 2^-2.5 (lemma
near-sparse). Exact arithmetic; inputs rounded up."""
import json
import os
import math
import sys
from fractions import Fraction as Fr

D = json.load(open(sys.argv[1]))
up = lambda x: Fr(math.ceil(Fr(x) * 10 ** 12), 10 ** 12)
mu = Fr(D["mu"]); R = Fr(D["round"])
AC_DATA = up("1.0149")                         # observed a/c max (the data's e, kappa are relative to it)
AC_DENSE = Fr(os.environ.get("AC_BOUND", "1.0149"))   # proved bound (S1): 0.999023 + 64 g*, g* <= 2.645e-4
AC = {"E": AC_DENSE, "I": AC_DENSE, "T": AC_DENSE, "En": up(2 ** -2.5)}

def grp(tag):
    if tag == "topRise":
        return "T"
    kind = tag.split("|")[1] if "|" in tag else "E"
    return {"En": "En", "I": "I", "S": "I"}.get(kind, "E")

G = {}
for tg, td in D["tags"].items():
    g = G.setdefault(grp(tg), dict(rf=Fr(0), e=Fr(0), D=Fr(0)))
    for k_ in ("rf", "e", "D"):
        g[k_] = max(g[k_], up(td[k_]))
for g_ in G:
    if g_ != "En":
        G[g_]["e"] = G[g_]["e"] * AC_DENSE / AC_DATA
# kappa per receiving type from the data: max over dense senders of loc / (a/c)_max(dense)
kap, cof = {}, {}
for pt, tg, cf, lc in D["trans"]:
    q = grp(tg); p = grp(pt)
    if p == "En":
        continue                                        # derive kappas from dense senders only
    kap[q] = max(kap.get(q, Fr(0)), up(lc) / AC_DATA)
    cof[q] = max(cof.get(q, Fr(0)), up(cf))
# spilled children (group S): conservative -- may be dense senders (data of the dense end group E), inherit
# with coef c/c' (as end children) and loc eps_B a/(2c') from a sender with a/c <= 2^-7 (spill only at
# botDesc senders with a/c <= 0.0076, width_sim spill_a_over_c_max)
EPSB_ = Fr(os.environ.get("EPSB", "2.25e-5"))
G["S"] = dict(G["E"])
AC["S"] = AC_DENSE
cof["S"] = cof["E"]
kap["S"] = None
AC_SPILL_SENDER = Fr(847, 100000)   # S4c: spill => capped first child => empty, R(w1') < pi/2 + G_L + o <= 5.29e-4 c, a/c <= k R(w1')/c < 0.00846
# group Eb (S3 non-generic cases: w1 botRise or inactive at t-1): both crossing sides charged at Property B,
# loc = eps_B a/(2c'), receiver sparse (a/c <= 2^-2.5 conservatively, lemma S2'), coef as end children
CERT_TAIL = Fr(os.environ.get("CERT_TAIL", "3.60899e-6"))
AC_EB = Fr(os.environ.get("AC_EB", "0.17678"))   # receiver a/c bound for Eb (capped-theta / non-generic cases)
G["Eb"] = dict(G["E"])
G["Eb"]["e"] = G["E"]["e"] * AC_EB / AC_DENSE      # e linear in the receiver's a/c
AC["Eb"] = AC_EB
cof["Eb"] = cof["E"]
kap["Eb"] = kap["En"] * EPSB_ / (EPSB_ / 2 + CERT_TAIL)
recv = [q for q in G if q != "T"]
send = list(G)
# eps_B a/(2c') per unit a/c with c' >= c / cof_E (cof_E = max c/c'): eps_B * cof_E / 2
SPILL_K = Fr(225, 10 ** 7) * cof["E"] / 2
hw = {g: 10 * mu for g in G}
# topRise receivers: children of a topDesc send carry hw = eps a/(2c') with no inherited term (topDesc senders
# hold no outsiders, exact X; R1 sec. 4); eps = eps_B (Lemma 3.2: non-root topDesc nodes are small; the
# oversized root uses eps_* = mu/k, R1 (4.1), whose a/(k c') is below this cap -- same rule as width_sim)
HW_T = mu / 2 + EPSB_ * AC_DENSE * cof["E"] / 2
hw["T"] = HW_T
def step(hw):
    new = dict(hw)
    for q in recv:
        if q == "S":
            new[q] = max(mu / 2 + cof[q] * hw[p] + SPILL_K * AC_SPILL_SENDER for p in send)
        else:
            new[q] = max(mu / 2 + cof[q] * hw[p] + kap[q] * AC[p] for p in send)
    return new
for _ in range(400):
    n_ = step(hw)
    hw = {g: Fr(math.ceil(min(n_[g], hw[g]) * 10 ** 15), 10 ** 15) for g in G}
    hw["T"] = HW_T
ok = all(step(hw)[q] <= hw[q] for q in recv)
worst = Fr(0)
for g in sorted(G):
    rb = hw[g] * G[g]["rf"] + G[g]["D"] + G[g]["e"] + R
    worst = max(worst, rb)
    print("group %-3s hw <= %.4f mu  ratio <= %.6f" % (g, float(hw[g] / mu), float(rb)))
for q in recv:
    kq = SPILL_K * AC_SPILL_SENDER / mu if q == "S" else kap[q] * AC_DENSE / mu
    print("   -> %-3s coef %.4f loc/mu (dense sender) %.4f" % (q, float(cof[q]), float(kq)))
print("post-fixed point:", ok, "  complete-box worst ratio:", float(worst), " < 1:", worst < 1)
