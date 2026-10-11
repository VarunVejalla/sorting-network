"""Certified check of the two-round F proof (F2ROUND.md), interval arithmetic (mpmath.iv, outward rounding).

Usage:  python cert.py F G1 G2 C_NUM C_DEN B
Defaults: f=131040, g1=52416 (=2f/5), g2=104832 (=4f/5), c=1/3, b=7000.

Every quantity is a rigorous upper bound on ln(failure probability) for ONE orientation, using the
closed forms and worst points derived in F2ROUND.md sec. 3-4.  The script prints the interval upper
ends and asserts all preconditions; it exits non-zero if any check fails.
"""
import sys
from fractions import Fraction as Fr
from mpmath import iv, mpf
iv.dps = 60

def I(x):
    x = Fr(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)

def up(x):   # upper end of an interval as mpf
    return x.b

def lo(x):
    return x.a

args = sys.argv[1:]
f = int(args[0]) if len(args) > 0 else 131040
g1 = int(args[1]) if len(args) > 1 else 2 * f // 5
g2 = int(args[2]) if len(args) > 2 else 4 * f // 5
c = Fr(int(args[3]), int(args[4])) if len(args) > 4 else Fr(1, 3)
b = Fr(args[5]) if len(args) > 5 else Fr(7000)
g0 = g1
J = 86_000_000
D = Fr(128, 4095) * f            # delta*f  (= 4096 for f = 131040)
Dl, Phi = g2 - g1, f - g2
e = iv.e
ok = True

def check(name, cond):
    global ok
    print(("  OK   " if cond else "  FAIL ") + name)
    ok = ok and bool(cond)

print(f"f={f} g0=g1={g1} g2={g2} Delta={Dl} Phi={Phi} c={c} b={b} delta*f={D} ({float(D):.3f})")
# ---------------- preconditions (exact rationals) ----------------
check("0 < g1 < g2 < f", 0 < g1 < g2 < f)
check("Delta+1 >= delta f   (R1 Chernoff validity, D/(Delta+1) <= 1)", Dl + 1 >= D)
check("f-g0+1 >= delta f    (SR Chernoff validity)", f - g0 + 1 >= D)
check("(g1+1)^2 >= delta f  (tops bound monotone in k)", (g1 + 1) ** 2 >= D)
check("c*Delta >= J/(g1+1)  (R1a decreasing in n)", c * Dl >= Fr(J, g1 + 1))
check("b >= J/(g1+1)        (R1b decreasing in n)", b >= Fr(J, g1 + 1))
check("c <= 1/2             (R2 nonincreasing in n: ceil(cE)+1 <= E for E>=2)", c <= Fr(1, 2))
check("Phi >= 2 b delta f / J (R2 Chernoff validity)", Phi >= 2 * b * D / J)
check("(c+1/2)^2 <= b J/(4 delta f)  (kappa^2 <= n(B-1), Y-count monotone in k)", (c + Fr(1, 2)) ** 2 <= b * J / (4 * D))

Dv, Jv, cv, bv = I(D), I(J), I(c), I(b)
ln = iv.log

# ---------------- SR: small ranks, worst n = J/D ----------------
n = Jv / Dv
K = Jv / (g0 + 1)
T0 = I(f - g0 + 1)
SR = ln(K + 1) + K * ln(e ** 2 * n * (g0 + 1) ** 2 / Jv) + ln(e * n) + T0 * ln(e * Jv / (n * T0))
print("SR    ln P <= %.6g" % up(SR))

# ---------------- R1a ----------------
ts = Jv / (g1 + 1) * ln(e ** 2 * I(g1 + 1) ** 2 / Dv)          # tops slope per E
beta = ln(e * Jv / (cv * Dv)) + (Dl + 1) * ln(e * Dv / (Dl + 1))
lam_a = -(ts + cv * beta)
check("beta < 0", up(beta) < 0)
check("lambda_a > 0", lo(lam_a) > 0)
alpha = Jv / (g1 + 1)

def geo_sums(r, E0):
    """upper bounds for S0=sum_{E>=E0} r^E, S1=sum E r^E, S2=sum E^2 r^E (0<r<1, interval)."""
    S0k = 1 / (1 - r)
    S1k = r / (1 - r) ** 2
    S2k = r * (1 + r) / (1 - r) ** 3
    rE0 = r ** E0
    return rE0 * S0k, rE0 * (S1k + E0 * S0k), rE0 * (S2k + 2 * E0 * S1k + E0 ** 2 * S0k)

r_a = iv.exp(-lam_a)
S0, S1, S2 = geo_sums(r_a, 2)
# sum_E exp(ln(alpha E+1) + E ts + (cE+1) beta) <= e^beta * sum (alpha E + 1) r_a^E
Sum_a = iv.exp(beta) * (alpha * S1 + S0)
print("R1a   lambda_a=%.6g  beta=%.6g  ln sum_E P <= %.6g" % (lo(lam_a), up(beta), up(ln(Sum_a))))

# ---------------- R1b: psi* by certified bisection on psi' (psi concave) ----------------
def psi(s):
    return s * ln(e * Jv / (s * Dv)) + (Dl * s + bv) * ln(e * Dv * s / (Dl * s + bv))

def dpsi(s):
    return ln(Jv / (s * Dv)) + Dl * ln(e * Dv * s / (Dl * s + bv)) + bv / s

slo, shi = I(Fr(1, 10 ** 30)), I(10 ** 30)
check("psi'(lo) > 0", lo(dpsi(slo)) > 0)
check("psi'(hi) < 0", up(dpsi(shi)) < 0)
for _ in range(300):
    mid = iv.mpf(iv.sqrt(slo * shi).a)
    d = dpsi(mid)
    if lo(d) > 0:
        slo = mid
    elif up(d) < 0:
        shi = mid
    else:
        break
psistar = psi(slo) + dpsi(slo) * (shi - slo)        # concavity: psi(s*) <= psi(slo)+psi'(slo)(s*-slo)
lam_b = -(ts + psistar)
check("lambda_b > 0", lo(lam_b) > 0)
r_b = iv.exp(-lam_b)
S0, S1, S2 = geo_sums(r_b, 2)
# sum_E (cE+1)(alpha E+1) r_b^E
Sum_b = cv * alpha * S2 + (cv + alpha) * S1 + S0
print("R1b   psi*=%.6g at sigma~%.4g  lambda_b=%.6g  ln sum_E P <= %.6g" % (up(psistar), float(slo.a), lo(lam_b), up(ln(Sum_b))))

# ---------------- R2 ----------------
LY = ln(e ** 2 * Jv * bv / (Dv * cv ** 2))
E2 = 2000
# tail E >= E2+1: (E-1)/E >= E2/(E2+1)
q0 = ln(Jv * Phi * E2 / ((E2 + 1) * Dv * e * bv))
tau = Jv / Dv * iv.exp(-Phi * q0)
Lam = q0 - cv * LY - tau
check("Lambda (R2 tail slope) > 0", lo(Lam) > 0)

def r2_exact(E):
    """regime I at the worst point n=(E-1)J/D (requires A<=1)."""
    E = I(E)
    nlo = (E - 1) * Jv / Dv
    kap = cv * E + 1
    Bm1 = bv * E
    lnY = ln(kap + 1) + kap * ln(e ** 2 * nlo * Bm1 / kap ** 2)
    q = ln(nlo * Phi / (e * Bm1))
    A = 1 + ln(nlo) - Phi * q
    assert up(A) <= 1, "regime I needs A<=1"
    return lnY + ln(nlo) + A - E * q

worstI = max(up(r2_exact(E)) for E in range(2, E2 + 1))
SumI = sum(iv.exp(r2_exact(E)) for E in range(2, E2 + 1))
# regime II tail E > E2: exp(ln(cE+2) + (cE+1)LY + ln(EJ/D) + 1 + E tau - E q0)
#   <= e^{LY+1} (J/D) * sum (cE+2) E e^{-Lam E} ... (cE+2)E <= c E^2 + 2E
r_2 = iv.exp(-Lam)
S0, S1, S2 = geo_sums(r_2, E2 + 1)
SumII = iv.exp(LY + 1) * (Jv / Dv) * (cv * S2 + 2 * S1)
print("R2    worst ln P (E<=%d) <= %.6g ; Lambda=%.4g ; ln tail sum <= %.6g ; ln total <= %.6g"
      % (E2, worstI, lo(Lam), up(ln(SumII)), up(ln(SumI + SumII))))

P1 = iv.exp(SR) + Sum_a + Sum_b
P2 = SumI + SumII
print("sigma1 F-failure, both orientations: ln(2 P1) <= %.6g" % up(ln(2 * P1)))
print("sigma2 F-failure, both orientations: ln(2 P2) <= %.6g" % up(ln(2 * P2)))
check("2*P1 <= 1/1000", up(2 * P1) <= mpf(1) / 1000)
check("2*P2 <= 1/1000", up(2 * P2) <= mpf(1) / 1000)

# ================= Lean-friendly closed forms (no psi*, no per-E evaluation) =================
print("--- closed-form (Lean-friendly) bounds ---")
sig_coef = ln(e * Jv / Dv) + Dl * ln(e * Dv / Dl)
check("crude psi: sigma coefficient ln(eJ/D)+Delta ln(eD/Delta) <= 0", up(sig_coef) <= 0)
lam_bc = -(ts + bv * ln(e * Dv / Dl) + 1 / e)
check("crude lambda_b > 0", lo(lam_bc) > 0)
S0, S1, S2 = geo_sums(iv.exp(-lam_bc), 2)
Sum_bc = cv * alpha * S2 + (cv + alpha) * S1 + S0
q0p = ln(Jv * Phi / (2 * Dv * e * bv))
LamI = q0p - cv * LY
N0 = 10 ** 6
check("regime I valid up to N0: ln(N0 J/D)+1 <= Phi q0'", up(ln(N0 * Jv / Dv) + 1) <= lo(Phi * q0p))
check("regime I slope q0' - c LY > 0", lo(LamI) > 0)
# sum_{E>=2} exp(ln(cE+2)+(cE+1)LY+2ln(EJ/D)+1-(Phi+E)q0') <= e^{LY+1-Phi q0'}(J/D)^2 sum (cE^3+2E^2) e^{-LamI E}
r_I = iv.exp(-LamI)
S0, S1, S2 = geo_sums(r_I, 2)
S3 = r_I ** 2 * (r_I * (1 + 4 * r_I + r_I ** 2) / (1 - r_I) ** 4 + 6 * (r_I * (1 + r_I) / (1 - r_I) ** 3)
                 + 12 * (r_I / (1 - r_I) ** 2) + 8 / (1 - r_I))   # sum_{k>=0} (k+2)^3 r^(k+2)
SumIc = iv.exp(LY + 1 - Phi * q0p) * (Jv / Dv) ** 2 * (cv * S3 + 2 * S2)
qN = ln(Jv * Phi * N0 / ((N0 + 1) * Dv * e * bv))
tauN = Jv / Dv * iv.exp(-Phi * qN)
LamN = qN - cv * LY - tauN
check("regime II slope > 0", lo(LamN) > 0)
S0, S1, S2 = geo_sums(iv.exp(-LamN), N0 + 1)
SumIIc = iv.exp(LY + 1) * (Jv / Dv) * (cv * S2 + 2 * S1)
P1c = iv.exp(SR) + Sum_a + Sum_bc
P2c = SumIc + SumIIc
print("closed: lambda_b'=%.6g LamI=%.6g LamII=%.6g ; ln(2P1) <= %.6g ; ln(2P2) <= %.6g"
      % (lo(lam_bc), lo(LamI), lo(LamN), up(ln(2 * P1c)), up(ln(2 * P2c))))
check("closed 2*P1 <= 1/1000", up(2 * P1c) <= mpf(1) / 1000)
check("closed 2*P2 <= 1/1000", up(2 * P2c) <= mpf(1) / 1000)
print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
