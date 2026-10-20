#!/usr/bin/env python3
"""Generate AKS/Sub800/R1Cells.lean: the concrete round-1 cells (LEAN-PLAN W4.5) as checked data.

Cells and parameters come from lean_numerics_plan.py (round 1). Every transcendental value is
replaced by an exact rational witness, checked here in exact arithmetic with the same Taylor bound
that `ExpBounds.exp_le'` / `le_exp'` use, so the generated `norm_num` goals are true.

  usage: python -I gen_r1_cells.py

The `tac_*` helpers (tactic-proof emitters) are still used by `gen_r2_cells.py` and `gen_fringe.py`.
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lean_numerics_plan as P  # noqa: E402

E1 = Fr(36842, 10 ** 8)          # 3.6842e-4
M = P.M_LO
ETA = Fr(1, 100)


def short(x, sig=6):
    x = Fr(x)
    if x == 0:
        return Fr(0)
    e = math.floor(math.log10(abs(float(x))))
    return Fr(round(x * Fr(10) ** (sig - 1 - e))) / Fr(10) ** (sig - 1 - e)


def taylor(y, up):
    p = 1 + y + y ** 2 / 2 + y ** 3 / 6 + y ** 4 / 24 + y ** 5 / 120
    r = abs(y) ** 6 * Fr(7, 4320)
    return p + r if up else p - r


def kfor(x):
    k = 0
    while abs(x) / 2 ** k > Fr(1, 64):
        k += 1
    return k


def exp_up(x):
    k = kfor(x)
    return k, taylor(Fr(x) / 2 ** k, True) ** (2 ** k)


def exp_lo(x):
    k = kfor(x)
    return k, taylor(Fr(x) / 2 ** k, False) ** (2 ** k)


def round_up(v, sig=20):
    v = Fr(v)
    e = math.floor(math.log10(abs(float(v)))) if v != 0 else 0
    q = Fr(10) ** (sig - 1 - e)
    r = Fr(math.ceil(v * q)) / q
    assert r >= v
    return r


def round_dn(v, sig=20):
    v = Fr(v)
    e = math.floor(math.log10(abs(float(v)))) if v != 0 else 0
    q = Fr(10) ** (sig - 1 - e)
    r = Fr(math.floor(v * q)) / q
    assert r <= v
    return r


NN = "(by (try simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero, div_one]); norm_num)"


def L(x):
    x = Fr(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"


def _abs1(zexpr, z):
    if z >= 0:
        return f"(by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ {zexpr})]; norm_num)"
    return f"(by rw [abs_of_neg (by norm_num : {zexpr} < 0)]; norm_num)"


def _absrw_goal(zexpr, z):
    if z >= 0:
        return f"rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ {zexpr})]"
    return f"rw [abs_of_neg (by norm_num : {zexpr} < 0)]"


DIG = 25


# Top-level certificate theorems emitted by `tac_exp_le` / `tac_le_exp`, flushed by the caller
# before the theorem that uses them (a `decide +kernel` inside a proof blocks parallel checking).
CERTS = []
CERT_COUNT = [0]


def flush_certs():
    out = "".join(CERTS)
    CERTS.clear()
    return out


def _cert_thm(kind, x, v, cert, xr=None):
    from certgen import Q
    name = f"xc{CERT_COUNT[0]}"
    CERT_COUNT[0] += 1
    if xr is None:
        CERTS.append(f"theorem {name} : ExpCert.{kind} {Q(x)} {cert} {Q(v)} = true := by decide +kernel\n")
    else:
        CERTS.append(f"theorem {name} : ExpCert.{kind} {Q(x)} {Q(xr)} {cert} {Q(v)} = true := by decide +kernel\n")
    return name


def tac_exp_le(name, xexpr, x):
    """returns (code, U): code proves `have name : Real.exp (xexpr) ≤ U` from an `ExpCert`
    certificate (a top-level theorem in `CERTS`), taken at `max(x, certgen.XCAP)`."""
    from certgen import cert_up_capped
    x = Fr(x)
    cert, U, xr = cert_up_capped(x)
    if xr == x:
        thm, snd = _cert_thm("expUp", x, U, cert), "expUp_sound"
    else:
        thm, snd = _cert_thm("expUpLe", x, U, cert, xr), "expUpLe_sound"
    code = (f"  have {name} : Real.exp ({xexpr}) ≤ {L(U)} := by\n"
            f"    have h := ExpCert.{snd} {thm}\n"
            f"    push_cast at h; first | exact h | (convert h using 2 <;> norm_num)\n")
    return code, U


def tac_le_exp(name, xexpr, x):
    """returns (code, Lo): code proves `have name : Lo ≤ Real.exp (xexpr)` from an `ExpCert`
    certificate (a top-level theorem in `CERTS`)."""
    from certgen import cert_lo
    x = Fr(x)
    cert, lo = cert_lo(x)
    thm = _cert_thm("expLo", x, lo, cert)
    code = (f"  have {name} : {L(lo)} ≤ Real.exp ({xexpr}) := by\n"
            f"    have h := ExpCert.expLo_sound {thm}\n"
            f"    push_cast at h; first | exact h | (convert h using 2 <;> norm_num)\n")
    return code, lo


def log_upper(y):
    """rational A with y <= exp(A) (A slightly above log y)."""
    y = Fr(y)
    if y == 1:
        return Fr(0)
    lg = math.log1p(float(y - 1)) if abs(float(y - 1)) < 0.5 else math.log(float(y))
    A = round_up(Fr(lg) * (1 + Fr(1, 10 ** 15)) if lg > 0 else Fr(lg) * (1 - Fr(1, 10 ** 15)), 20)
    step = abs(A) / 10 ** 15 + Fr(1, 10 ** 40)
    from certgen import cert_lo
    while cert_lo(A)[1] < y:
        A += step
        step *= 2
    return A


def tac_y_le_exp(name, yexpr, y, A):
    if A == 0:
        return (f"  have {name} : {yexpr} ≤ Real.exp (0 : ℝ) := by\n"
                f"    rw [Real.exp_zero]; (try simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero, div_one]); norm_num\n")
    code, lo = tac_le_exp(name + "e", L(A), A)
    assert lo >= y
    return code + f"  have {name} : {yexpr} ≤ Real.exp {L(A)} := le_trans {NN} {name}e\n"


def main():
    from certgen import C, Q, cert_lo, cert_up  # noqa: F401
    worst, cells = P.plan_round1(E1)
    assert worst is not None, "planner failed"
    cA1, A1 = cert_up(Fr(1, 1000))
    cB1, B1 = cert_lo(Fr(-1, 1000))
    L1500 = log_upper(Fr(1500))
    cL, lo = cert_lo(L1500)
    assert lo >= 1500
    out = ["import AKS.Sub800.CellCheck1\n",
           "/-! Generated by `gen_r1_cells.py` — do not edit. Concrete round-1 cells as checked data\n"
           "(`CellCheck1`): one `decide +kernel` checks every cell and its `exp`/`log` certificates. -/\n",
           "namespace R1Cells\n"]
    out.append("def glob : CellCheck1.Glob where\n"
               f"  E1 := {Q(E1)}\n  M := {Q(M)}\n  η := {Q(ETA)}\n"
               f"  A1 := {Q(A1)}\n  B1 := {Q(B1)}\n  L1500 := {Q(L1500)}\n"
               f"  cA1 := {cA1}\n  cB1 := {cB1}\n  cL := {cL}\n")
    recs = []
    for idx, (pa, pb, lam0, t0, al0) in enumerate(cells):
        chosen = None
        for sig in (6, 8, 10, 14, None):
            if sig is None:
                lam, t, al = Fr(lam0), Fr(t0), Fr(al0)
            else:
                lam, t, al = short(lam0, sig), short(t0, sig), short(al0, sig)
            if not (0 < t < al):
                continue
            cEu, Eu = cert_up(al)
            cEl, El = cert_lo(al)
            cQ, Qv = cert_lo(al * (pa + lam))
            if not (1 + pa * (Eu - 1) <= Qv):
                continue
            Lq = log_upper(1 + pa * (Eu - 1))
            if not (Lq + (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) <= al * (pb + lam)):
                continue
            chosen = (lam, t, al, cEu, Eu, cEl, El, cQ, Qv, Lq)
            break
        assert chosen is not None, ("rate", idx)
        lam, t, al, cEu, Eu, cEl, El, cQ, Qv, Lq = chosen
        cLq, lo = cert_lo(Lq)
        assert lo >= 1 + pa * (Eu - 1)
        cx = (t - al) * Fr(1, 1000) / t
        cC1, C1 = cert_up(cx)
        assert C1 < 1
        y2 = A1 * (1 + (1 - B1) / (1 - C1))
        Lq2 = log_upper(y2)
        cLq2, lo = cert_lo(Lq2)
        assert lo >= y2
        if pb <= Fr(1, 2):
            q = pb
        elif pa >= Fr(1, 2):
            q = pa
        else:
            q = None
        if q is None:
            Hq = Fr(6932, 10000)
            c2, l2 = cert_lo(Hq)
            assert l2 >= 2
            ent = f".mid {Q(Hq)} {c2}"
        else:
            A = log_upper(1 / q)
            B = log_upper(1 / (1 - q))
            cA, la = cert_lo(A)
            cB, lb = cert_lo(B)
            assert la >= 1 / q and lb >= 1 / (1 - q)
            Hq = q * A + (1 - q) * B
            ent = f".atQ {Q(A)} {Q(B)} {cA} {cB}"
        fin = lam * M + (Hq + Lq2 + L1500 / 16) / t
        assert fin <= E1 / 2 * M, ("budget", idx, float(fin), float(E1 / 2 * M))
        recs.append("  { pa := " + Q(pa) + ", pb := " + Q(pb) + ", lam := " + Q(lam) + ", tt := " + Q(t)
                    + ", al := " + Q(al) + ",\n    Eu := " + Q(Eu) + ", El := " + Q(El) + ", Q := " + Q(Qv)
                    + ", Lq := " + Q(Lq) + ", C1 := " + Q(C1) + ", Lq2 := " + Q(Lq2)
                    + ",\n    cEu := " + cEu + ",\n    cEl := " + cEl + ",\n    cQ := " + cQ
                    + ",\n    cLq := " + cLq + ",\n    cC1 := " + cC1 + ",\n    cLq2 := " + cLq2
                    + ",\n    ent := " + ent + " }")
    out.append("set_option maxRecDepth 100000 in")
    out.append(f"/-- The {len(recs)} cells, contiguous from `0` to `1`. -/")
    out.append("noncomputable def cells : List CellCheck1.Cell := [\n" + ",\n".join(recs) + "]\n")
    out.append("theorem cells_checked : CellCheck1.allOK glob cells = true := by decide +kernel\n")
    out.append("open Classical in")
    out.append("/-- **Round 1 of the walk bound, numerically closed**: for every `n ≥ 16` and every row count")
    out.append(f"`m ≥ {M}`, at most 1/100 of the scrambles fail the pipeline Property B with `E1 = {float(E1):.5e}`. -/")
    out.append("theorem round1_numeric {m n : ℕ} (hn : 16 ≤ n) (hmM : (" + str(M) + " : ℝ) ≤ m) (hm : 0 < m) :")
    out.append(f"    ((Finset.univ.filter fun σ : Chvatal.Scramble m n => ¬ Chvatal.HasCombinatorialPropertyBOnPipeline σ {L(E1)}).card : ℝ) ≤")
    out.append(f"      {L(ETA)} * ((Fintype.card (Chvatal.Scramble m n) : ℕ) : ℝ) := by")
    out.append("  have hE1 : ((glob.E1 : ℚ) : ℝ) = " + L(E1) + " := by norm_num [glob]")
    out.append("  have hη : ((glob.η : ℚ) : ℝ) = " + L(ETA) + " := by norm_num [glob]")
    out.append("  have hM : ((glob.M : ℚ) : ℝ) = " + L(M) + " := by norm_num [glob]")
    out.append("  have h := CellCheck1.round1_of_cert glob cells cells_checked hn (by rw [hM]; exact hmM) hm")
    out.append("  rwa [hE1, hη] at h\n")
    out.append("end R1Cells\n")
    path = os.path.join(HERE, "..", "..", "AKS", "Sub800", "R1Cells.lean")
    open(path, "w", encoding="utf-8", newline="\n").write("\n".join(out))
    print(f"wrote {path}: {len(recs)} cells, E1 = {float(E1):.5e}")


if __name__ == "__main__":
    main()
