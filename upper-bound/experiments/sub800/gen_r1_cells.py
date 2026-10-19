#!/usr/bin/env python3
"""Generate lean/R1Cells.lean: the concrete round-1 cells (LEAN-PLAN W4.5) and their proofs.

Cells and parameters come from lean_numerics_plan.py (round 1). Every transcendental value is
replaced by an exact rational witness, checked here in exact arithmetic with the same Taylor bound
that `ExpBounds.exp_le'` / `le_exp'` use, so the generated `norm_num` goals are true.

  usage: python -I gen_r1_cells.py [K_MAX]     (K_MAX: only the first cells, for testing)
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


def tac_exp_le(name, xexpr, x):
    """returns (code, U): code proves `have name : Real.exp (xexpr) ≤ U`."""
    x = Fr(x)
    k = kfor(x)
    zs = [x / 2 ** j for j in range(k + 1)]
    us = [None] * (k + 1)
    us[k] = round_up(taylor(zs[k], True), DIG)
    code = []
    zk = L(zs[k]) if k > 0 else f"(({xexpr}) : ℝ)"
    code.append(f"  have {name}_{k} : Real.exp {zk} ≤ {L(us[k])} :=\n"
                f"    ExpBounds.exp_le_base _ _ {_abs1(zk, zs[k])} (by {_absrw_goal(zk, zs[k])}; norm_num)\n")
    for j in range(k - 1, -1, -1):
        us[j] = round_up(us[j + 1] ** 2, DIG)
        zj = L(zs[j]) if j > 0 else f"({xexpr})"
        code.append(f"  have {name}_{j} : Real.exp {zj} ≤ {L(us[j])} :=\n"
                    f"    ExpBounds.exp_le_sq _ {L(zs[j + 1])} _ _ (by norm_num) {name}_{j + 1} (by norm_num)\n")
    code.append(f"  have {name} := {name}_0\n")
    return "".join(code), us[0]


def tac_le_exp(name, xexpr, x):
    """returns (code, Lo): code proves `have name : Lo ≤ Real.exp (xexpr)`."""
    x = Fr(x)
    k = kfor(x)
    zs = [x / 2 ** j for j in range(k + 1)]
    ls = [None] * (k + 1)
    ls[k] = round_dn(taylor(zs[k], False), DIG)
    assert ls[k] > 0
    code = []
    zk = L(zs[k]) if k > 0 else f"(({xexpr}) : ℝ)"
    code.append(f"  have {name}_{k} : {L(ls[k])} ≤ Real.exp {zk} :=\n"
                f"    ExpBounds.le_exp_base _ _ {_abs1(zk, zs[k])} (by {_absrw_goal(zk, zs[k])}; norm_num)\n")
    for j in range(k - 1, -1, -1):
        ls[j] = round_dn(ls[j + 1] ** 2, DIG)
        zj = L(zs[j]) if j > 0 else f"({xexpr})"
        code.append(f"  have {name}_{j} : {L(ls[j])} ≤ Real.exp {zj} :=\n"
                    f"    ExpBounds.le_exp_sq _ {L(zs[j + 1])} _ _ (by norm_num) {name}_{j + 1} (by norm_num) (by norm_num)\n")
    code.append(f"  have {name} := {name}_0\n")
    return "".join(code), ls[0]


def log_upper(y):
    """rational A with y <= exp(A) (A slightly above log y)."""
    y = Fr(y)
    if y == 1:
        return Fr(0)
    lg = math.log1p(float(y - 1)) if abs(float(y - 1)) < 0.5 else math.log(float(y))
    A = round_up(Fr(lg) * (1 + Fr(1, 10 ** 15)) if lg > 0 else Fr(lg) * (1 - Fr(1, 10 ** 15)), 20)
    step = abs(A) / 10 ** 15 + Fr(1, 10 ** 40)
    while tac_le_exp("t", L(A), A)[1] < y:
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
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else None
    worst, cells = P.plan_round1(E1)
    assert worst is not None, "planner failed"
    K = len(cells)
    use = cells[:kmax] if kmax else cells
    cA1, A1 = tac_exp_le("h", "1 / 1000", Fr(1, 1000))
    cB1, B1 = tac_le_exp("h", "-(1 / 1000)", Fr(-1, 1000))
    L1500 = log_upper(Fr(1500))
    out = ["import CellLemmas\n",
           "/-! Generated by `gen_r1_cells.py` — do not edit. Concrete round-1 cells. -/\n",
           "set_option maxHeartbeats 4000000\n",
           "namespace R1Cells\nopen Real\n"]
    out.append("theorem hA1 : Real.exp (1 / 1000) ≤ " + L(A1) + " := by\n" + cA1 + "  exact h\n")
    out.append("theorem hB1 : " + L(B1) + " ≤ Real.exp (-(1 / 1000)) := by\n" + cB1 + "  exact h\n")
    out.append("theorem hL1500 : Real.log 1500 ≤ " + L(L1500) + " := by\n"
               + tac_y_le_exp("h", "(1500 : ℝ)", Fr(1500), L1500)
               + "  exact ExpBounds.log_le _ _ (by norm_num) h\n")
    params = []
    for idx, (pa, pb, lam0, t0, al0) in enumerate(use):
        chosen = None
        for sig in (6, 8, 10, 14, None):
            if sig is None:
                lam, t, al = Fr(lam0), Fr(t0), Fr(al0)
            else:
                lam, t, al = short(lam0, sig), short(t0, sig), short(al0, sig)
            if not (0 < t < al):
                continue
            cEu, Eu = tac_exp_le("hEu", L(al), al)
            cEl, El = tac_le_exp("hEl", L(al), al)
            cQ, Q = tac_le_exp("hQ", f"{L(al)} * ({L(pa)} + {L(lam)})", al * (pa + lam))
            if not (1 + pa * (Eu - 1) <= Q):
                continue
            Lq = log_upper(1 + pa * (Eu - 1))
            if not (Lq + (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) <= al * (pb + lam)):
                continue
            chosen = (lam, t, al, cEu, Eu, cEl, El, cQ, Q, Lq)
            break
        assert chosen is not None, ("rate", idx)
        lam, t, al, cEu, Eu, cEl, El, cQ, Q, Lq = chosen
        params.append((pa, pb, lam, t, al))
        cx = (t - al) * Fr(1, 1000) / t
        cC1, C1 = tac_exp_le("hC1", f"({L(t)} - {L(al)}) * (1 / 1000 / {L(t)})", cx)
        assert C1 < 1
        y2 = A1 * (1 + (1 - B1) / (1 - C1))
        Lq2 = log_upper(y2)
        body = [cEu, cEl, cQ,
                tac_y_le_exp("hLq", f"1 + {L(pa)} * ({L(Eu)} - 1)", 1 + pa * (Eu - 1), Lq),
                cC1,
                tac_y_le_exp("hLq2", f"{L(A1)} * (1 + (1 - {L(B1)}) / (1 - {L(C1)}))", y2, Lq2)]
        if pb <= Fr(1, 2):
            q = pb
        elif pa >= Fr(1, 2):
            q = pa
        else:
            q = None
        if q is None:
            Hq = Fr(6932, 10000)
            cl2, l2 = tac_le_exp("hl2", L(Hq), Hq)
            assert l2 >= 2
            body.append(cl2)
            body.append(f"  have hH : ∀ p, {L(pa)} ≤ p → p ≤ {L(pb)} → binEntropy p ≤ {L(Hq)} := by\n"
                        f"    intro p h1 h2\n"
                        f"    have h := CellLemmas.binEntropy_cell_le {L(pa)} {L(pb)} p (by norm_num) (by norm_num) h1 h2\n"
                        f"    rw [if_neg (by norm_num), if_neg (by norm_num)] at h\n"
                        f"    have hlt : Real.log 2 ≤ {L(Hq)} := ExpBounds.log_le _ _ (by norm_num) (le_trans {NN} hl2)\n"
                        f"    linarith\n")
        else:
            A = log_upper(1 / q)
            B = log_upper(1 / (1 - q))
            Hq = q * A + (1 - q) * B
            body.append(tac_y_le_exp("hA", f"1 / {L(q)}", 1 / q, A))
            body.append(tac_y_le_exp("hB", f"1 / (1 - {L(q)})", 1 / (1 - q), B))
            br = "rw [if_pos (by norm_num)] at h" if q == pb else "rw [if_neg (by norm_num), if_pos (by norm_num)] at h"
            body.append(f"  have hH : ∀ p, {L(pa)} ≤ p → p ≤ {L(pb)} → binEntropy p ≤ {L(Hq)} := by\n"
                        f"    intro p h1 h2\n"
                        f"    have h := CellLemmas.binEntropy_cell_le {L(pa)} {L(pb)} p (by norm_num) (by norm_num) h1 h2\n"
                        f"    {br}\n"
                        f"    have hq := CellLemmas.binEntropy_le_of {L(q)} {L(A)} {L(B)} (by norm_num) (by norm_num) hA hB\n"
                        f"    have e : {L(q)} * {L(A)} + (1 - {L(q)}) * {L(B)} = {L(Hq)} := by norm_num\n"
                        f"    linarith\n")
        fin = lam * M + (Hq + Lq2 + L1500 / 16) / t
        assert fin <= E1 / 2 * M, ("budget", idx, float(fin), float(E1 / 2 * M))
        out.append(f"theorem cell{idx} : Round1Num.CellOK1 {L(E1)} {L(M)} {L(ETA)} {L(pa)} {L(pb)} {L(lam)} {L(t)} {L(al)} := by")
        out.append("".join(body).rstrip("\n"))
        out.append(f"  exact CellLemmas.cellOK1_of_bounds {L(E1)} {L(M)} {L(ETA)} {L(pa)} {L(pb)} {L(lam)} {L(t)} {L(al)} {L(Eu)} {L(El)} {L(Q)} {L(Lq)} {L(Hq)} {L(C1)} {L(Lq2)} {L(A1)} {L(B1)} {L(L1500)}")
        out.append("    " + " ".join([NN] * 8))
        out.append(f"    hEu hEl {NN} hQ {NN} hLq {NN} hH hA1 hB1 {NN} hC1 {NN} hLq2 hL1500 {NN}\n")
    # tables, cover, dispatch and the final theorem (only for the full cell list)
    if not kmax:
        Kc = len(params)
        def table(name, vals):
            lines = [f"noncomputable def {name} : ℕ → ℝ"]
            for i, v in enumerate(vals):
                lines.append(f"  | {i} => {L(v)}")
            lines.append(f"  | _ => {L(vals[-1])}")
            return "\n".join(lines) + "\n"
        edges = [c[0] for c in params] + [params[-1][1]]
        out.append(table("edge", edges))
        out.append(table("lamf", [c[2] for c in params]))
        out.append(table("tf", [c[3] for c in params]))
        out.append(table("alf", [c[4] for c in params]))
        out.append(f"theorem cells_ok : ∀ i : Fin {Kc}, Round1Num.CellOK1 {L(E1)} {L(M)} {L(ETA)} (edge i) (edge (i + 1)) (lamf i) (tf i) (alf i) := by")
        out.append("  intro ⟨i, hi⟩")
        out.append("  interval_cases i")
        for i in range(Kc):
            out.append(f"  · exact cell{i}")
        out.append("")
        out.append(f"theorem edges_mono : ∀ i, i < {Kc} → edge i ≤ edge (i + 1) := by")
        out.append("  intro i hi")
        out.append("  interval_cases i <;> norm_num [edge]\n")
        out.append(f"theorem cover : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ i : Fin {Kc}, edge i ≤ p ∧ p ≤ edge (i + 1) := by")
        out.append("  intro p h0 h1")
        out.append(f"  obtain ⟨i, hi, h⟩ := CellLemmas.cover_of_edges {Kc} (by norm_num) edge (by norm_num [edge]) (by norm_num [edge]) edges_mono p h0 h1")
        out.append("  exact ⟨⟨i, hi⟩, h⟩\n")
        out.append("open Classical in")
        out.append("/-- **Round 1 of the walk bound, numerically closed**: for every `n ≥ 16` and every row count")
        out.append(f"`m ≥ {M}`, at most 1/100 of the scrambles fail the pipeline Property B with `E1 = {float(E1):.5e}`. -/")
        out.append("theorem round1_numeric {m n : ℕ} (hn : 16 ≤ n) (hmM : (" + str(M) + " : ℝ) ≤ m) (hm : 0 < m) :")
        out.append(f"    ((Finset.univ.filter fun σ : Chvatal.Scramble m n => ¬ Chvatal.HasCombinatorialPropertyBOnPipeline σ {L(E1)}).card : ℝ) ≤")
        out.append(f"      {L(ETA)} * ((Fintype.card (Chvatal.Scramble m n) : ℕ) : ℝ) :=")
        out.append(f"  Round1Num.round1_bound {L(E1)} {L(M)} {L(ETA)} (by norm_num) (by norm_num) (by norm_num)")
        out.append("    (fun i => edge i) (fun i => edge (i + 1)) (fun i => lamf i) (fun i => tf i) (fun i => alf i)")
        out.append("    cover cells_ok hn hmM hm\n")
    out.append("end R1Cells\n")
    path = os.path.join(HERE, "lean", "R1Cells.lean")
    open(path, "w", encoding="utf-8", newline="\n").write("\n".join(out))
    print(f"wrote {path}: {len(use)} of {K} cells, E1 = {float(E1):.5e}")


if __name__ == "__main__":
    main()
