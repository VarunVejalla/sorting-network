import AKS.Sub800.F2DR2c

/-! # R2 for `F2PD`: blocks, tail, and the failure bound

`a n E = #badE_E / #Scramble` if `(E-1) J ≤ jmax n`, else `0`.

* `block_le`: on a block `Ea ≤ E ≤ Eb` with constants `(κ1, H, θmin)`, `a n E ≤ Mb`.
* `tail_sum_le`: `∑_{ET ≤ E < K} a n E ≤ Mt` for a tail with `θmin = 0`.
* `R2nd_fail`: `#{¬ R2nd} ≤ (Wfin + Mt) #Scramble` given `∑_{2 ≤ E < ET} a n E ≤ Wfin`. -/

namespace Chvatal

open Finset

open Classical in
/-- The per-`E` failure fraction (zero outside the admissible ranks). -/
noncomputable def aR2 (P : F2PD) (m n E : ℕ) : ℝ :=
  if (E - 1) * P.J ≤ P.jmax n then
    ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) / Fintype.card (Scramble m n)
  else 0

theorem aR2_nonneg (P : F2PD) (m n E : ℕ) : 0 ≤ aR2 P m n E := by
  unfold aR2; split_ifs <;> positivity

/-- The common constants of an R2 certificate. -/
structure R2Common (P : F2PD) (LY L0 : ℝ) : Prop where
  hc2 : P.c ≤ 1 / 2
  hb1 : 1 ≤ P.b
  hY : (P.c + 1 / 2) ^ 2 ≤ (P.b - 1 / 2) * P.J / (2 * (P.δ * P.f))
  hΦ : 1 ≤ P.Φ
  hLY : Real.log (Real.exp 2 * P.b * P.J / (P.δ * P.f * P.c ^ 2)) ≤ LY
  hL0 : Real.log (Real.exp 1 * P.J * P.Φ / (P.δ * P.f)) ≤ L0

/-- The `θ`-function of a block. -/
noncomputable def hR2 (P : F2PD) (L0 κ1 θ : ℝ) : ℝ :=
  θ / P.Φ * (L0 - Real.log θ) + (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1)))

/-- The per-`E` bound of `R2E_le`. -/
noncomputable def FR2 (P : F2PD) (LY H : ℝ) (E : ℕ) : ℝ :=
  (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) *
    (Real.exp 2 * (E * P.J / (P.δ * P.f)) * Real.exp (E * H) +
      2 * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / (P.δ * P.f)))))

theorem aR2_le_FR2 (P : F2PD) {LY L0 : ℝ} (C : R2Common P LY L0) {m n : ℕ} (hn : 0 < n) (E : ℕ)
    (hE : 2 ≤ E) (Ea : ℕ) (hEa : Ea ≤ E) (hEa2 : 2 ≤ Ea) (κ1 H θmin : ℝ)
    (hk1 : P.b * (P.δ * P.f) * Ea ≤ κ1 * ((Ea : ℝ) - 1) * P.J)
    (heκ : Real.exp 1 * κ1 ≤ P.Φ) (hθmin : θmin * E ≤ P.Φ)
    (hθ : ∀ θ : ℝ, 0 < θ → θmin ≤ θ → hR2 P L0 κ1 θ ≤ H) :
    aR2 P m n E ≤ FR2 P LY H E := by
  have hδ := P.hδ
  have hf0 : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; omega
    exact_mod_cast this
  have hFnn : 0 ≤ FR2 P LY H E := by unfold FR2; have := P.hc0; positivity
  unfold aR2
  split_ifs with hEn
  · have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ htot]
    have hEr : (Ea : ℝ) ≤ E := by exact_mod_cast hEa
    have hEa1 : (1 : ℝ) < Ea := by
      have : (2 : ℝ) ≤ Ea := by exact_mod_cast hEa2
      linarith
    have hk1' : P.b * (P.δ * P.f) * E ≤ κ1 * ((E : ℝ) - 1) * P.J := by
      -- E/(E-1) ≤ Ea/(Ea-1)
      have hJ : (0 : ℝ) ≤ P.J := Nat.cast_nonneg _
      have hbD : 0 ≤ P.b * (P.δ * P.f) := by have := P.hb0; positivity
      have hκ1 : 0 ≤ κ1 * P.J := by
        have h1 : 0 ≤ P.b * (P.δ * P.f) * Ea := by positivity
        have h2 : 0 < (Ea : ℝ) - 1 := by linarith
        have := h1.trans hk1
        rw [mul_comm κ1, mul_assoc] at this
        nlinarith
      have hEa' : (E : ℝ) * ((Ea : ℝ) - 1) ≤ Ea * ((E : ℝ) - 1) := by nlinarith
      have h2 : 0 < (Ea : ℝ) - 1 := by linarith
      have key : P.b * (P.δ * P.f) * E * ((Ea : ℝ) - 1) ≤ κ1 * ((E : ℝ) - 1) * P.J * ((Ea : ℝ) - 1) := by
        calc P.b * (P.δ * P.f) * E * ((Ea : ℝ) - 1) = P.b * (P.δ * P.f) * (E * ((Ea : ℝ) - 1)) := by ring
          _ ≤ P.b * (P.δ * P.f) * (Ea * ((E : ℝ) - 1)) := mul_le_mul_of_nonneg_left hEa' hbD
          _ = (P.b * (P.δ * P.f) * Ea) * ((E : ℝ) - 1) := by ring
          _ ≤ (κ1 * ((Ea : ℝ) - 1) * P.J) * ((E : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hk1 (by
                have : (2 : ℝ) ≤ E := by exact_mod_cast hE
                linarith)
          _ = _ := by ring
      exact le_of_mul_le_mul_right key h2
    have h := R2E_le P (m := m) hn E hE hEn κ1 LY L0 H θmin C.hc2 C.hb1 C.hY hk1' C.hΦ heκ C.hLY
      C.hL0 hθmin (fun θ h0 h1 => hθ θ h0 h1)
    unfold FR2
    exact h
  · exact hFnn

/-- **Block bound.** -/
theorem block_le (P : F2PD) {LY L0 : ℝ} (C : R2Common P LY L0) {m n : ℕ} (hn : 0 < n)
    (Ea Eb : ℕ) (hEa2 : 2 ≤ Ea) (κ1 H θmin Mb : ℝ)
    (hk1 : P.b * (P.δ * P.f) * Ea ≤ κ1 * ((Ea : ℝ) - 1) * P.J)
    (heκ : Real.exp 1 * κ1 ≤ P.Φ) (hθmin : θmin * Eb ≤ P.Φ) (hθmin0 : 0 ≤ θmin)
    (hθ : ∀ θ : ℝ, 0 < θ → θmin ≤ θ → hR2 P L0 κ1 θ ≤ H)
    (hs1 : P.c * LY + H ≤ 0) (hs2 : P.c * LY ≤ Real.exp 2 * P.J / (P.δ * P.f))
    (hM : (P.c * Eb + 2) * (Real.exp 2 * (Eb * P.J / (P.δ * P.f)) *
        Real.exp (LY + Ea * (P.c * LY + H)) +
      2 * Real.exp (LY + Real.exp 2 * P.J / (P.δ * P.f) +
        Ea * (P.c * LY - Real.exp 2 * P.J / (P.δ * P.f)))) ≤ Mb) :
    ∀ E ∈ Ico Ea (Eb + 1), aR2 P m n E ≤ Mb := by
  intro E hE
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hE
  have hEb : E ≤ Eb := by omega
  have hEr : (Ea : ℝ) ≤ E := by exact_mod_cast h1
  have hEbr : (E : ℝ) ≤ Eb := by exact_mod_cast hEb
  have hθE : θmin * E ≤ P.Φ := le_trans (mul_le_mul_of_nonneg_left hEbr hθmin0) hθmin
  refine (aR2_le_FR2 P C hn E (by omega) Ea h1 hEa2 κ1 H θmin hk1 heκ hθE hθ).trans ?_
  refine le_trans ?_ hM
  unfold FR2
  have hδ := P.hδ
  have hc0 := P.hc0
  have hf0 : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; omega
    exact_mod_cast this
  set D := P.δ * P.f
  have hD : 0 < D := by positivity
  have e1 : Real.exp ((P.c * E + 1) * LY) * Real.exp (E * H) =
      Real.exp (LY + E * (P.c * LY + H)) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((P.c * E + 1) * LY) * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / D))) =
      Real.exp (LY + Real.exp 2 * P.J / D + E * (P.c * LY - Real.exp 2 * P.J / D)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have m1 : Real.exp (LY + E * (P.c * LY + H)) ≤ Real.exp (LY + Ea * (P.c * LY + H)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have m2 : Real.exp (LY + Real.exp 2 * P.J / D + E * (P.c * LY - Real.exp 2 * P.J / D)) ≤
      Real.exp (LY + Real.exp 2 * P.J / D + Ea * (P.c * LY - Real.exp 2 * P.J / D)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hJ : (0 : ℝ) ≤ P.J := Nat.cast_nonneg _
  have m3 : Real.exp 2 * (E * P.J / D) ≤ Real.exp 2 * (Eb * P.J / D) := by gcongr
  calc (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) *
        (Real.exp 2 * (E * P.J / D) * Real.exp (E * H) +
          2 * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / D))))
      = (P.c * E + 2) * (Real.exp 2 * (E * P.J / D) * Real.exp (LY + E * (P.c * LY + H)) +
          2 * Real.exp (LY + Real.exp 2 * P.J / D + E * (P.c * LY - Real.exp 2 * P.J / D))) := by
        rw [← e1, ← e2]; ring
    _ ≤ _ := by
        gcongr

/-- `x ≤ e^{x-1}`, scaled: `E ≤ (1/(e a)) e^{a E}` for `a > 0`. -/
theorem le_exp_scaled (a x : ℝ) (ha : 0 < a) : x ≤ 1 / (Real.exp 1 * a) * Real.exp (a * x) := by
  have h := Real.add_one_le_exp (a * x - 1)
  rw [Real.exp_sub] at h
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have he := Real.exp_pos 1
  have : a * x ≤ Real.exp (a * x) / Real.exp 1 := by linarith
  rw [le_div_iff₀ he] at this
  linarith

theorem geom_exp_le (a : ℝ) (ha : 0 < a) (ET K : ℕ) :
    ∑ E ∈ Ico ET K, Real.exp (-(a * E)) ≤ Real.exp (-(a * ET)) / (1 - Real.exp (-a)) := by
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ E : ℕ, Real.exp (-(a * E)) = Real.exp (-a) ^ E := fun E => by
    rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [hpow]
  exact geom_sum_Ico_le_of_lt_one hr0 hr1

/-- **Tail bound** (`θmin = 0`). With `A = e² J / D`, `λ = -(c LY + H)`, `μ = A - c LY`:
`a n E ≤ (c+2) (A E² e^{LY-λE} + 2 E e^{LY+A-μE})`, then `E² ≤ (4/(eλ))² e^{λE/2}`,
`E ≤ (2/(eμ)) e^{μE/2}` and geometric sums from `ET`. -/
theorem tail_sum_le_d (P : F2PD) {LY L0 : ℝ} (C : R2Common P LY L0) {m n : ℕ} (hn : 0 < n)
    (ET : ℕ) (hET : 2 ≤ ET) (κ1 H lam mu Mt : ℝ)
    (hk1 : P.b * (P.δ * P.f) * ET ≤ κ1 * ((ET : ℝ) - 1) * P.J)
    (heκ : Real.exp 1 * κ1 ≤ P.Φ)
    (hθ : ∀ θ : ℝ, 0 < θ → hR2 P L0 κ1 θ ≤ H)
    (hlam : lam = -(P.c * LY + H)) (hlam0 : 0 < lam)
    (A0 : ℝ) (hA0le : A0 ≤ Real.exp 2 * P.J / (P.δ * P.f))
    (hmu : mu = A0 - P.c * LY) (hmu0 : 0 < mu)
    (hMt : (P.c + 2) * (Real.exp 2 * P.J / (P.δ * P.f) * (4 / (Real.exp 1 * lam)) ^ 2 *
        (Real.exp (LY - lam / 2 * ET) / (1 - Real.exp (-(lam / 2)))) +
      2 * (2 / (Real.exp 1 * mu)) *
        (Real.exp (LY + A0 - mu / 2 * ET) /
          (1 - Real.exp (-(mu / 2))))) ≤ Mt)
    (K : ℕ) : ∑ E ∈ Ico ET K, aR2 P m n E ≤ Mt := by
  have hδ := P.hδ
  have hc0 := P.hc0
  have hf0 : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; omega
    exact_mod_cast this
  set D := P.δ * P.f with hD
  have hD0 : 0 < D := by positivity
  have hJ : (0 : ℝ) ≤ P.J := Nat.cast_nonneg _
  set A := Real.exp 2 * P.J / D with hA
  have hA0 : 0 ≤ A := by positivity
  set q1 := 4 / (Real.exp 1 * lam) with hq1def
  set q2 := 2 / (Real.exp 1 * mu) with hq2def
  have hq1 : 0 ≤ q1 := by positivity
  have hq2 : 0 ≤ q2 := by positivity
  have hper : ∀ E ∈ Ico ET K, aR2 P m n E ≤
      (P.c + 2) * (A * q1 ^ 2 * Real.exp LY * Real.exp (-(lam / 2 * E)) +
        2 * q2 * Real.exp (LY + A0) * Real.exp (-(mu / 2 * E))) := by
    intro E hE
    have hE1 := (Finset.mem_Ico.mp hE).1
    have hEr : (2 : ℝ) ≤ E := by exact_mod_cast (le_trans hET hE1)
    have hE0 : (0 : ℝ) ≤ E := by linarith
    have hΦ0 : (0 : ℝ) ≤ P.Φ := Nat.cast_nonneg _
    refine (aR2_le_FR2 P C hn E (le_trans hET hE1) ET hE1 hET κ1 H 0 hk1 heκ
      (by rw [zero_mul]; exact hΦ0) (fun θ h0 _ => hθ θ h0)).trans ?_
    unfold FR2
    have e1 : Real.exp ((P.c * E + 1) * LY) * Real.exp (E * H) =
        Real.exp LY * Real.exp (-(lam * E)) := by
      rw [← Real.exp_add, ← Real.exp_add, hlam]; congr 1; ring
    have e2 : Real.exp ((P.c * E + 1) * LY) * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / D))) ≤
        Real.exp (LY + A0) * Real.exp (-(mu * E)) := by
      rw [← Real.exp_add, ← Real.exp_add, hmu, Real.exp_le_exp]
      have hAe : Real.exp 2 * (((E : ℝ) - 1) * P.J / D) = A * ((E : ℝ) - 1) := by rw [hA]; ring
      rw [hAe]
      have : A0 * ((E : ℝ) - 1) ≤ A * ((E : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (by rw [hA]; exact hA0le) (by linarith)
      linarith
    have hcE : P.c * E + 2 ≤ (P.c + 2) * E := by nlinarith
    have hs1 := le_exp_scaled (lam / 4) E (by linarith)
    have hs2 := le_exp_scaled (mu / 2) E (by linarith)
    have hsq : (E : ℝ) * E * Real.exp (-(lam * E)) ≤ q1 ^ 2 * Real.exp (-(lam / 2 * E)) := by
      have hq : 1 / (Real.exp 1 * (lam / 4)) = q1 := by rw [hq1def]; field_simp
      rw [hq] at hs1
      have h0 : 0 ≤ q1 * Real.exp (lam / 4 * E) := le_trans hE0 hs1
      have h2 : (E : ℝ) * E ≤ q1 ^ 2 * (Real.exp (lam / 4 * E) * Real.exp (lam / 4 * E)) := by
        have := mul_le_mul hs1 hs1 hE0 h0
        nlinarith
      have e3 : Real.exp (lam / 4 * E) * Real.exp (lam / 4 * E) * Real.exp (-(lam * E)) =
          Real.exp (-(lam / 2 * E)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc (E : ℝ) * E * Real.exp (-(lam * E))
          ≤ q1 ^ 2 * (Real.exp (lam / 4 * E) * Real.exp (lam / 4 * E)) * Real.exp (-(lam * E)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = q1 ^ 2 * Real.exp (-(lam / 2 * E)) := by rw [mul_assoc, e3]
    have hlin : (E : ℝ) * Real.exp (-(mu * E)) ≤ q2 * Real.exp (-(mu / 2 * E)) := by
      have hq : 1 / (Real.exp 1 * (mu / 2)) = q2 := by rw [hq2def]; field_simp
      rw [hq] at hs2
      have e3 : Real.exp (mu / 2 * E) * Real.exp (-(mu * E)) = Real.exp (-(mu / 2 * E)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (E : ℝ) * Real.exp (-(mu * E)) ≤ q2 * Real.exp (mu / 2 * E) * Real.exp (-(mu * E)) :=
            mul_le_mul_of_nonneg_right hs2 (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, e3]
    have hX : 0 ≤ A * E * (Real.exp LY * Real.exp (-(lam * E))) +
        2 * (Real.exp (LY + A0) * Real.exp (-(mu * E))) := by positivity
    calc (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) *
          (Real.exp 2 * (E * P.J / D) * Real.exp (E * H) +
            2 * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / D))))
        = (P.c * E + 2) * (Real.exp 2 * (E * P.J / D) *
            (Real.exp ((P.c * E + 1) * LY) * Real.exp (E * H)) +
            2 * (Real.exp ((P.c * E + 1) * LY) *
              Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / D))))) := by ring
      _ ≤ (P.c * E + 2) * (Real.exp 2 * (E * P.J / D) *
            (Real.exp ((P.c * E + 1) * LY) * Real.exp (E * H)) +
            2 * (Real.exp (LY + A0) * Real.exp (-(mu * E)))) := by gcongr
      _ = (P.c * E + 2) * (A * E * (Real.exp LY * Real.exp (-(lam * E))) +
            2 * (Real.exp (LY + A0) * Real.exp (-(mu * E)))) := by
          rw [e1, hA]; ring
      _ ≤ (P.c + 2) * E * (A * E * (Real.exp LY * Real.exp (-(lam * E))) +
            2 * (Real.exp (LY + A0) * Real.exp (-(mu * E)))) := mul_le_mul_of_nonneg_right hcE hX
      _ = (P.c + 2) * (A * Real.exp LY * (E * E * Real.exp (-(lam * E))) +
            2 * Real.exp (LY + A0) * (E * Real.exp (-(mu * E)))) := by ring
      _ ≤ (P.c + 2) * (A * Real.exp LY * (q1 ^ 2 * Real.exp (-(lam / 2 * E))) +
            2 * Real.exp (LY + A0) * (q2 * Real.exp (-(mu / 2 * E)))) := by
          gcongr
      _ = _ := by ring
  have hg1 := geom_exp_le (lam / 2) (by linarith) ET K
  have hg2 := geom_exp_le (mu / 2) (by linarith) ET K
  calc ∑ E ∈ Ico ET K, aR2 P m n E
      ≤ ∑ E ∈ Ico ET K, (P.c + 2) * (A * q1 ^ 2 * Real.exp LY * Real.exp (-(lam / 2 * E)) +
        2 * q2 * Real.exp (LY + A0) * Real.exp (-(mu / 2 * E))) := Finset.sum_le_sum hper
    _ = (P.c + 2) * (A * q1 ^ 2 * Real.exp LY * ∑ E ∈ Ico ET K, Real.exp (-(lam / 2 * E)) +
        2 * q2 * Real.exp (LY + A0) * ∑ E ∈ Ico ET K, Real.exp (-(mu / 2 * E))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (P.c + 2) * (A * q1 ^ 2 * Real.exp LY *
          (Real.exp (-(lam / 2 * ET)) / (1 - Real.exp (-(lam / 2)))) +
        2 * q2 * Real.exp (LY + A0) *
          (Real.exp (-(mu / 2 * ET)) / (1 - Real.exp (-(mu / 2))))) := by
        gcongr
    _ = (P.c + 2) * (A * q1 ^ 2 * (Real.exp (LY - lam / 2 * ET) / (1 - Real.exp (-(lam / 2)))) +
        2 * q2 * (Real.exp (LY + A0 - mu / 2 * ET) / (1 - Real.exp (-(mu / 2))))) := by
        have e5 : Real.exp (LY - lam / 2 * ET) = Real.exp LY * Real.exp (-(lam / 2 * ET)) := by
          rw [← Real.exp_add, sub_eq_add_neg]
        have e6 : Real.exp (LY + A0 - mu / 2 * ET) = Real.exp (LY + A0) * Real.exp (-(mu / 2 * ET)) := by
          rw [← Real.exp_add, sub_eq_add_neg]
        rw [e5, e6]; ring
    _ ≤ Mt := hMt

open Classical in
/-- `¬ R2nd` lands in the admissible ranks. -/
theorem not_R2nd_subset {m n : ℕ} (P : F2PD) :
    (Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ) ⊆
      (Finset.Icc 2 (1 + P.jmax n / P.J)).biUnion
        fun E => badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E) := by
  classical
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, R2nd] at hσ
  push_neg at hσ
  obtain ⟨E, hE, hEn, c, hc1, hc2, S, hne, hge⟩ := hσ
  refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Icc.mpr ⟨hE, ?_⟩, ?_⟩
  · have := (Nat.le_div_iff_mul_le P.hJ).mpr hEn
    omega
  · simp only [badE, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, hc1, hc2, S, hne, hge⟩

open Classical in
/-- **R2 failure bound.** -/
theorem R2nd_fail (P : F2PD) {m n : ℕ} (ET : ℕ) (hET : 2 ≤ ET) (Wfin Mt : ℝ)
    (hfin : ∑ E ∈ Ico 2 ET, aR2 P m n E ≤ Wfin)
    (htail : ∀ K, ∑ E ∈ Ico ET K, aR2 P m n E ≤ Mt) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ).card : ℝ) ≤
      (Wfin + Mt) * Fintype.card (Scramble m n) := by
  classical
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  set N := 1 + P.jmax n / P.J with hN
  set K := max (N + 1) ET with hK
  have h1 : ((Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ).card : ℝ) ≤
      ∑ E ∈ Finset.Icc 2 N, ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (not_R2nd_subset P)).trans Finset.card_biUnion_le
  have h2 : ∀ E ∈ Finset.Icc 2 N, ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) =
      aR2 P m n E * Fintype.card (Scramble m n) := by
    intro E hE
    have hEN := (Finset.mem_Icc.mp hE).2
    have hEn : (E - 1) * P.J ≤ P.jmax n := by
      have : E - 1 ≤ P.jmax n / P.J := Nat.sub_le_iff_le_add'.mpr hEN
      exact (Nat.le_div_iff_mul_le P.hJ).mp this
    unfold aR2
    rw [if_pos hEn, div_mul_cancel₀ _ htot.ne']
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ htot.le)
  have hsub : Finset.Icc 2 N ⊆ Ico 2 K := by
    intro E hE
    have := Finset.mem_Icc.mp hE
    exact Finset.mem_Ico.mpr ⟨this.1, lt_of_lt_of_le (Nat.lt_succ_of_le this.2) (le_max_left _ _)⟩
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun E _ _ => aR2_nonneg P m n E)
  have h4 : ∑ E ∈ Ico 2 K, aR2 P m n E =
      ∑ E ∈ Ico 2 ET, aR2 P m n E + ∑ E ∈ Ico ET K, aR2 P m n E :=
    (Finset.sum_Ico_consecutive _ hET (le_max_right _ _)).symm
  linarith [hfin, htail K]

end Chvatal
