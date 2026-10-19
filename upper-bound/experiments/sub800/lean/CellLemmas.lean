import Round1Num
import ExpBounds

/-! # Per-cell reduction to rational witness inequalities (LEAN-PLAN W4.5)

`cellOK1_of_bounds` turns the round-1 cell conditions into inequalities between explicit rationals
and values of `exp` that `ExpBounds` brackets. `binEntropy_cell_le` bounds the entropy on a cell
by its value at one endpoint (or by `log 2`). `cover_of_edges` gives the covering of `[0,1]`. -/

open Real Round2Col

namespace CellLemmas

/-- Entropy on a cell, by monotonicity on `[0, 1/2]` and `[1/2, 1]`. -/
theorem binEntropy_cell_le (pa pb p : ℝ) (h0 : 0 ≤ pa) (h1 : pb ≤ 1) (hpa : pa ≤ p) (hpb : p ≤ pb) :
    binEntropy p ≤ (if pb ≤ 1 / 2 then binEntropy pb else if 1 / 2 ≤ pa then binEntropy pa
      else Real.log 2) := by
  split_ifs with hl hr
  · exact binEntropy_strictMonoOn.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hpb
  · exact binEntropy_strictAntiOn.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hpa
  · exact binEntropy_le_log_two

/-- Entropy at a rational point from upper bounds on `log(1/q)` and `log(1/(1-q))`. -/
theorem binEntropy_le_of (q A B : ℝ) (h0 : 0 < q) (h1 : q < 1)
    (hA : 1 / q ≤ Real.exp A) (hB : 1 / (1 - q) ≤ Real.exp B) :
    binEntropy q ≤ q * A + (1 - q) * B := by
  unfold binEntropy
  have hA' : Real.log q⁻¹ ≤ A := by
    rw [← one_div]; exact ExpBounds.log_le _ _ (by positivity) hA
  have hB' : Real.log (1 - q)⁻¹ ≤ B := by
    rw [← one_div]; exact ExpBounds.log_le _ _ (div_pos one_pos (by linarith)) hB
  have : 0 < 1 - q := by linarith
  nlinarith

/-- Covering of `[0,1]` by consecutive edges. -/
theorem cover_of_edges (K : ℕ) (hK : 0 < K) (e : ℕ → ℝ) (h0 : e 0 = 0) (hKe : e K = 1)
    (hmono : ∀ i, i < K → e i ≤ e (i + 1)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ i, i < K ∧ e i ≤ p ∧ p ≤ e (i + 1) := by
  have key : ∀ k, k ≤ K → (∃ i, i < k ∧ e i ≤ p ∧ p ≤ e (i + 1)) ∨ e k ≤ p := by
    intro k
    induction k with
    | zero => intro _; right; rw [h0]; exact hp0
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨i, hi, h⟩ | h
      · left; exact ⟨i, by omega, h⟩
      · by_cases hle : p ≤ e (k + 1)
        · left; exact ⟨k, by omega, h, hle⟩
        · right; linarith
  rcases key K le_rfl with ⟨i, hi, h⟩ | h
  · exact ⟨i, hi, h⟩
  · refine ⟨K - 1, by omega, ?_, ?_⟩
    · have hm := hmono (K - 1) (by omega)
      rw [show K - 1 + 1 = K by omega] at hm
      have : p = 1 := le_antisymm hp1 (hKe ▸ h)
      linarith [hKe ▸ hm]
    · rw [show K - 1 + 1 = K by omega, hKe]; exact hp1

set_option maxHeartbeats 2000000 in
/-- **Round-1 cell from rational witnesses.** `A1 ≥ e^{1/1000}`, `B1 ≤ e^{-1/1000}`,
`L1500 ≥ log 1500` are global constants. -/
theorem cellOK1_of_bounds (E1 M η pa pb lam tt al : ℝ)
    (Eu El Q Lq Hq C1 Lq2 A1 B1 L1500 : ℝ)
    (hpa : 0 ≤ pa) (hpab : pa ≤ pb) (hpb1 : pb ≤ 1) (hlam : 0 ≤ lam) (ht : 0 < tt) (htal : tt < al)
    (hlamE : lam ≤ E1 / 2) (hη : 15 / η = 1500)
    (hEu : Real.exp al ≤ Eu) (hEl : El ≤ Real.exp al) (hEl1 : 1 ≤ El)
    (hQ : Q ≤ Real.exp (al * (pa + lam))) (hQ' : 1 + pa * (Eu - 1) ≤ Q)
    (hLq : 1 + pa * (Eu - 1) ≤ Real.exp Lq)
    (hrb : Lq + (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) ≤ al * (pb + lam))
    (hH : ∀ p, pa ≤ p → p ≤ pb → binEntropy p ≤ Hq)
    (hA1 : Real.exp (1 / 1000) ≤ A1) (hB1 : B1 ≤ Real.exp (-(1 / 1000))) (hB11 : B1 ≤ 1)
    (hC1 : Real.exp ((tt - al) * (1 / 1000 / tt)) ≤ C1) (hC1' : C1 < 1)
    (hLq2 : A1 * (1 + (1 - B1) / (1 - C1)) ≤ Real.exp Lq2)
    (hL1500 : Real.log 1500 ≤ L1500)
    (hfin : lam * M + (Hq + Lq2 + L1500 / 16) / tt ≤ E1 / 2 * M) :
    Round1Num.CellOK1 E1 M η pa pb lam tt al where
  pa_nonneg := hpa
  lam_nonneg := hlam
  t_pos := ht
  t_lt := htal
  lam_le := hlamE
  rate_a := by
    have hy : 0 < 1 + pa * (Real.exp al - 1) := by
      have : 1 ≤ Real.exp al := Real.one_le_exp (by linarith)
      nlinarith
    apply ExpBounds.log_le _ _ hy
    have : 1 + pa * (Real.exp al - 1) ≤ 1 + pa * (Eu - 1) := by nlinarith
    linarith
  rate_b := by
    have hE1 : 1 ≤ Real.exp al := Real.one_le_exp (by linarith)
    have hy : 0 < 1 + pa * (Real.exp al - 1) := by nlinarith
    have hlog : Real.log (1 + pa * (Real.exp al - 1)) ≤ Lq := by
      apply ExpBounds.log_le _ _ hy
      have : 1 + pa * (Real.exp al - 1) ≤ 1 + pa * (Eu - 1) := by nlinarith
      linarith
    have hden : 1 + pa * (El - 1) ≤ 1 + pa * (Real.exp al - 1) := by nlinarith
    have hden0 : 0 < 1 + pa * (El - 1) := by nlinarith
    have hfrac : (pb - pa) * (Real.exp al - 1) / (1 + pa * (Real.exp al - 1)) ≤
        (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) := by
      apply div_le_div₀ (by nlinarith) (by nlinarith) hden0 hden
    linarith
  budget := by
    intro p hp1 hp2
    have hHp := hH p hp1 hp2
    -- the layer-cake constant
    have htd : tt * (1 / 1000 / tt) = 1 / 1000 := by field_simp
    have hlb : Lb tt al (1 / 1000 / tt) ≤ A1 * (1 + (1 - B1) / (1 - C1)) := by
      unfold Lb
      rw [htd, show -(1 / 1000 : ℝ) = -(1 / 1000) from rfl]
      have hE : 0 ≤ 1 - Real.exp (-(1 / 1000 : ℝ)) := by
        have : Real.exp (-(1 / 1000 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
        linarith
      have hC0 : 0 < 1 - Real.exp ((tt - al) * (1 / 1000 / tt)) := by
        have hneg : (tt - al) * (1 / 1000 / tt) < 0 := by
          apply mul_neg_of_neg_of_pos (by linarith); positivity
        have : Real.exp ((tt - al) * (1 / 1000 / tt)) < 1 := by
          calc Real.exp ((tt - al) * (1 / 1000 / tt)) < Real.exp 0 := Real.exp_lt_exp.2 hneg
            _ = 1 := Real.exp_zero
        linarith
      have h1 : (1 - Real.exp (-(1 / 1000 : ℝ))) / (1 - Real.exp ((tt - al) * (1 / 1000 / tt))) ≤
          (1 - B1) / (1 - C1) := by
        apply div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
      have hpos : 0 ≤ 1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
          (1 - Real.exp ((tt - al) * (1 / 1000 / tt))) := by positivity
      calc Real.exp (1 / 1000) * (1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
            (1 - Real.exp ((tt - al) * (1 / 1000 / tt))))
          ≤ A1 * (1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
            (1 - Real.exp ((tt - al) * (1 / 1000 / tt)))) :=
            mul_le_mul_of_nonneg_right hA1 hpos
        _ ≤ A1 * (1 + (1 - B1) / (1 - C1)) := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have : 0 < Real.exp (1 / 1000 : ℝ) := Real.exp_pos _
            linarith
    have hLbpos : 0 < Lb tt al (1 / 1000 / tt) :=
      Round1Num.Lb_pos _ _ _ ht (by positivity) htal
    have hlogLb : Real.log (Lb tt al (1 / 1000 / tt)) ≤ Lq2 :=
      ExpBounds.log_le _ _ hLbpos (hlb.trans hLq2)
    rw [hη]
    have : (binEntropy p + Real.log (Lb tt al (1 / 1000 / tt)) + Real.log 1500 / 16) / tt ≤
        (Hq + Lq2 + L1500 / 16) / tt := by
      apply div_le_div_of_nonneg_right _ ht.le
      linarith
    linarith

end CellLemmas
