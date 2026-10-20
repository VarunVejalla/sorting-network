import AKS.Sub800.F2DR1
import AKS.Chvatal.F2SR

/-! # Small-rank failure bound for `F2PD`

Port of the package's `F2SR_fail_card_le`. The constants `1641`, `3300`, `1/7`, `70000` become the
parameters `K0` (tops), `Xn` (`e J / T ≤ Xn`), `qd` (`e δ f / T ≤ 1 / qd`) and `N` (the number of
tail factors kept), tied together by one natural-number inequality. -/

namespace Chvatal

/-- Numerical core (general constants). -/
theorem SRd_numeric (n K T j0 K0 J Xn qd N : ℕ) (hK : K ≤ K0) (hT : N + K0 + 1 ≤ T)
    (b X : ℝ) (hb0 : 0 ≤ b) (hqd : 1 ≤ qd) (hb : b ≤ 1 / qd) (hbX : b ≤ X / n) (hn : 0 < n)
    (hX0 : 0 ≤ X) (hX : X ≤ Xn) (hXn : 1 ≤ Xn) (hj0 : j0 ≤ J) (hJ : 1 ≤ J)
    (hnat : 10000 * ((K0 + 1) * J ^ K0 * Xn ^ (K0 + 1)) ≤ qd ^ N) :
    ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T) ≤ 1 / 10000 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0r : (j0 : ℝ) ≤ J := by exact_mod_cast hj0
  have hqd0 : (0 : ℝ) < qd := by exact_mod_cast hqd
  have hT' : b ^ T = b ^ (K + 1) * b ^ (T - (K + 1)) := by
    rw [← pow_add]; congr 1; omega
  have step1 : ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T) ≤
      (J : ℝ) ^ K * X ^ (K + 1) * b ^ (T - (K + 1)) := by
    rw [hT']
    have hbn : b ^ (K + 1) ≤ (X / n) ^ (K + 1) := pow_le_pow_left₀ hb0 hbX _
    have hb2 : 0 ≤ b ^ (T - (K + 1)) := pow_nonneg hb0 _
    have e1 : ((n : ℝ) * j0) ^ K ≤ ((n : ℝ) * J) ^ K :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    calc ((n : ℝ) * j0) ^ K * ((n : ℝ) * (b ^ (K + 1) * b ^ (T - (K + 1))))
        ≤ ((n : ℝ) * J) ^ K * ((n : ℝ) * ((X / n) ^ (K + 1) * b ^ (T - (K + 1)))) := by
          gcongr
      _ = _ := by
          rw [mul_pow, div_pow]
          field_simp
          ring
  have h2 : b ^ (T - (K + 1)) ≤ (1 / qd : ℝ) ^ N :=
    (pow_le_pow_left₀ hb0 hb _).trans
      (pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hqd0]; exact_mod_cast hqd)
        (by omega))
  have h3 : X ^ (K + 1) ≤ (Xn : ℝ) ^ (K0 + 1) :=
    (pow_le_pow_left₀ hX0 hX _).trans
      (pow_le_pow_right₀ (by exact_mod_cast hXn) (by omega))
  have h4 : (J : ℝ) ^ K ≤ (J : ℝ) ^ K0 := pow_le_pow_right₀ (by exact_mod_cast hJ) hK
  have h5 : ((K + 1 : ℕ) : ℝ) ≤ ((K0 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K + 1 ≤ K0 + 1)
  have hnatR : (10000 : ℝ) * (((K0 + 1 : ℕ) : ℝ) * (J : ℝ) ^ K0 * (Xn : ℝ) ^ (K0 + 1)) ≤
      (qd : ℝ) ^ N := by exact_mod_cast hnat
  have h7 : (0 : ℝ) < (qd : ℝ) ^ N := by positivity
  calc ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T)
      = ((K + 1 : ℕ) : ℝ) * (((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T)) := by ring
    _ ≤ ((K0 + 1 : ℕ) : ℝ) * ((J : ℝ) ^ K0 * (Xn : ℝ) ^ (K0 + 1) * (1 / qd : ℝ) ^ N) := by
        refine mul_le_mul h5 (step1.trans ?_) (by positivity) (by positivity)
        gcongr
    _ ≤ 1 / 10000 := by
        rw [one_div, inv_pow]
        have : ((K0 + 1 : ℕ) : ℝ) * ((J : ℝ) ^ K0 * (Xn : ℝ) ^ (K0 + 1) * (((qd : ℝ) ^ N))⁻¹) =
            (((K0 + 1 : ℕ) : ℝ) * (J : ℝ) ^ K0 * (Xn : ℝ) ^ (K0 + 1)) / (qd : ℝ) ^ N := by
          field_simp
        rw [this, div_le_iff₀ h7]
        generalize (qd : ℝ) ^ N = Z at hnatR ⊢
        linarith

open scoped Classical in
/-- **Small-rank failure bound** for `F2PD`, uniform in `n ≥ 16`. -/
theorem SRd_fail_card_le (P : F2PD) (H : F2Pre P) (K0 Xn qd N : ℕ)
    (hK0 : P.J / (P.g1 + 1) ≤ K0) (hT : N + K0 + 1 ≤ P.f - P.g1 + 1)
    (hD2 : P.δ * P.f ≤ ((P.f - P.g1 : ℕ) : ℝ) + 1)
    (hXe : Real.exp 1 * P.J ≤ Xn * (((P.f - P.g1 : ℕ) : ℝ) + 1)) (hXn : 1 ≤ Xn)
    (hqe : qd * (Real.exp 1 * (P.δ * P.f)) ≤ ((P.f - P.g1 : ℕ) : ℝ) + 1) (hqd : 1 ≤ qd)
    (hnat : 10000 * ((K0 + 1) * P.J ^ K0 * Xn ^ (K0 + 1)) ≤ qd ^ N)
    {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hn0' : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0'
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ := P.hδ
  set j0 : ℕ := min P.J (P.jmax n) with hj0def
  set T : ℕ := P.f - P.g1 + 1 with hTdef
  have hjmaxR : (P.jmax n : ℝ) ≤ P.δ * (P.f * n) := by
    unfold F2PD.jmax
    exact Nat.floor_le (by positivity)
  have hj0R : (j0 : ℝ) ≤ P.δ * (P.f * n) :=
    (by exact_mod_cast min_le_right _ _ : (j0 : ℝ) ≤ P.jmax n).trans hjmaxR
  have hj0pos : 0 < j0 := by
    refine lt_min P.hJ ?_
    unfold F2PD.jmax
    refine Nat.floor_pos.mpr ?_
    have h0 : 0 ≤ P.δ * P.f := mul_nonneg hδ.le (Nat.cast_nonneg _)
    have := H.hf16
    have : P.δ * P.f * 16 ≤ P.δ * P.f * n := mul_le_mul_of_nonneg_left hn16 h0
    nlinarith
  have hj0J : j0 ≤ P.J := min_le_left _ _
  have hTR : (T : ℝ) = ((P.f - P.g1 : ℕ) : ℝ) + 1 := by rw [hTdef]; push_cast; ring
  have hTpos : (0 : ℝ) < T := by rw [hTR]; positivity
  have hTj : (j0 : ℝ) / n ≤ (T : ℝ) := by
    rw [div_le_iff₀ hn0, hTR]
    have h2 := mul_le_mul_of_nonneg_right hD2 hn0.le
    calc (j0 : ℝ) ≤ P.δ * (P.f * n) := hj0R
      _ = P.δ * P.f * n := by ring
      _ ≤ _ := h2
  have hbad : ∀ σ ∈ (Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ),
      ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j0 ∧
        ∃ S : Finset (Fin n), S.card = 1 ∧ T ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    have h := (Finset.mem_filter.mp hσ).2
    unfold SRd at h
    push_neg at h
    obtain ⟨c, hc, S, hS, hle⟩ := h
    exact ⟨c, hc, S, hS, hle⟩
  have hmain := F2SR_union_bound P.g1 j0 T hn0' hj0pos hTj _ hbad
  have htops := tops_card_le_crude P.g1 n j0 hn0' hj0pos
  have hKle : j0 / (P.g1 + 1) ≤ K0 := (Nat.div_le_div_right hj0J).trans hK0
  set K := j0 / (P.g1 + 1) with hKdef
  set b : ℝ := Real.exp 1 * j0 / (n * (T : ℝ)) with hbdef
  set X : ℝ := Real.exp 1 * P.J / T with hXdef
  have he0 := Real.exp_pos 1
  have hb0 : 0 ≤ b := by positivity
  have hbX : b ≤ X / n := by
    rw [hbdef, hXdef, div_div, mul_comm (T : ℝ) (n : ℝ)]
    gcongr
  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ Xn := by
    rw [hXdef, div_le_iff₀ hTpos, hTR]; exact hXe
  have hqd0 : (0 : ℝ) < qd := by exact_mod_cast hqd
  have hb7 : b ≤ 1 / qd := by
    rw [hbdef, div_le_div_iff₀ (by positivity) hqd0, one_mul]
    have h1 : Real.exp 1 * j0 ≤ Real.exp 1 * (P.δ * (P.f * n)) :=
      mul_le_mul_of_nonneg_left hj0R he0.le
    have h2 := mul_le_mul_of_nonneg_right hqe hn0.le
    rw [← hTR] at h2
    nlinarith
  have hnum := SRd_numeric n K T j0 K0 P.J Xn qd N hKle hT b X hb0 hqd hb7 hbX hn0' hX0 hX hXn
    hj0J P.hJ hnat
  have hcard : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  rw [Real.rpow_natCast] at hmain
  refine hmain.trans ?_
  have htopsR : ((tops P.g1 n j0).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K := by
    exact_mod_cast htops
  calc ((tops P.g1 n j0).card : ℝ) * ((n : ℝ) * b ^ T) * (Fintype.card (Scramble m n) : ℝ)
      ≤ (((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K) * ((n : ℝ) * b ^ T) *
          (Fintype.card (Scramble m n) : ℝ) := by
        gcongr
    _ ≤ (1 / 10000) * (Fintype.card (Scramble m n) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hnum hcard

end Chvatal
