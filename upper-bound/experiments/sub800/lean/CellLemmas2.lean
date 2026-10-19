import Round2Num
import CellLemmas

/-! # Round-2 cells from rational witnesses -/

open Real Round2Col

namespace CellLemmas2

/-- The two tangent checks from witnesses (shared by both rounds). -/
theorem rates_of_bounds (pa pb lam al Eu El Q Lq : ℝ) (hpa : 0 ≤ pa) (hal : 0 ≤ al)
    (hEu : Real.exp al ≤ Eu) (hEl : El ≤ Real.exp al) (hEl1 : 1 ≤ El)
    (hQ : Q ≤ Real.exp (al * (pa + lam))) (hQ' : 1 + pa * (Eu - 1) ≤ Q)
    (hLq : 1 + pa * (Eu - 1) ≤ Real.exp Lq)
    (hrb : Lq + (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) ≤ al * (pb + lam)) (hpab : pa ≤ pb) :
    Real.log (1 + pa * (Real.exp al - 1)) ≤ al * (pa + lam) ∧
    Real.log (1 + pa * (Real.exp al - 1)) +
      (pb - pa) * (Real.exp al - 1) / (1 + pa * (Real.exp al - 1)) ≤ al * (pb + lam) := by
  have hE1 : 1 ≤ Real.exp al := Real.one_le_exp hal
  have hy : 0 < 1 + pa * (Real.exp al - 1) := by nlinarith
  have hup : 1 + pa * (Real.exp al - 1) ≤ 1 + pa * (Eu - 1) := by nlinarith
  refine ⟨ExpBounds.log_le _ _ hy (by linarith), ?_⟩
  have hlog : Real.log (1 + pa * (Real.exp al - 1)) ≤ Lq := ExpBounds.log_le _ _ hy (by linarith)
  have hden : 1 + pa * (El - 1) ≤ 1 + pa * (Real.exp al - 1) := by nlinarith
  have hden0 : 0 < 1 + pa * (El - 1) := by nlinarith
  have hfrac : (pb - pa) * (Real.exp al - 1) / (1 + pa * (Real.exp al - 1)) ≤
      (pb - pa) * (Eu - 1) / (1 + pa * (El - 1)) :=
    div_le_div₀ (by nlinarith) (by nlinarith) hden0 hden
  linarith

/-- The layer-cake constant from witnesses. -/
theorem Lb_le_of (tt al A1 B1 C1 : ℝ) (ht : 0 < tt) (htal : tt < al)
    (hA1 : Real.exp (1 / 1000) ≤ A1) (hB1 : B1 ≤ Real.exp (-(1 / 1000)))
    (hC1 : Real.exp ((tt - al) * (1 / 1000 / tt)) ≤ C1) (hC1' : C1 < 1) :
    Lb tt al (1 / 1000 / tt) ≤ A1 * (1 + (1 - B1) / (1 - C1)) := by
  unfold Lb
  have htd : tt * (1 / 1000 / tt) = 1 / 1000 := by field_simp
  rw [htd]
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
      (1 - B1) / (1 - C1) :=
    div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hpos : 0 ≤ 1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
      (1 - Real.exp ((tt - al) * (1 / 1000 / tt))) := by positivity
  calc Real.exp (1 / 1000) * (1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
        (1 - Real.exp ((tt - al) * (1 / 1000 / tt))))
      ≤ A1 * (1 + (1 - Real.exp (-(1 / 1000 : ℝ))) /
        (1 - Real.exp ((tt - al) * (1 / 1000 / tt)))) := mul_le_mul_of_nonneg_right hA1 hpos
    _ ≤ A1 * (1 + (1 - B1) / (1 - C1)) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        have : 0 < Real.exp (1 / 1000 : ℝ) := Real.exp_pos _
        linarith

set_option maxHeartbeats 2000000 in
/-- **Round-2 cell from rational witnesses.** -/
theorem cellOK2_of_bounds (E1 d g' M η lnG pa pb lam tt al be : ℝ)
    (Eua Ela Qa Lqa Eub Elb Qb Lqb Hq C1a C1b Lq2 A1 B1 L15000 : ℝ)
    (hpa : 0 ≤ pa) (hpab : pa ≤ pb) (hpb : pb ≤ 1 / 2) (hlam : 0 ≤ lam) (ht : 0 < tt)
    (htal : tt < al) (htbe : tt < be) (hlamE : lam * E1 ≤ d / 2) (hη : 15 / η = 15000)
    (hEua : Real.exp al ≤ Eua) (hEla : Ela ≤ Real.exp al) (hEla1 : 1 ≤ Ela)
    (hQa : Qa ≤ Real.exp (al * (pa + lam))) (hQa' : 1 + pa * (Eua - 1) ≤ Qa)
    (hLqa : 1 + pa * (Eua - 1) ≤ Real.exp Lqa)
    (hrba : Lqa + (pb - pa) * (Eua - 1) / (1 + pa * (Ela - 1)) ≤ al * (pb + lam))
    (hEub : Real.exp be ≤ Eub) (hElb : Elb ≤ Real.exp be) (hElb1 : 1 ≤ Elb)
    (hQb : Qb ≤ Real.exp (be * ((1 - pb) + lam))) (hQb' : 1 + (1 - pb) * (Eub - 1) ≤ Qb)
    (hLqb : 1 + (1 - pb) * (Eub - 1) ≤ Real.exp Lqb)
    (hrbb : Lqb + ((1 - pa) - (1 - pb)) * (Eub - 1) / (1 + (1 - pb) * (Elb - 1)) ≤
      be * ((1 - pa) + lam))
    (hH : ∀ p, pa ≤ p → p ≤ pb → binEntropy p ≤ Hq)
    (hA1 : Real.exp (1 / 1000) ≤ A1) (hB1 : B1 ≤ Real.exp (-(1 / 1000)))
    (hC1a : Real.exp ((tt - al) * (1 / 1000 / tt)) ≤ C1a) (hC1a' : C1a < 1)
    (hC1b : Real.exp ((tt - be) * (1 / 1000 / tt)) ≤ C1b) (hC1b' : C1b < 1)
    (hLq2 : A1 * (1 + (1 - B1) / (1 - C1a)) + A1 * (1 + (1 - B1) / (1 - C1b)) - 1 ≤ Real.exp Lq2)
    (hL15000 : Real.log 15000 ≤ L15000)
    (hfin : lam * (E1 * M + g') + (Hq + Lq2 + (lnG + L15000) / 16) / tt ≤ d / 2 * M) :
    Round2Num.CellOK2 E1 d g' M η lnG pa pb lam tt al be := by
  have hal : 0 ≤ al := by linarith
  have hbe : 0 ≤ be := by linarith
  have hab := rates_of_bounds pa pb lam al Eua Ela Qa Lqa hpa hal hEua hEla hEla1 hQa hQa' hLqa hrba hpab
  have hcd := rates_of_bounds (1 - pb) (1 - pa) lam be Eub Elb Qb Lqb (by linarith) hbe hEub hElb
    hElb1 hQb hQb' hLqb hrbb (by linarith)
  refine ⟨hpa, hpb, hlam, ht, htal, htbe, hlamE, hab.1, hab.2, hcd.1, hcd.2, ?_⟩
  intro p hp1 hp2
  have hHp := hH p hp1 hp2
  have hla := Lb_le_of tt al A1 B1 C1a ht htal hA1 hB1 hC1a hC1a'
  have hlb := Lb_le_of tt be A1 B1 C1b ht htbe hA1 hB1 hC1b hC1b'
  have hMpos : 0 < Lb tt al (1 / 1000 / tt) + Lb tt be (1 / 1000 / tt) - 1 := by
    have h1 := Round2Num.Lb_ge_one tt al (1 / 1000 / tt) ht.le (by positivity) htal
    have h2 := Round2Num.Lb_ge_one tt be (1 / 1000 / tt) ht.le (by positivity) htbe
    linarith
  have hlog : Real.log (Lb tt al (1 / 1000 / tt) + Lb tt be (1 / 1000 / tt) - 1) ≤ Lq2 :=
    ExpBounds.log_le _ _ hMpos (by linarith)
  rw [hη]
  have : (binEntropy p + Real.log (Lb tt al (1 / 1000 / tt) + Lb tt be (1 / 1000 / tt) - 1) +
      (lnG + Real.log 15000) / 16) / tt ≤ (Hq + Lq2 + (lnG + L15000) / 16) / tt := by
    apply div_le_div_of_nonneg_right _ ht.le
    linarith
  linarith

/-- Covering of `[0, top]` by consecutive edges. -/
theorem cover_of_edges_top (K : ℕ) (hK : 0 < K) (e : ℕ → ℝ) (top : ℝ) (h0 : e 0 = 0)
    (hKe : e K = top) (hmono : ∀ i, i < K → e i ≤ e (i + 1)) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ top) : ∃ i, i < K ∧ e i ≤ p ∧ p ≤ e (i + 1) := by
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
      linarith
    · rw [show K - 1 + 1 = K by omega, hKe]; exact hp1

end CellLemmas2
