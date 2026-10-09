module

public import AKS.Chvatal.Lemma63

@[expose] public section

namespace Chvatal

/-- Pipeline-class Lemma 6.1 union bound over `(c, S)`. -/
theorem lemma61FailBound_onPipeline_of_decodeClass {m n : Nat} (epsB : ℝ)
    (O : DecodeMatrixClassObligation m n epsB) :
    Lemma61FailBoundOnPipeline m n epsB := by
  classical
  obtain ⟨hm, hn, heps⟩ := O
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hε : 0 < epsB := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) heps
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let V : MonotoneColumnSums m n × Finset (Fin n) → Finset (Scramble m n) := fun p =>
    Finset.univ.filter fun σ => 0 < p.2.card ∧
      ((∑ r : Fin m, ((monotoneRowOnes p.1 r).card : ℝ)) / (m * n) + epsB / 2 * (n / p.2.card)) *
        m * p.2.card ≤ onesInColumns p.1 σ p.2
  refine ⟨fun bad hbad => ?_⟩
  have hcover : bad ⊆ Finset.univ.biUnion V := by
    intro σ hσ
    have hnot := hbad σ hσ
    simp only [HasCombinatorialPropertyBOnPipeline, not_forall, not_lt] at hnot
    obtain ⟨c, i, hc, -, -, hge⟩ := hnot
    have hex := lemma61_excess_columns epsB c σ i hge
    have hs : 0 < (excessColumnSet c σ i).card := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [Finset.card_eq_zero.1 h0] at hex
      simp [onesInColumns] at hex
      nlinarith [mul_pos hm0 hn0]
    refine Finset.mem_biUnion.2 ⟨(c, excessColumnSet c σ i), Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, ?_⟩⟩
    set s : ℝ := ((excessColumnSet c σ i).card : ℝ)
    have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 hs
    have htot : (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) ≤ n * i := by
      exact_mod_cast (totalColumnOnes_eq_sum_rowOnes c ▸ hc)
    have : ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n) + epsB / 2 * (n / s)) * m * s =
        (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) * s / n + epsB / 2 * (m * n) := by
      field_simp
    rw [this]
    have h2 : (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) * s / n ≤ i * s := by
      rw [div_le_iff₀ hn0]; nlinarith
    linarith
  have hV : ∀ p, (V p).card ≤ (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
    intro p
    by_cases hs : 0 < p.2.card
    · refine (lemma63ExpBound hm hn p.1 p.2 _ (by positivity) (V p) fun σ hσ => (Finset.mem_filter.1 hσ).2.2).trans ?_
      exact mul_le_mul_of_nonneg_right (lemma61_exp_bound m n _ epsB hm hs
        ((Finset.card_le_univ _).trans (by simp)) heps) hN
    · have : V p = ∅ := Finset.filter_false_of_mem fun σ _ h => hs h.1
      simp [this]; positivity
  calc (bad.card : ℝ) ≤ ((Finset.univ.biUnion V).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ p, ((V p).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p : MonotoneColumnSums m n × Finset (Fin n), (Real.exp 1 * m) ^ (-(n : ℝ)) * N :=
      Finset.sum_le_sum fun p _ => hV p
    _ = lemma61_failFactor m n * N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset]
      simp only [nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, lemma61_failFactor]
      push_cast
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, mul_pow]
      field_simp
      rw [mul_pow]; ring

end Chvatal
