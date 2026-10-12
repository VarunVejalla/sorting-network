import CandidateBulkWitness
import CandidateBulkExistence
import AKS.Chvatal.Bulk2Bridge
import AKS.Chvatal.FlipSpec

namespace Tapered945
open Chvatal

def ExactBulk {m n : Nat} (σ : Scramble m n)
    (Adm : MonotoneColumnSums m n → Nat → Prop) (d : Real) : Prop :=
  ∀ c i, totalColumnOnes c = n*i → i ≤ m → Adm c i →
    (onesAboveBottom c σ i : Real) < (d/2)*(m*n)

open Classical in
/-- Uniform exact-mass two-tailed union. Admissibility must be invariant under
state complementation, and each half-column cell needs a real tail bound. -/
theorem exact_bulk_fail_union {m n : Nat} (hn : 0 < n)
    (Adm : MonotoneColumnSums m n → Nat → Prop) (d B : Real)
    (hB0 : 0 ≤ B)
    (hcomp : ∀ c i, totalColumnOnes c = n*i → i ≤ m → Adm c i →
      Adm (complementColumns c) (m-i))
    (hcell : ∀ c i, totalColumnOnes c = n*i → i ≤ m → Adm c i →
      ∀ S : Finset (Fin n), (S.card : Real) ≤ (n : Real)/2 →
      ((Finset.univ.filter (fun σ : Scramble m n =>
        (i : Real)*S.card+(d/2)*(m*n) ≤ (onesInColumns c σ S : Real))).card : Real) ≤
          B*(Fintype.card (Scramble m n) : Real)) :
    ((Finset.univ.filter (fun σ : Scramble m n => ¬ ExactBulk σ Adm d)).card : Real) ≤
      2*(2*((m : Real)+1))^n*B*(Fintype.card (Scramble m n) : Real) := by
  classical
  let i₀ : MonotoneColumnSums m n → Nat := fun c => totalColumnOnes c/n
  let D : MonotoneColumnSums m n → Prop := fun c =>
    totalColumnOnes c = n*i₀ c ∧ i₀ c ≤ m ∧ Adm c (i₀ c)
  let V : MonotoneColumnSums m n × Finset (Fin n) → Finset (Scramble m n) := fun p =>
    Finset.univ.filter (fun σ => D p.1 ∧ (p.2.card : Real) ≤ (n : Real)/2 ∧
      (i₀ p.1 : Real)*p.2.card+(d/2)*(m*n) ≤ (onesInColumns p.1 σ p.2 : Real))
  let U := Finset.univ.biUnion V
  let bad := Finset.univ.filter (fun σ : Scramble m n => ¬ ExactBulk σ Adm d)
  have hcover : bad ⊆ U ∪ Finset.univ.filter (fun σ => reverseRows σ ∈ U) := by
    intro σ hσ
    have hf := (Finset.mem_filter.mp hσ).2
    simp only [ExactBulk, not_forall, not_lt] at hf
    obtain ⟨c, i, hm, hi, ha, hge⟩ := hf
    obtain ⟨R, hR, ht⟩ := excess_small_column_witness c σ i hi hm d hge
    have hi₀ : i₀ c = i := by dsimp [i₀]; rw [hm]; exact Nat.mul_div_cancel_left i hn
    rcases ht with ht | ht
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      refine ⟨(c,R), Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      change D c ∧ _
      rw [show D c ↔ totalColumnOnes c = n*i ∧ i ≤ m ∧ Adm c i by simp only [D, hi₀]]
      rw [hi₀]
      exact ⟨⟨hm, hi, ha⟩, hR, ht⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
      have hmc := complement_exact_mass c i hi hm
      have hic : i₀ (complementColumns c) = m-i := by
        dsimp [i₀]; rw [hmc]; exact Nat.mul_div_cancel_left (m-i) hn
      refine ⟨(complementColumns c,R), Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      change D (complementColumns c) ∧ _
      dsimp only [D]
      rw [hic]
      exact ⟨⟨hmc, Nat.sub_le _ _, hcomp c i hm hi ha⟩, hR, ht⟩
  have hV : ∀ p, ((V p).card : Real) ≤ B*(Fintype.card (Scramble m n) : Real) := by
    intro p
    by_cases hD : D p.1
    · by_cases hS : (p.2.card : Real) ≤ (n : Real)/2
      · have hsub : V p ⊆ Finset.univ.filter (fun σ : Scramble m n =>
            (i₀ p.1 : Real)*p.2.card+(d/2)*(m*n) ≤ (onesInColumns p.1 σ p.2 : Real)) := by
          intro σ hσ
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hσ).2.2.2⟩
        have hh := (Nat.cast_le (α := Real)).mpr (Finset.card_le_card hsub)
        exact hh.trans (hcell p.1 (i₀ p.1) hD.1 hD.2.1 hD.2.2 p.2 hS)
      · have he : V p = ∅ := Finset.filter_false_of_mem (fun _ _ h => hS h.2.1)
        rw [he, Finset.card_empty, Nat.cast_zero]; positivity
    · have he : V p = ∅ := Finset.filter_false_of_mem (fun _ _ h => hD h.1)
      rw [he, Finset.card_empty, Nat.cast_zero]; positivity
  have hU : (U.card : Real) ≤ (2*((m : Real)+1))^n*B*(Fintype.card (Scramble m n) : Real) := by
    calc
      _ ≤ ∑ p, ((V p).card : Real) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _ : MonotoneColumnSums m n × Finset (Fin n),
          B*(Fintype.card (Scramble m n) : Real) := Finset.sum_le_sum (fun p _ => hV p)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset]
        simp only [nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
        push_cast
        rw [mul_pow]
        ring
  have hrev : (Finset.univ.filter (fun σ => reverseRows σ ∈ U)).card = U.card := by
    simpa using (card_filter_reverseRows (fun σ : Scramble m n => σ ∈ U))
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [hrev] at hc
  have hcR : (bad.card : Real) ≤ (U.card : Real)+(U.card : Real) := by exact_mod_cast hc
  change (bad.card : Real) ≤ _
  nlinarith

open Classical in
/-- Hoeffding cell bound at exact mass with a genuinely half-sized witness. -/
theorem hoeffding_half_columns {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) (i : Nat) (hmass : totalColumnOnes c = n*i)
    (S : Finset (Fin n)) (hS : (S.card : Real) ≤ (n : Real)/2)
    (E : Real) (hE : 0 < E) :
    ((Finset.univ.filter (fun σ : Scramble m n =>
      (i : Real)*S.card+(E/2)*(m*n) ≤ (onesInColumns c σ S : Real))).card : Real) ≤
      Real.exp (-((n : Real)*m*E^2))*(Fintype.card (Scramble m n) : Real) := by
  classical
  let bad := Finset.univ.filter (fun σ : Scramble m n =>
    (i : Real)*S.card+(E/2)*(m*n) ≤ (onesInColumns c σ S : Real))
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  by_cases hs : S.card = 0
  · have hsempty := Finset.card_eq_zero.mp hs
    have he : bad = ∅ := by
      apply Finset.filter_false_of_mem
      intro σ _ h
      simp only [hsempty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_add,
        onesInColumns, onesInRows, Finset.inter_empty, Finset.sum_const_zero] at h
      have hp : (0 : Real) < (E/2)*(m*n) := by positivity
      linarith
    change (bad.card : Real) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hsR : (0 : Real) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    let t : Real := (E/2)*(n : Real)/S.card
    have ht : 0 < t := by dsimp [t]; positivity
    have hsum : (∑ r : Fin m, ((monotoneRowOnes c r).card : Real)) = (n : Real)*i := by
      exact_mod_cast (totalColumnOnes_eq_sum_rowOnes c).symm.trans hmass
    have he : ((∑ r : Fin m, ((monotoneRowOnes c r).card : Real))/(m*n)+t)*m*S.card =
        (i : Real)*S.card+(E/2)*(m*n) := by
      rw [hsum]
      dsimp [t]
      field_simp
    have hb := lemma63ExpBound hm hn c S t ht bad (fun σ hσ => by
      rw [he]; exact (Finset.mem_filter.mp hσ).2)
    have hrate : (n : Real)*m*E^2 ≤ 2*t^2*m*S.card := by
      have hs2 : 2*(S.card : Real) ≤ n := by linarith
      have hx := mul_le_mul_of_nonneg_left hs2
        (show (0 : Real) ≤ E^2*m*n by positivity)
      have heq : 2*t^2*m*S.card = E^2*m*(n : Real)^2/(2*S.card) := by
        dsimp [t]
        field_simp
      rw [heq, le_div_iff₀ (by positivity)]
      nlinarith [hx]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _))

open Classical in
theorem exact_round1_fail_fraction {m n : Nat} (hm : 0 < m) (hn : 16 ≤ n)
    (E : Real) (hE : 0 < E)
    (hgap : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*E^2) :
    ((Finset.univ.filter (fun σ : Scramble m n => ¬ ExactBulk σ (fun _ _ => True) E)).card : Real) ≤
      (1/1000)*(Fintype.card (Scramble m n) : Real) := by
  have h := exact_bulk_fail_union (m := m) (n := n) (by omega)
    (fun _ _ => True) E (Real.exp (-((n : Real)*m*E^2))) (Real.exp_nonneg _)
    (fun _ _ _ _ _ => trivial)
    (fun c i hc _ _ S hS => hoeffding_half_columns hm (by omega) c i hc S hS E hE)
  have hf := two_tail_union_factor_le hm hn (E^2) hgap
  calc
    _ ≤ 2*(2*((m : Real)+1))^n*Real.exp (-((n : Real)*m*E^2))*
      (Fintype.card (Scramble m n) : Real) := h
    _ = (2*((2*((m : Real)+1))^n*Real.exp (-((n : Real)*m*E^2))))*
      (Fintype.card (Scramble m n) : Real) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _)

def IntermediateAdm {m n : Nat} (E : Real) (c : MonotoneColumnSums m n) (i : Nat) : Prop :=
  (excessAbove c i : Real) ≤ (E/2)*(m*n)

open Classical in
theorem exact_round2_fail_fraction {m n : Nat} (hm : 0 < m) (hn : 16 ≤ n)
    (E d lam : Real) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hgap : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*
      (lam*d/2-lam^2*(1/2+2*lam/9)*E/2)) :
    ((Finset.univ.filter (fun σ : Scramble m n => ¬ ExactBulk σ (IntermediateAdm E) d)).card : Real) ≤
      (1/1000)*(Fintype.card (Scramble m n) : Real) := by
  let K : Real := lam*d/2-lam^2*(1/2+2*lam/9)*E/2
  have hc : ∀ (c : MonotoneColumnSums m n) (i : Nat), totalColumnOnes c = n*i → i ≤ m → IntermediateAdm E c i →
      IntermediateAdm E (complementColumns c) (m-i) := by
    intro c i hmass hi he
    unfold IntermediateAdm at he ⊢
    rw [complement_excess_exact c i hi hmass]
    exact he
  have h := exact_bulk_fail_union (m := m) (n := n) (by omega)
    (IntermediateAdm E) d (Real.exp (-((n : Real)*m*K))) (Real.exp_nonneg _) hc
    (fun c i hmass _ he S hS => bernstein_half_columns (by omega) c i hmass S hS
      lam d E hl0 hl1 he _ (fun σ hσ => (Finset.mem_filter.mp hσ).2))
  have hf := two_tail_union_factor_le hm hn K hgap
  calc
    _ ≤ 2*(2*((m : Real)+1))^n*Real.exp (-((n : Real)*m*K))*
      (Fintype.card (Scramble m n) : Real) := h
    _ = (2*((2*((m : Real)+1))^n*Real.exp (-((n : Real)*m*K))))*
      (Fintype.card (Scramble m n) : Real) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _)

/-- Exact-mass first-round guarantees suffice for actual threshold inputs. -/
theorem semantic_B2_of_exact {m n : Nat} (hn : 0 < n)
    {σ₁ σ₂ : Scramble m n} {E d : Real}
    (h1 : ExactBulk σ₁ (fun _ _ => True) E)
    (h2 : ExactBulk σ₂ (IntermediateAdm E) d) :
    HasPackSemanticPropertyB2 hn σ₁ σ₂ d := by
  intro v i hi1 him
  let x : Fin (m*n) → Bool := fun w => largestKeyThresholdJ01 (m := m) (n := n) (i*n) (v w)
  have hmass : totalColumnOnes (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec x)) = i*n :=
    sum_topJ_colSums_eq_j hn v (i*n) (Nat.mul_le_mul_right n him)
  obtain ⟨ht, he⟩ := semanticExec_intermediate hn σ₁ x i
  have hB1 := h1 _ i (by rw [hmass]; ring) him trivial
  rw [matrixOnesCountInRegion_semanticExec2_eq]
  refine h2 _ i (by rw [ht, hmass]; ring) him ?_
  unfold IntermediateAdm
  rw [he]
  exact hB1.le

open Classical in
theorem candidate_bulk_pair_exists {m n : Nat} (hm : 2^34 ≤ m) (hn : 16 ≤ n) :
    ∃ σ₁ σ₂ : Scramble m n,
      HasPackSemanticPropertyB2 (by omega : 0<n) σ₁ σ₂ (1/2^21) ∧
      HasPackSemanticPropertyB2 (by omega : 0<n) (flipScramble σ₁) (flipScramble σ₂) (1/2^21) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  obtain ⟨σ₁, h1, h1f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (fun _ _ => True) (38/10^6))
    (c := 1/1000) (by norm_num)
    (exact_round1_fail_fraction hm0 hn _ (by norm_num) (candidate_round_one_gap m hm))
  obtain ⟨σ₂, h2, h2f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (IntermediateAdm (38/10^6)) (1/2^21))
    (c := 1/1000) (by norm_num)
    (exact_round2_fail_fraction hm0 hn _ _ (1/80) (by norm_num) (by norm_num) (candidate_round_two_gap m hm))
  exact ⟨σ₁, σ₂, semantic_B2_of_exact (by omega) h1 h2, semantic_B2_of_exact (by omega) h1f h2f⟩

open Classical in
/-- Parameterized simultaneous two-sided bulk and first-round auxiliary
property existence. Actual F providers can use the remaining failure share. -/
theorem bulk_pair_with_aux_of_gaps {m n : Nat} (hm : 0 < m) (hn : 16 ≤ n)
    (E d lam F : Real) (hE : 0 < E) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hgap1 : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*E^2)
    (hgap2 : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*
      (lam*d/2-lam^2*(1/2+2*lam/9)*E/2))
    (PF : Scramble m n → Prop) (hF : 1/1000+F < 1/2)
    (hPF : ((Finset.univ.filter (fun σ : Scramble m n => ¬ PF σ)).card : Real) ≤
      F*(Fintype.card (Scramble m n) : Real)) :
    ∃ σ₁ σ₂ : Scramble m n,
      (PF σ₁ ∧ HasPackSemanticPropertyB2 (by omega : 0<n) σ₁ σ₂ d) ∧
      (PF (flipScramble σ₁) ∧ HasPackSemanticPropertyB2 (by omega : 0<n)
        (flipScramble σ₁) (flipScramble σ₂) d) := by
  have hfail1 := exact_round1_fail_fraction hm hn E hE hgap1
  have hboth : ((Finset.univ.filter (fun σ : Scramble m n =>
      ¬ (ExactBulk σ (fun _ _ => True) E ∧ PF σ))).card : Real) ≤
      (1/1000+F)*(Fintype.card (Scramble m n) : Real) := by
    simp only [not_and_or, Finset.filter_or]
    have hc := (Nat.cast_le (α := Real)).mpr (Finset.card_union_le
      (Finset.univ.filter (fun σ : Scramble m n => ¬ ExactBulk σ (fun _ _ => True) E))
      (Finset.univ.filter (fun σ : Scramble m n => ¬ PF σ)))
    push_cast at hc
    linarith
  obtain ⟨σ₁, h1, h1f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (fun _ _ => True) E ∧ PF σ)
    (c := 1/1000+F) hF (by convert hboth using 2; congr 1; ext σ; simp)
  obtain ⟨σ₂, h2, h2f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (IntermediateAdm E) d)
    (c := 1/1000) (by norm_num) (exact_round2_fail_fraction hm hn E d lam hl0 hl1 hgap2)
  exact ⟨σ₁, σ₂, ⟨h1.2, semantic_B2_of_exact (by omega) h1.1 h2⟩,
    ⟨h1f.2, semantic_B2_of_exact (by omega) h1f.1 h2f⟩⟩

end Tapered945
