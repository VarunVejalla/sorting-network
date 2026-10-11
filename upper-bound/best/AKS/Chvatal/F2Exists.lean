module

public import AKS.Chvatal.F2Det
public import AKS.Chvatal.F2ParamsOf
public import AKS.Chvatal.F2SR
public import AKS.Chvatal.F2R1Fail
public import AKS.Chvatal.F2R2Fail
public import AKS.Chvatal.Bulk2Exists

/-! # Existence of a two-round scrambling pair with B2 and F2 for `131040 ≤ f < 8.5·10⁹` -/

@[expose] public section

namespace Chvatal

open Classical in
theorem card_fail_and_le {α : Type*} [Fintype α] (A B : α → Prop) {a b : ℝ}
    (hA : ((Finset.univ.filter fun x => ¬ A x).card : ℝ) ≤ a * Fintype.card α)
    (hB : ((Finset.univ.filter fun x => ¬ B x).card : ℝ) ≤ b * Fintype.card α) :
    ((Finset.univ.filter fun x => ¬ (A x ∧ B x)).card : ℝ) ≤ (a + b) * Fintype.card α := by
  have h : (Finset.univ.filter fun x => ¬ (A x ∧ B x)) ⊆
      (Finset.univ.filter fun x => ¬ A x) ∪ (Finset.univ.filter fun x => ¬ B x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    tauto
  have h3 := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card h).trans (Finset.card_union_le _ _))
  push_cast at h3
  linarith

open Classical in
theorem exists_twoRound_mid {m n f : ℕ} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n)
    (hf1 : 131040 ≤ f) (hf2 : f < 8500000000) (hfm : f ≤ m) :
    ∃ σ1 σ2 : Scramble m n,
      (HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn) σ1 σ2 (1 / 59000000) ∧
        HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn)
          (flipScramble σ1) (flipScramble σ2) (1 / 59000000)) ∧
      (HasPackSemanticPropertyF2 (lt_of_lt_of_le (by norm_num) hn) σ1 σ2 f hfm (128 / 4095) eps ∧
        HasPackSemanticPropertyF2 (lt_of_lt_of_le (by norm_num) hn)
          (flipScramble σ1) (flipScramble σ2) f hfm (128 / 4095) eps) := by
  set P := F2Params.ofF f hf1 hf2 with hP
  have hPf : P.f = f := rfl
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hm100 : 100 ≤ m := le_trans (by norm_num) hm
  -- round 1
  have hB1 := lemma61FailBound_onPipeline (m := m) (n := n) (371 / 10 ^ 8) (by omega) (by omega)
    (epsB1_le hm)
  have hfac := lemma61_failFactor_lt_one_hundredth m n hm100 hn
  have hB1' : ((Finset.univ.filter fun σ : Scramble m n =>
      ¬ HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8)).card : ℝ) ≤
      1 / 100 * (Fintype.card (Scramble m n) : ℝ) :=
    hB1.trans (by gcongr)
  have hSR := F2SR_fail_card_le P (by simpa using hf1) rfl rfl (m := m) (n := n) hn (by simpa using hfm)
  have hR1 := F2R1_fail P (by simpa using hf1) rfl rfl rfl rfl rfl (m := m) (n := n) hn
    (by simpa using hfm)
  have hPF1 := card_fail_and_le (fun σ : Scramble m n => F2SmallRank P σ)
    (fun σ : Scramble m n => F2R1 P σ) hSR hR1
  have hfail1 := card_fail_and_le
    (fun σ : Scramble m n => HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8))
    (fun σ : Scramble m n => F2SmallRank P σ ∧ F2R1 P σ) hB1' (by simpa using hPF1)
  obtain ⟨σ1, h1, h1'⟩ := exists_and_flip (m := m) (n := n)
    (fun σ => HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8) ∧
      (F2SmallRank P σ ∧ F2R1 P σ))
    (c := 1 / 100 + (1 / 10000 + 1 / 10000)) (by norm_num)
    (by convert hfail1 using 2 <;> first | (congr 1; ext σ; simp; done) | norm_num)
  have hR2 := F2R2n_fail P (by simpa using hf1) (by simpa using hf2) rfl rfl rfl rfl hn
    (by simpa using hfm) (m := m) (n := n)
  have hfail2 := card_fail_and_le
    (fun σ : Scramble m n => HasCombinatorialPropertyB2 σ (371 / 10 ^ 8) (1 / 59000000))
    (fun σ : Scramble m n => F2R2n P σ) (bulk2_fail_fraction_le hm hn) hR2
  obtain ⟨σ2, h2, h2'⟩ := exists_and_flip (m := m) (n := n)
    (fun σ => HasCombinatorialPropertyB2 σ (371 / 10 ^ 8) (1 / 59000000) ∧ F2R2n P σ)
    (c := 1 / 1000 + 1 / 10000) (by norm_num)
    (by convert hfail2 using 2 <;> first | (congr 1; ext σ; simp; done) | norm_num)
  have hF := F2_both_orientations P hn0 hfm
    ⟨h1.2.1, h1.2.2, h2.2⟩ ⟨h1'.2.1, h1'.2.2, h2'.2⟩
  have e : (1 / ((P.J : ℕ) : ℝ)) = eps := by
    have : P.J = 86000000 := rfl
    rw [this]; unfold eps; norm_num
  rw [e] at hF
  exact ⟨σ1, σ2, ⟨HasPackSemanticPropertyB2.of_combinatorial _ h1.1 h2.1,
    HasPackSemanticPropertyB2.of_combinatorial _ h1'.1 h2'.1⟩, hF⟩

end Chvatal
