import AKS.Sub800.PaddedSeparator
import AKS.Chvatal.PackSpec2
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Padding shifts a live largest-key cohort by precisely the number of
dummy keys. Smaller physical fringes do not require an extra row-error
charge: the live unprotected output region is contained in the padded one. -/
theorem restrictWires_fHigh_padded {A a : Nat} (ha : a ≤ A)
    (net : ComparatorNetwork A) (F J : Nat) (eps : Real)
    (provider : ∀ (x : Equiv.Perm (Fin A)) q, 0 < q → q ≤ J → q ≤ A →
      ((Finset.univ.filter fun c : Fin A =>
        A - q ≤ (net.exec x c).val ∧ c.val < A - F).card : Real) < eps * q)
    (p : Equiv.Perm (Fin a)) (u j : Nat) (hu : u ≤ a)
    (hF : F ≤ u + (A - a)) (hj : 0 < j) (hja : j ≤ a)
    (hJ : j + (A - a) ≤ J) :
    ((Finset.univ.filter fun c : Fin a =>
      a - j ≤ ((net.restrictWires a ha).exec p c).val ∧ c.val < a - u).card : Real) <
      eps * ((j + (A - a) : Nat) : Real) := by
  have hevent := padding_rank_event_card ha net p
    (fun wire rank => a - j ≤ rank ∧ wire < a - u)
    (by intro i hi; omega)
  have hthreshold : A - (j + (A - a)) = a - j := by omega
  have hcut : a - u ≤ A - F := by omega
  have hsub : (Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec (padRankPerm ha p) c).val ∧ c.val < a - u) ⊆
    (Finset.univ.filter fun c : Fin A =>
      A - (j + (A - a)) ≤ (net.exec (padRankPerm ha p) c).val ∧ c.val < A - F) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨by rw [hthreshold]; exact hc.1, hc.2.trans_le hcut⟩
  have hcount : ((Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec (padRankPerm ha p) c).val ∧ c.val < a - u).card : Real) ≤
    ((Finset.univ.filter fun c : Fin A =>
      A - (j + (A - a)) ≤ (net.exec (padRankPerm ha p) c).val ∧ c.val < A - F).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [hevent] at hcount
  exact hcount.trans_lt (provider (padRankPerm ha p) (j + (A - a)) (by omega) hJ (by omega))

/-- The live smallest-key cohort needs no padding enlargement at all. -/
theorem restrictWires_fLow_padded {A a : Nat} (ha : a ≤ A)
    (net : ComparatorNetwork A) (F J : Nat) (eps : Real)
    (provider : ∀ (x : Equiv.Perm (Fin A)) q, 0 < q → q ≤ J → q ≤ A →
      ((Finset.univ.filter fun c : Fin A =>
        (net.exec x c).val < q ∧ F ≤ c.val).card : Real) < eps * q)
    (p : Equiv.Perm (Fin a)) (u j : Nat) (hF : F ≤ u)
    (hj : 0 < j) (hja : j ≤ a) (hJ : j ≤ J) :
    ((Finset.univ.filter fun c : Fin a =>
      ((net.restrictWires a ha).exec p c).val < j ∧ u ≤ c.val).card : Real) < eps * j := by
  have hevent := padding_rank_event_card ha net p
    (fun wire rank => rank < j ∧ u ≤ wire)
    (by intro i hi; omega)
  have hsub : (Finset.univ.filter fun c : Fin A =>
      (net.exec (padRankPerm ha p) c).val < j ∧ u ≤ c.val) ⊆
    (Finset.univ.filter fun c : Fin A =>
      (net.exec (padRankPerm ha p) c).val < j ∧ F ≤ c.val) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1, hF.trans hc.2⟩
  have hcount : ((Finset.univ.filter fun c : Fin A =>
      (net.exec (padRankPerm ha p) c).val < j ∧ u ≤ c.val).card : Real) ≤
    ((Finset.univ.filter fun c : Fin A =>
      (net.exec (padRankPerm ha p) c).val < j ∧ F ≤ c.val).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [hevent] at hcount
  exact hcount.trans_lt (provider (padRankPerm ha p) j hj hJ (hja.trans ha))

/-- The physical two-round F witness supplies the high-tail provider above.
The cohort range explicitly includes all dummy ranks. -/
theorem paddedPack2Net_fHigh {m n a f : Nat} (hn : 0 < n)
    (ha : a ≤ m * n) (hfm : f ≤ m) (σ₁ σ₂ : Scramble m n)
    (delta eps : Real)
    (hF : HasPackSemanticPropertyF2 hn σ₁ σ₂ f hfm delta eps)
    (p : Equiv.Perm (Fin a)) (u j : Nat) (hu : u ≤ a)
    (hfringe : f * n ≤ u + (m * n - a)) (hj : 0 < j) (hja : j ≤ a)
    (hcohort : ((j + (m * n - a) : Nat) : Real) ≤ delta * (f * n)) :
    ((Finset.univ.filter fun c : Fin a =>
      a - j ≤ ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val ∧ c.val < a - u).card : Real) <
      eps * ((j + (m * n - a) : Nat) : Real) := by
  apply restrictWires_fHigh_padded ha (physicalPack2Net m n hn σ₁ σ₂)
    (f * n) (j + (m * n - a)) eps _ p u j hu hfringe hj hja le_rfl
  intro x q hq hqJ hqA
  have hqR : (q : Real) ≤ (j + (m * n - a) : Nat) := by exact_mod_cast hqJ
  have h := packSpec2_high_F hn σ₁ σ₂ hfm hF x q hq (hqR.trans hcohort)
  have heq : 2 * f * n / 2 = f * n := by rw [mul_assoc]; omega
  simpa only [heq] using h

/-- Add an entirely marked bottom row. It is preserved by every row
scramble and column sort, allowing the rare live mass to be counted alone. -/
def baselineLiftColumnSums {m n : Nat} (c : MonotoneColumnSums m n) :
    MonotoneColumnSums (m + 1) n :=
  fun col => ⟨(c col).val + 1, by have := (c col).isLt; omega⟩

def truncateBottomScramble {m n : Nat} (σ : Scramble (m + 1) n) : Scramble m n :=
  fun r => σ r.castSucc

theorem baselineLift_row {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m) :
    monotoneRowOnes (baselineLiftColumnSums c) r.castSucc = monotoneRowOnes c r := by
  ext col
  simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and,
    baselineLiftColumnSums, Fin.val_castSucc]
  have := r.isLt
  omega

theorem baselineLift_last_row {m n : Nat} (c : MonotoneColumnSums m n) :
    monotoneRowOnes (baselineLiftColumnSums c) (Fin.last m) = Finset.univ := by
  ext col
  simp [monotoneRowOnes, baselineLiftColumnSums]

theorem baselineLift_scrambled_row {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble (m + 1) n) (r : Fin m) :
    scrambledRowOnes (baselineLiftColumnSums c) σ r.castSucc =
      scrambledRowOnes c (truncateBottomScramble σ) r := by
  simp only [scrambledRowOnes, baselineLift_row, truncateBottomScramble]

theorem baselineLift_scrambled_last {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble (m + 1) n) :
    scrambledRowOnes (baselineLiftColumnSums c) σ (Fin.last m) = Finset.univ := by
  rw [scrambledRowOnes, baselineLift_last_row]
  exact Finset.image_univ_of_surjective (σ (Fin.last m)).surjective

/-- Exact one-round baseline removal. No error proportional to padding is
introduced: the residual heights evolve under the truncated scramble. -/
theorem baselineLift_scrambledColSum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble (m + 1) n) (col : Fin n) :
    scrambledColSum (baselineLiftColumnSums c) σ col =
      scrambledColSum c (truncateBottomScramble σ) col + 1 := by
  unfold scrambledColSum
  rw [Fin.sum_univ_castSucc]
  simp only [baselineLift_scrambled_row, baselineLift_scrambled_last,
    Finset.mem_univ, if_true]

theorem baselineLift_escapes {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble (m + 1) n) (f : Nat) :
    onesAboveBottom (baselineLiftColumnSums c) σ (f + 1) =
      onesAboveBottom c (truncateBottomScramble σ) f := by
  unfold onesAboveBottom
  simp only [baselineLift_scrambledColSum, Nat.add_sub_add_right]

/-- The first round preserves the exact full-row baseline, in the column
height representation used by `semanticExec2_decode`. -/
theorem baselineLift_round1_eq {m n : Nat} (c c₁ : MonotoneColumnSums m n)
    (C₁ : MonotoneColumnSums (m + 1) n) (σ₁ : Scramble (m + 1) n)
    (hc₁ : ∀ col, (c₁ col).val = scrambledColSum c (truncateBottomScramble σ₁) col)
    (hC₁ : ∀ col, (C₁ col).val = scrambledColSum (baselineLiftColumnSums c) σ₁ col) :
    C₁ = baselineLiftColumnSums c₁ := by
  funext col
  apply Fin.ext
  rw [hC₁, baselineLift_scrambledColSum, ← hc₁]
  rfl

/-- Exact two-round escape-count transfer, still with no additive padding
charge. The only full-rectangle fringe change is one baseline row. -/
theorem baselineLift_two_round_escapes {m n : Nat} (c c₁ : MonotoneColumnSums m n)
    (C₁ : MonotoneColumnSums (m + 1) n) (σ₁ σ₂ : Scramble (m + 1) n)
    (hc₁ : ∀ col, (c₁ col).val = scrambledColSum c (truncateBottomScramble σ₁) col)
    (hC₁ : ∀ col, (C₁ col).val = scrambledColSum (baselineLiftColumnSums c) σ₁ col)
    (f : Nat) :
    onesAboveBottom C₁ σ₂ (f + 1) =
      onesAboveBottom c₁ (truncateBottomScramble σ₂) f := by
  rw [baselineLift_round1_eq c c₁ C₁ σ₁ hc₁ hC₁]
  exact baselineLift_escapes c₁ σ₂ f

end Tapered945
