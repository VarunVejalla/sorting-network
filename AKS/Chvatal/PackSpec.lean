module
/-
  # Position-form high-side node guarantee from semantic Properties B and F (P1)

  Translates the matrix-level semantic Properties B and F of the canonical sort–scramble–sort
  pack (0/1 markings of the largest keys, row regions of the semantic output) into the
  high-side (`bHigh`, `fHigh`) position form of `NodeSpec` for the PHYSICAL network
  `physicalPackNet`. Cell `c` is the wire `c = r*n + col` (row `c / n`), ascending order.

  Ingredients: `physicalPackNet_rowRegion_card` (rows regions agree physical vs semantic),
  `ComparatorNetwork.exec_comp_monotone` (threshold marking commutes with the physical
  network), and the Fin-value reading of `largestKeyThreshold01` / `largestKeyThresholdJ01`.
-/

public import AKS.Chvatal.PhysicalPack
public import AKS.Chvatal.NodeSpec
public import AKS.Chvatal.SortedColumnDecode

@[expose] public section

namespace Chvatal

/-- Cells `c < (m-i)*n` are exactly the cells in rows `< m - i`. -/
theorem matrixRow_lt_iff_val_lt {m n : ℕ} (hn : 0 < n) (i : ℕ) (w : Fin (m * n)) :
    (matrixRow m n hn w).val < m - i ↔ w.val < (m - i) * n := by
  rw [matrixRow_val]
  exact Nat.div_lt_iff_lt_mul hn

/-- Core translation: for a threshold `t` on key values, the number of cells in the top
`m - i` rows (cells `< (m-i)*n`) of the physical output whose key is among the largest `t`
equals the number of ones in the region of the semantic output on the `t`-threshold marking
of `x`. -/
theorem physical_threshold_count_eq_semantic {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (x : Equiv.Perm (Fin (m * n))) (t i : ℕ) :
    (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < (m - i) * n).card =
      matrixOnesCountInRegion hn
        ((canonicalSortScrambleSortPack m n hn σ).semanticExec
          (fun w => decide (m * n - t ≤ (x w).val))) i := by
  classical
  have hmono : Monotone (fun k : Fin (m * n) => decide (m * n - t ≤ k.val)) := by
    intro a b hab
    by_cases ha : m * n - t ≤ a.val
    · have hb : m * n - t ≤ b.val := le_trans ha (Fin.mk_le_mk.mp hab)
      simp [ha, hb]
    · simp [ha]
  have hcomm := (physicalPackNet m n hn σ).exec_comp_monotone hmono
    (x : Fin (m * n) → Fin (m * n))
  have h1 := physicalPackNet_rowRegion_card hn σ
    (fun w => decide (m * n - t ≤ (x w).val))
    (Finset.univ.filter fun r : Fin m => r.val < m - i) (fun b : Bool => b = true)
  have e1 : (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < (m - i) * n) =
      (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ (Finset.univ.filter fun r : Fin m => r.val < m - i) ∧
          (physicalPackNet m n hn σ).exec (fun w => decide (m * n - t ≤ (x w).val)) w = true) := by
    ext c
    have hc : (physicalPackNet m n hn σ).exec
        (fun w => decide (m * n - t ≤ (x w).val)) c =
        decide (m * n - t ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val) := by
      have := congrFun hcomm c
      simpa [Function.comp] using this.symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc, decide_eq_true_iff,
      matrixRow_lt_iff_val_lt hn]
    exact and_comm
  rw [e1, h1]
  unfold matrixOnesCountInRegion
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem packSpec_high_B {m n : ℕ} (hn : 0 < n) (σ : Scramble m n) {epsB : ℝ}
    (hB : HasPackSemanticPropertyB hn (canonicalSortScrambleSortPack m n hn σ) epsB)
    (x : Equiv.Perm (Fin (m * n))) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - i * n ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - i * n).card : ℝ) ≤ epsB / 2 * (m * n) := by
  have h := hB x i hi1 him
  have heq := physical_threshold_count_eq_semantic hn σ x (i * n) i
  have hdef : packSemanticIntrusionCountB hn (canonicalSortScrambleSortPack m n hn σ) x i =
      matrixOnesCountInRegion hn
        ((canonicalSortScrambleSortPack m n hn σ).semanticExec
          (fun w => decide (m * n - i * n ≤ (x w).val))) i := rfl
  rw [hdef, ← heq] at h
  have hs : m * n - i * n = (m - i) * n := (Nat.sub_mul m i n).symm
  have hc : (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - i * n ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n - i * n) =
      (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - i * n ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < (m - i) * n) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
  rw [hc]
  exact h.le

theorem packSpec_high_F {m n f : ℕ} (hn : 0 < n) (σ : Scramble m n) (hfm : f ≤ m)
    {deltaF epsF : ℝ}
    (hF : HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm
      deltaF epsF)
    (x : Equiv.Perm (Fin (m * n))) (j : ℕ) (hj : 0 < j) (hjd : (j : ℝ) ≤ deltaF * (f * n)) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - j ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - (2 * f * n) / 2).card : ℝ) < epsF * j := by
  have h := hF x j hj hjd
  have heq := physical_threshold_count_eq_semantic hn σ x j f
  have hdiv : 2 * f * n / 2 = f * n := by
    rw [show 2 * f * n = 2 * (f * n) by ring]; omega
  have hdef : packSemanticIntrusionCountF hn (canonicalSortScrambleSortPack m n hn σ) x f j =
      matrixOnesCountInRegion hn
        ((canonicalSortScrambleSortPack m n hn σ).semanticExec
          (fun w => decide (m * n - j ≤ (x w).val))) f := rfl
  rw [hdef, ← heq] at h
  rw [hdiv, show m * n - f * n = (m - f) * n from (Nat.sub_mul m f n).symm]
  exact h

theorem packSpec_high {m n f b : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB deltaF epsF : ℝ}
    (hB : HasPackSemanticPropertyB hn (canonicalSortScrambleSortPack m n hn σ) epsB)
    (hF : HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm
      deltaF epsF) :
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ p ∈ blockBounds (2 * f * n) (b * n), p ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - p ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - p).card : ℝ) ≤ epsB / 2 * (m * n)) ∧
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ j : ℕ, 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      j ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - j ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - (2 * f * n) / 2).card : ℝ) < epsF * j) := by
  refine ⟨?_, fun x j hj hjd _ => packSpec_high_F hn σ hfm hF x j hj hjd⟩
  intro x p hp hpmn
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
  have hdiv : 2 * f * n / 2 = f * n := by
    rw [show 2 * f * n = 2 * (f * n) by ring]; omega
  rw [hdiv] at hpmn ⊢
  have hpi : f * n + k * (b * n) = (f + k * b) * n := by ring
  rw [hpi] at hpmn ⊢
  generalize f + k * b = i at hpmn ⊢
  have him : i ≤ m := by
    by_contra h
    have : m * n < i * n := Nat.mul_lt_mul_of_pos_right (not_le.mp h) hn
    omega
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have hempty : (Finset.univ.filter fun c : Fin (m * n) =>
          m * n - 0 * n ≤ ((physicalPackNet m n hn σ).exec
            (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n - 0 * n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      have := ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).isLt
      simp at h1 h2
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp
    · have h := hB (Equiv.refl _) 1 le_rfl h0
      have h' : (0 : ℝ) ≤ (packSemanticIntrusionCountB hn
        (canonicalSortScrambleSortPack m n hn σ) (Equiv.refl _) 1 : ℝ) := Nat.cast_nonneg _
      linarith
  · exact packSpec_high_B hn σ hB x i hi0 him

end Chvatal
