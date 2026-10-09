module
public import AKS.Chvatal.PhysicalPack
public import AKS.Chvatal.NodeSpec

/-! # Position-form high-side node guarantee from semantic Properties B and F

Translates the semantic Properties B and F of the canonical sort-scramble-sort pack into the
high-side (`bHigh`, `fHigh`) position form of `NodeSpec` for `physicalPackNet` (cell `c = r*n + col`). -/

@[expose] public section

namespace Chvatal

/-- For a threshold `t` on key values, the cells in the top `m - i` rows of the physical output
whose key is among the largest `t` number as many as the ones in the region of the semantic output on
the `t`-threshold marking of `x`. -/
theorem physical_threshold_count_eq_semantic {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (x : Equiv.Perm (Fin (m * n))) (t i : ℕ) :
    (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - i * n).card =
      matrixOnesCountInRegion hn
        ((canonicalSortScrambleSortPack m n hn σ).semanticExec
          (fun w => decide (m * n - t ≤ (x w).val))) i := by
  classical
  have hmono : Monotone (fun k : Fin (m * n) => decide (m * n - t ≤ k.val)) := fun a b hab => by
    by_cases ha : m * n - t ≤ a.val
    · simp [ha, show m * n - t ≤ b.val from ha.trans (Fin.mk_le_mk.mp hab)]
    · simp [ha]
  have hcomm := (physicalPackNet m n hn σ).exec_comp_monotone hmono
    (x : Fin (m * n) → Fin (m * n))
  have h1 := physicalPackNet_rowRegion_card hn σ
    (fun w => decide (m * n - t ≤ (x w).val))
    (Finset.univ.filter fun r : Fin m => r.val < m - i) (fun b : Bool => b = true)
  have e1 : (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - i * n) =
      (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ (Finset.univ.filter fun r : Fin m => r.val < m - i) ∧
          (physicalPackNet m n hn σ).exec (fun w => decide (m * n - t ≤ (x w).val)) w = true) := by
    ext c
    have hc : (physicalPackNet m n hn σ).exec (fun w => decide (m * n - t ≤ (x w).val)) c =
        decide (m * n - t ≤ ((physicalPackNet m n hn σ).exec
          (x : Fin (m * n) → Fin (m * n)) c).val) := by
      simpa [Function.comp] using (congrFun hcomm c).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc, decide_eq_true_iff, matrixRow_val,
      Nat.div_lt_iff_lt_mul hn, Nat.sub_mul]
    exact and_comm
  rw [e1, h1]
  unfold matrixOnesCountInRegion
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

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
  rw [show 2 * f * n / 2 = f * n by rw [mul_assoc]; omega,
    physical_threshold_count_eq_semantic hn σ x j f]
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
  rw [show 2 * f * n / 2 = f * n by rw [mul_assoc]; omega,
    show f * n + k * (b * n) = (f + k * b) * n by ring] at hpmn ⊢
  generalize f + k * b = i at hpmn ⊢
  have him : i ≤ m := by
    by_contra h
    have : m * n < i * n := Nat.mul_lt_mul_of_pos_right (not_le.mp h) hn
    omega
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hempty : (Finset.univ.filter fun c : Fin (m * n) =>
          m * n - 0 * n ≤ ((physicalPackNet m n hn σ).exec
            (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n - 0 * n) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun c _ ⟨h1, h2⟩ => ?_
      have := ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).isLt
      simp at h1 h2
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · simp
    · have h := hB (Equiv.refl _) 1 le_rfl h0
      have : (0 : ℝ) ≤ (packSemanticIntrusionCountB hn
        (canonicalSortScrambleSortPack m n hn σ) (Equiv.refl _) 1 : ℝ) := Nat.cast_nonneg _
      linarith
  · have h := hB x i hi0 him
    rw [show packSemanticIntrusionCountB hn (canonicalSortScrambleSortPack m n hn σ) x i =
      matrixOnesCountInRegion hn ((canonicalSortScrambleSortPack m n hn σ).semanticExec
          (fun w => decide (m * n - i * n ≤ (x w).val))) i from rfl,
      ← physical_threshold_count_eq_semantic hn σ x (i * n) i] at h
    exact h.le

end Chvatal
