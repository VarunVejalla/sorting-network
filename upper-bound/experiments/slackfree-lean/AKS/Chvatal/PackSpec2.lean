module
public import AKS.Chvatal.ScrambleMonotone
public import AKS.Chvatal.PackSpec
public import AKS.Chvatal.FlipSpec

/-! # Two-round semantic Properties B/F and the position-form node guarantee

`HasPackSemanticPropertyB2/F2` are the analogues of `HasPackSemanticPropertyB/F` for
`semanticExec2`.  Round-1 Property F implies two-round Property F for every second scramble
(`ScrambleMonotone`); two-round Property B is a hypothesis (probabilistic content). -/

@[expose] public section

namespace Chvatal

/-- Matrix Property B for the two-round semantic map. -/
def HasPackSemanticPropertyB2 {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n) (epsB : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (i : Nat), 1 ≤ i → i ≤ m →
    (matrixOnesCountInRegion hn
        (semanticExec2 hn σ1 σ2
          fun w => largestKeyThresholdJ01 (m := m) (n := n) (i * n) (v w)) i : ℝ) <
      (epsB / 2) * (m * n)

/-- Matrix Property F for the two-round semantic map. -/
def HasPackSemanticPropertyF2 {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n) (f : Nat)
    (_hfm : f ≤ m) (deltaF epsF : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (j : Nat), 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
    (matrixOnesCountInRegion hn
        (semanticExec2 hn σ1 σ2
          fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) f : ℝ) <
      epsF * j

/-- **Round-1 Property F gives two-round Property F for any second scramble.** -/
theorem HasPackSemanticPropertyF2.of_F {m n f : Nat} (hn : 0 < n) {σ1 : Scramble m n}
    (σ2 : Scramble m n) {hfm : f ≤ m} {deltaF epsF : ℝ}
    (hF : HasPackSemanticPropertyF hn σ1 f hfm deltaF epsF) :
    HasPackSemanticPropertyF2 hn σ1 σ2 f hfm deltaF epsF := fun v j hj hjd =>
  lt_of_le_of_lt (by exact_mod_cast matrixOnesCountInRegion_semanticExec2_le hn σ1 σ2 _ f)
    (hF v j hj hjd)

/-- Round-1 Property B gives two-round Property B (with the same `epsB`) for any `σ2`. -/
theorem HasPackSemanticPropertyB2.of_B {m n : Nat} (hn : 0 < n) {σ1 : Scramble m n}
    (σ2 : Scramble m n) {epsB : ℝ} (hB : HasPackSemanticPropertyB hn σ1 epsB) :
    HasPackSemanticPropertyB2 hn σ1 σ2 epsB := fun v i hi1 him =>
  lt_of_le_of_lt (by exact_mod_cast matrixOnesCountInRegion_semanticExec2_le hn σ1 σ2 _ i)
    (hB v i hi1 him)

/-- For a threshold `t` on key values, the cells in the top `m - i` rows of the physical output
whose key is among the largest `t` number as many as the ones in the region of the semantic output on
the `t`-threshold marking of `x`. -/
theorem physical_threshold_count_eq_semantic2 {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (x : Equiv.Perm (Fin (m * n))) (t i : ℕ) :
    (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - i * n).card =
      matrixOnesCountInRegion hn
        (semanticExec2 hn σ1 σ2
          (fun w => decide (m * n - t ≤ (x w).val))) i := by
  classical
  have hmono : Monotone (fun k : Fin (m * n) => decide (m * n - t ≤ k.val)) := fun a b hab => by
    by_cases ha : m * n - t ≤ a.val
    · simp [ha, show m * n - t ≤ b.val from ha.trans (Fin.mk_le_mk.mp hab)]
    · simp [ha]
  have hcomm := (physicalPack2Net m n hn σ1 σ2).exec_comp_monotone hmono
    (x : Fin (m * n) → Fin (m * n))
  have h1 := physicalPack2Net_rowRegion_card hn σ1 σ2
    (fun w => decide (m * n - t ≤ (x w).val))
    (Finset.univ.filter fun r : Fin m => r.val < m - i) (fun b : Bool => b = true)
  have e1 : (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - i * n) =
      (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ (Finset.univ.filter fun r : Fin m => r.val < m - i) ∧
          (physicalPack2Net m n hn σ1 σ2).exec (fun w => decide (m * n - t ≤ (x w).val)) w = true) := by
    ext c
    have hc : (physicalPack2Net m n hn σ1 σ2).exec (fun w => decide (m * n - t ≤ (x w).val)) c =
        decide (m * n - t ≤ ((physicalPack2Net m n hn σ1 σ2).exec
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

theorem packSpec2_high_F {m n f : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n) (hfm : f ≤ m)
    {deltaF epsF : ℝ}
    (hF : HasPackSemanticPropertyF2 hn σ1 σ2 f hfm
      deltaF epsF)
    (x : Equiv.Perm (Fin (m * n))) (j : ℕ) (hj : 0 < j) (hjd : (j : ℝ) ≤ deltaF * (f * n)) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - j ≤ ((physicalPack2Net m n hn σ1 σ2).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - (2 * f * n) / 2).card : ℝ) < epsF * j := by
  have h := hF x j hj hjd
  rw [show 2 * f * n / 2 = f * n by rw [mul_assoc]; omega,
    physical_threshold_count_eq_semantic2 hn σ1 σ2 x j f]
  exact h

theorem packSpec2_high {m n f b : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB deltaF epsF : ℝ}
    (hB : HasPackSemanticPropertyB2 hn σ1 σ2 epsB)
    (hF : HasPackSemanticPropertyF2 hn σ1 σ2 f hfm
      deltaF epsF) :
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ p ∈ blockBounds (2 * f * n) (b * n), p ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - p ≤ ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - p).card : ℝ) ≤ epsB / 2 * (m * n)) ∧
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ j : ℕ, 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      j ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        m * n - j ≤ ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - (2 * f * n) / 2).card : ℝ) < epsF * j) := by
  refine ⟨?_, fun x j hj hjd _ => packSpec2_high_F hn σ1 σ2 hfm hF x j hj hjd⟩
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
          m * n - 0 * n ≤ ((physicalPack2Net m n hn σ1 σ2).exec
            (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n - 0 * n) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun c _ ⟨h1, h2⟩ => ?_
      have := ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).isLt
      simp at h1 h2
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · simp
    · exact ((Nat.cast_nonneg _).trans_lt (hB (Equiv.refl _) 1 le_rfl h0)).le
  · have h := hB x i hi0 him
    change (matrixOnesCountInRegion hn (semanticExec2 hn σ1 σ2
          (fun w => decide (m * n - i * n ≤ (x w).val))) i : ℝ) < _ at h
    rw [← physical_threshold_count_eq_semantic2 hn σ1 σ2 x (i * n) i] at h
    exact h.le


/-! ## Flip symmetry for two rounds -/

theorem rowScrambleWirePerm2_flip {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (w : Fin (m * n)) :
    rowScrambleWirePerm2 m n hn (flipScramble σ1) (flipScramble σ2) (Fin.rev w) =
      Fin.rev (rowScrambleWirePerm2 m n hn σ1 σ2 w) := by
  show rowScrambleWirePerm m n hn (flipScramble σ2)
      (rowScrambleWirePerm m n hn (flipScramble σ1) (Fin.rev w)) = _
  rw [rowScrambleWirePerm_flip, rowScrambleWirePerm_flip]
  rfl

theorem semanticExec2_flip {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (x : Fin (m * n) → Fin (m * n)) :
    semanticExec2 hn (flipScramble σ1) (flipScramble σ2)
        (fun w => Fin.rev (x (Fin.rev w))) =
      fun w => Fin.rev (semanticExec2 hn σ1 σ2 x (Fin.rev w)) := by
  have h : semanticExec hn (flipScramble σ1) (fun w => Fin.rev (x (Fin.rev w))) ∘
        (rowScrambleWirePerm m n hn (flipScramble σ2)).symm =
      fun w => Fin.rev ((semanticExec hn σ1 x ∘
        (rowScrambleWirePerm m n hn σ2).symm) (Fin.rev w)) := by
    funext w
    simp only [Function.comp_apply]
    rw [semanticExec_flip]
    have h2 : (rowScrambleWirePerm m n hn (flipScramble σ2)).symm w =
        Fin.rev ((rowScrambleWirePerm m n hn σ2).symm (Fin.rev w)) := by
      have := rowScrambleWirePerm_symm_flip hn σ2 (Fin.rev w)
      rwa [Fin.rev_rev] at this
    simp only [h2, Fin.rev_rev]
  unfold semanticExec2
  rw [h]
  exact colSort_flip hn _

theorem physicalPack2Net_flip {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (x : Fin (m * n) → Fin (m * n)) :
    (physicalPack2Net m n hn (flipScramble σ1) (flipScramble σ2)).exec
        (fun w => Fin.rev (x (Fin.rev w))) =
      fun c => Fin.rev ((physicalPack2Net m n hn σ1 σ2).exec x (Fin.rev c)) := by
  funext c
  rw [physicalPack2Net_exec, physicalPack2Net_exec]
  show semanticExec2 hn (flipScramble σ1) (flipScramble σ2) _
      (rowScrambleWirePerm2 m n hn (flipScramble σ1) (flipScramble σ2) c) = _
  rw [semanticExec2_flip]
  show Fin.rev (semanticExec2 hn σ1 σ2 x
      (Fin.rev (rowScrambleWirePerm2 m n hn (flipScramble σ1) (flipScramble σ2) c))) =
    Fin.rev (semanticExec2 hn σ1 σ2 x
      (rowScrambleWirePerm2 m n hn σ1 σ2 (Fin.rev c)))
  congr 2
  have := rowScrambleWirePerm2_flip hn σ1 σ2 (Fin.rev c)
  rw [Fin.rev_rev] at this
  rw [this, Fin.rev_rev]

theorem packSpec2_low {m n f b : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB deltaF epsF : ℝ}
    (hB' : HasPackSemanticPropertyB2 hn (flipScramble σ1) (flipScramble σ2) epsB)
    (hF' : HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) f hfm deltaF epsF) :
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ p ∈ blockBounds (2 * f * n) (b * n), p ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val < p ∧
          p ≤ c.val).card : ℝ) ≤ epsB / 2 * (m * n)) ∧
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ j : ℕ, 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val < j ∧
          (2 * f * n) / 2 ≤ c.val).card : ℝ) < epsF * j) := by
  have hH := packSpec2_high hn (flipScramble σ1) (flipScramble σ2) hmfb hfm hB' hF'
  have key : ∀ (x : Equiv.Perm (Fin (m * n))) (t s : ℕ),
      (Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPack2Net m n hn σ1 σ2).exec (x : Fin (m * n) → Fin (m * n)) c).val < t ∧
          s ≤ c.val).card =
      (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPack2Net m n hn (flipScramble σ1) (flipScramble σ2)).exec
          ((flipPerm x : Equiv.Perm (Fin (m * n))) : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - s).card := by
    intro x t s
    refine card_low_eq_high _ _ (fun c => ?_) t s
    exact congrFun (physicalPack2Net_flip hn σ1 σ2 (x : Fin (m * n) → Fin (m * n))) c
  refine ⟨fun x p hp hpmn => ?_, fun x j hj hjd => ?_⟩
  · rw [key x p p]
    exact hH.1 (flipPerm x) p hp hpmn
  · rw [key x j _]
    have hdiv : 2 * f * n / 2 = f * n := by
      rw [show 2 * f * n = 2 * (f * n) by ring]; omega
    rw [hdiv]
    have := packSpec2_high_F hn (flipScramble σ1) (flipScramble σ2) hfm hF' (flipPerm x) j hj hjd
    rw [hdiv] at this
    exact this

end Chvatal
