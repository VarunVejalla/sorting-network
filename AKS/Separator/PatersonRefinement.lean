module

public import AKS.Separator.PatersonPrefix

/-! # Four refinement levels for padded partial bags

These are the last four levels of the Paterson separator, shifted to a single
half block. They filter cohorts of size at most twice mu times that half
block size, with depth at most 726. The actual initial half split is separate.
-/

@[expose] public section

namespace Paterson

noncomputable def refinementPrefix (n t : ℕ) : ComparatorNetwork n :=
  ⟨(List.range t).flatMap fun level =>
    (halverAtLevel n (stageNetwork (level + 1)) level).comparators⟩

def refinementError (t : ℕ) : ℝ :=
  ((List.range t).map (fun level => stageError (level + 1))).sum

theorem refinementPrefix_zero (n : ℕ) :
    refinementPrefix n 0 = ⟨[]⟩ := by
  simp [refinementPrefix]

theorem refinementPrefix_succ (n t : ℕ) :
    refinementPrefix n (t + 1) =
      ⟨(refinementPrefix n t).comparators ++
        (halverAtLevel n (stageNetwork (t + 1)) t).comparators⟩ := by
  simp only [refinementPrefix, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

theorem refinementError_succ (t : ℕ) :
    refinementError (t + 1) = refinementError t + stageError (t + 1) := by
  simp [refinementError, List.range_succ]

private theorem empty_supported (n : ℕ) (support : ℝ) :
    IsSupportedSeparator (⟨[]⟩ : ComparatorNetwork n) n support 0 := by
  intro v
  constructor
  · intro k _
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        n ≤ pos.val ∧ ((⟨[]⟩ : ComparatorNetwork n).exec v pos).val < k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨hpos, _⟩
      exact (Nat.not_le.mpr pos.isLt) hpos
    simp [hempty]
  · intro k _
    simp

private theorem stage_support_arithmetic (n t : ℕ) (ht : t < 4)
    (h16 : 16 ∣ n) :
    (2 * patersonMu : ℝ) * n ≤
      (stageAlpha (t + 1) : ℝ) * ↑(n / 2 ^ t / 2) := by
  have hdiv : 2 ^ (t + 1) ∣ n := by
    exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : t + 1 ≤ 4))
      (by simpa using h16)
  have hsize : 2 ^ (t + 1) * (n / 2 ^ (t + 1)) = n :=
    Nat.mul_div_cancel' hdiv
  have hcast : (n : ℝ) = (2 ^ (t + 1) : ℝ) * ↑(n / 2 ^ (t + 1)) := by
    exact_mod_cast hsize.symm
  rw [stageAlpha_eq (t + 1) (by omega), half_chunk_eq n t, hcast]
  push_cast
  exact le_of_eq (by simp only [pow_succ]; ring)

/-- Every prefix is supported on the same global extreme cohort. For this
version all four local chunk sizes are integral, hence the `16 ∣ n` hypothesis.
Arbitrary virtual padding is handled in `Paterson.Padding`. -/
theorem refinementPrefix_supported (n t : ℕ) (ht : t ≤ 4) (h16 : 16 ∣ n) :
    IsSupportedSeparator (refinementPrefix n t) (n / 2 ^ t)
      (2 * patersonMu : ℝ) (refinementError t) := by
  induction t with
  | zero =>
    simpa [refinementPrefix_zero, refinementError] using
      (empty_supported n (2 * patersonMu : ℝ))
  | succ t ih =>
    have ht' : t < 4 := by omega
    have hdiv : 2 ^ (t + 1) ∣ n := by
      exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : t + 1 ≤ 4))
        (by simpa using h16)
    have h_pow_div : 2 ^ t ∣ n :=
      dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ t)) hdiv
    have h_even : 2 ∣ n / 2 ^ t := by
      rw [pow_succ] at hdiv
      obtain ⟨k, hk⟩ := hdiv
      rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
      exact dvd_mul_right 2 k
    rw [refinementPrefix_succ, refinementError_succ]
    have hstep := supported_halving_step t
      (ih (by omega)) (stageNetwork_halver (t + 1) _ (by omega))
      (stageErrorQ_nonneg (t + 1) (by omega)) h_even h_pow_div
      (stage_support_arithmetic n t ht' h16)
    convert hstep using 1
    · rw [stageError_eq]


noncomputable def refinementNetwork (n : ℕ) : ComparatorNetwork n :=
  refinementPrefix n 4

def refinementTailError : ℚ :=
  patersonDelta2 + patersonDelta3 + patersonDelta4 + patersonDelta5

theorem refinementError_four : refinementError 4 = (refinementTailError : ℝ) := by
  norm_num [refinementError, stageError, refinementTailError, List.range_succ]
  ring

theorem refinementNetwork_supported (n : ℕ) (h16 : 16 ∣ n) :
    IsSupportedSeparator (refinementNetwork n) (n / 16)
      (2 * patersonMu : ℝ) (refinementTailError : ℝ) := by
  simpa only [refinementNetwork, refinementError_four] using
    refinementPrefix_supported n 4 (by omega) h16

private theorem refinementList_depth_le (n : ℕ) (levels : List ℕ) :
    (⟨levels.flatMap fun level =>
      (halverAtLevel n (stageNetwork (level + 1)) level).comparators⟩ :
        ComparatorNetwork n).depth ≤
      (levels.map (fun level => stageDepth (level + 1))).sum := by
  induction levels with
  | nil => simp [ComparatorNetwork.depth]
  | cons level levels ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    have happ := depth_append
      (halverAtLevel n (stageNetwork (level + 1)) level)
      (⟨levels.flatMap fun j =>
        (halverAtLevel n (stageNetwork (j + 1)) j).comparators⟩ : ComparatorNetwork n)
    have hlevel := halverAtLevel_depth_le n (stageNetwork (level + 1))
      (stageNetwork_depth_le (level + 1)) level
    exact happ.trans (add_le_add hlevel ih)

theorem refinementNetwork_depth_le (n : ℕ) : (refinementNetwork n).depth ≤ 726 := by
  have h := refinementList_depth_le n (List.range 4)
  change (refinementNetwork n).depth ≤ _ at h
  norm_num [stageDepth, List.range_succ] at h
  exact h

end Paterson
