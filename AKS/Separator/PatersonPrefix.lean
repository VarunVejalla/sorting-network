module

public import AKS.Separator.PatersonStep

/-! # The five-level supported-range separator on divisible arities -/

@[expose] public section

namespace Paterson

noncomputable def separatorPrefix (n t : ℕ) : ComparatorNetwork n :=
  ⟨(List.range t).flatMap fun level =>
    (halverAtLevel n (stageNetwork level) level).comparators⟩

def prefixError (t : ℕ) : ℝ :=
  ((List.range t).map stageError).sum

theorem separatorPrefix_zero (n : ℕ) :
    separatorPrefix n 0 = ⟨[]⟩ := by
  simp [separatorPrefix]

theorem separatorPrefix_succ (n t : ℕ) :
    separatorPrefix n (t + 1) =
      ⟨(separatorPrefix n t).comparators ++
        (halverAtLevel n (stageNetwork t) t).comparators⟩ := by
  simp only [separatorPrefix, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

theorem prefixError_succ (t : ℕ) :
    prefixError (t + 1) = prefixError t + stageError t := by
  simp [prefixError, List.range_succ]

theorem separatorPrefix_five (n : ℕ) : separatorPrefix n 5 = separatorNetwork n := rfl

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

private theorem stage_support_arithmetic (n t : ℕ) (ht : t < 5)
    (h32 : 32 ∣ n) :
    (patersonMu : ℝ) * n ≤
      (stageAlpha t : ℝ) * ↑(n / 2 ^ t / 2) := by
  have hdiv : 2 ^ (t + 1) ∣ n := by
    exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : t + 1 ≤ 5))
      (by simpa using h32)
  have hsize : 2 ^ (t + 1) * (n / 2 ^ (t + 1)) = n :=
    Nat.mul_div_cancel' hdiv
  have hcast : (n : ℝ) = (2 ^ (t + 1) : ℝ) * ↑(n / 2 ^ (t + 1)) := by
    exact_mod_cast hsize.symm
  rw [stageAlpha_eq t ht, half_chunk_eq n t, hcast]
  push_cast
  exact le_of_eq (by ring)

/-- Every prefix is supported on the same global extreme cohort. For this
version all five local chunk sizes are integral, hence the `32 ∣ n` hypothesis.
The odd-size virtual-element construction remains separate. -/
theorem separatorPrefix_supported (n t : ℕ) (ht : t ≤ 5) (h32 : 32 ∣ n) :
    IsSupportedSeparator (separatorPrefix n t) (n / 2 ^ t)
      (patersonMu : ℝ) (prefixError t) := by
  induction t with
  | zero =>
    simpa [separatorPrefix_zero, prefixError] using
      (empty_supported n (patersonMu : ℝ))
  | succ t ih =>
    have ht' : t < 5 := by omega
    have hdiv : 2 ^ (t + 1) ∣ n := by
      exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : t + 1 ≤ 5))
        (by simpa using h32)
    have h_pow_div : 2 ^ t ∣ n :=
      dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ t)) hdiv
    have h_even : 2 ∣ n / 2 ^ t := by
      rw [pow_succ] at hdiv
      obtain ⟨k, hk⟩ := hdiv
      rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
      exact dvd_mul_right 2 k
    rw [separatorPrefix_succ, prefixError_succ]
    have hstep := supported_halving_step t
      (ih (by omega)) (stageNetwork_halver t _ ht')
      (stageErrorQ_nonneg t ht') h_even h_pow_div
      (stage_support_arithmetic n t ht' h32)
    convert hstep using 1
    · rw [stageError_eq]

theorem separatorNetwork_supported_of_dvd32 (n : ℕ) (h32 : 32 ∣ n) :
    IsSupportedSeparator (separatorNetwork n) (n / 32)
      (patersonMu : ℝ) (prefixError 5) := by
  simpa [separatorPrefix_five] using separatorPrefix_supported n 5 (by omega) h32

end Paterson
