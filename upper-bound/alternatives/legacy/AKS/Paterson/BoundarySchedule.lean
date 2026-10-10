module

public import AKS.Paterson.ColdStorage
public import AKS.Separator.PatersonPartialCertificate

/-! # Clipped scheduling and cold-storage conservation

Unlike the full-bag identities, these statements cover the bottom partial
level and empty levels. Source: Paterson (1990), Sections 5 and 7.
-/

@[expose] public section

namespace Paterson.Bags

theorem ceil32_mono : Monotone ceil32 := by
  intro x y h
  exact Nat.mul_le_mul_left 32 (Nat.ceil_mono (by linarith : x / 32 ≤ y / 32))

theorem ceil32_of_nonpos {x : ℚ} (hx : x ≤ 0) : ceil32 x = 0 := by
  simp only [ceil32, Nat.ceil_eq_zero.mpr (show x / 32 ≤ 0 by linarith), Nat.mul_zero]

theorem scheduledSubtree_nonnegative (p : Params) (width cap : ℚ) :
    0 ≤ idealSubtree p width cap := le_max_left _ _

/-- Clipping does not break the nesting of rounded totals, even at the
partial level. In particular, each outgoing middle has a nonnegative size. -/
theorem fast_clipped_nesting {width cap : ℚ}
    (hcap : fastParams.minCapacity ≤ cap) :
    2 * scheduledSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) ≤
      scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) ∧
    2 * scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) ≤
      scheduledSubtree fastParams width cap := by
  let a := width - ancestorReserve fastParams cap
  let g := width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap)
  let next := width / 2 - ancestorReserve fastParams (fastParams.nu * fastParams.A * cap)
  have hiden : a = cap + 4 * g := full_subtree_identity _ _ _
  have hfiden : a / 2 - next = fastParams.lambda * cap / 2 := full_fringe_identity _ _ _
  change 2 * ceil32 (max 0 g) ≤ ceil32 (max 0 next) ∧
    2 * ceil32 (max 0 next) ≤ ceil32 (max 0 a)
  by_cases hg : 0 ≤ g
  · have hcap0 : 0 ≤ cap := fastParams.minCapacity_pos.le.trans hcap
    have ha : 0 ≤ a := by linarith
    have hnext : 0 ≤ next := by
      have hprod := mul_nonneg (sub_nonneg.mpr fastParams.lambda_lt_one.le) hcap0
      nlinarith
    rw [max_eq_right hg, max_eq_right ha, max_eq_right hnext]
    have hl := le_ceil32 next
    have hu := ceil32_lt_add hg
    have haLow := le_ceil32 a
    have hnHigh := ceil32_lt_add hnext
    have hsmallQ : (2 : ℚ) * ceil32 g ≤ ceil32 next := by
      norm_num [fastParams] at hcap hfiden
      linarith
    have hlargeQ : (2 : ℚ) * ceil32 next ≤ ceil32 a := by
      norm_num [fastParams] at hcap hfiden
      linarith
    exact ⟨by exact_mod_cast hsmallQ, by exact_mod_cast hlargeQ⟩
  · have hg0 : max 0 g = 0 := max_eq_left (le_of_not_ge hg)
    rw [hg0, ceil32_of_nonpos (le_refl 0), Nat.mul_zero]
    refine ⟨Nat.zero_le _, ?_⟩
    by_cases hn : 0 ≤ next
    · have ha : 0 ≤ a := by
        norm_num [fastParams] at hcap hfiden
        linarith
      rw [max_eq_right hn, max_eq_right ha]
      have haLow := le_ceil32 a
      have hnHigh := ceil32_lt_add hn
      have hlargeQ : (2 : ℚ) * ceil32 next ≤ ceil32 a := by
        norm_num [fastParams] at hcap hfiden
        linarith
      exact_mod_cast hlargeQ
    · rw [max_eq_left (le_of_not_ge hn), ceil32_of_nonpos (le_refl 0), Nat.mul_zero]
      exact Nat.zero_le _

/-- The root's returning storage allocation fits in the actual storage.
This is the integer conservation used when the root changes from empty to
occupied. The scheduler must establish the supplied subtree totals. -/
theorem root_feed_conservation (width oldChild nextRoot : ℕ)
    (hsmall : 2 * oldChild ≤ nextRoot) (hwidth : nextRoot ≤ width) :
    nextRoot - 2 * oldChild ≤ width - 2 * oldChild ∧
      (width - 2 * oldChild) - (nextRoot - 2 * oldChild) = width - nextRoot := by
  omega

/-- When the root empties, its two fringes augment storage by exactly the
decrease in total content below storage. -/
theorem root_fringe_conservation (width oldRoot nextChild : ℕ)
    (hwidth : oldRoot ≤ width) (hsmall : 2 * nextChild ≤ oldRoot) :
    (width - oldRoot) + (oldRoot - 2 * nextChild) = width - 2 * nextChild := by
  omega

end Paterson.Bags
