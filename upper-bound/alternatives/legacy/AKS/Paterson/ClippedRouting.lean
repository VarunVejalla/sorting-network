module

public import AKS.Paterson.BoundarySchedule

/-! # Exact rounded routing at full, partial, and empty levels -/

@[expose] public section

namespace Paterson.Bags

theorem fast_clipped_routing {width cap : ℚ}
    (hcap : fastParams.minCapacity ≤ cap) :
    scheduledFringe fastParams width cap ≤ scheduledBag fastParams width cap / 2 ∧
      scheduledBag fastParams width cap / 2 - scheduledFringe fastParams width cap =
        scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) -
          2 * scheduledSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) ∧
      2 * scheduledFringe fastParams width cap =
        scheduledSubtree fastParams width cap -
          2 * scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) := by
  obtain ⟨hsmall, hlarge⟩ := fast_clipped_nesting (width := width) hcap
  have hd : 2 ∣ scheduledSubtree fastParams width cap :=
    dvd_trans (by norm_num) (ceil32_dvd _)
  have heven := Nat.mul_div_cancel' hd
  unfold scheduledFringe scheduledBag
  omega

/-- A rounded ideal half can hold half the rounded ideal whole. -/
theorem ceil32_le_double_half (cap : ℚ) : ceil32 cap ≤ 2 * ceil32 (cap / 2) := by
  have harg : cap / 2 / 32 = cap / 64 := by ring
  have hl := Nat.le_ceil (cap / 64)
  have hc : ⌈cap / 32⌉₊ ≤ 2 * ⌈cap / 64⌉₊ := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  simp only [ceil32, harg]
  omega

/-- The actual partial half fits the padded refinement arity, including
empty partial bags. Each padded arity is divisible by 32. -/
theorem partial_half_fits {width cap : ℚ} (hc : 0 ≤ cap)
    (hpartial : width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap) ≤ 0) :
    scheduledBag fastParams width cap / 2 ≤ ceil32 (cap / 2) := by
  have hiden := full_subtree_identity fastParams width cap
  have hclip : idealSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) = 0 :=
    max_eq_left hpartial
  have hg : scheduledSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) = 0 := by
    simp only [scheduledSubtree, hclip, ceil32_of_nonpos (le_refl 0)]
  have hideal : idealSubtree fastParams width cap ≤ cap := by
    apply max_le hc
    linarith
  have hn : scheduledSubtree fastParams width cap ≤ ceil32 cap := ceil32_mono hideal
  have hh := ceil32_le_double_half cap
  simp only [scheduledBag, hg, Nat.mul_zero, Nat.sub_zero]
  omega

/-- Whenever a lower subtree is nonempty, the rounded fringe covers the
padded refinement's ideal fringe. Empty outgoing middles need no filter. -/
theorem fast_virtual_fringe_coverage {width cap : ℚ}
    (hc : fastParams.minCapacity ≤ cap)
    (hn : 0 ≤ width / 2 - ancestorReserve fastParams (fastParams.nu * fastParams.A * cap)) :
    ceil32 (cap / 2) / 16 ≤ scheduledFringe fastParams width cap := by
  let a := width - ancestorReserve fastParams cap
  let next := width / 2 - ancestorReserve fastParams (fastParams.nu * fastParams.A * cap)
  have hnext : 0 ≤ next := hn
  have hiden : a / 2 - next = fastParams.lambda * cap / 2 := full_fringe_identity _ _ _
  have hcap0 : 0 ≤ cap := fastParams.minCapacity_pos.le.trans hc
  have ha : 0 ≤ a := by
    have := mul_nonneg fastParams.lambda_pos.le hcap0
    linarith
  have haLow := le_ceil32 a
  have hnHigh := ceil32_lt_add hnext
  have hfHigh := ceil32_lt_add (show 0 ≤ cap / 2 by linarith)
  have heven : 2 ∣ ceil32 a := dvd_trans (by norm_num) (ceil32_dvd a)
  have hhalf : ((ceil32 a / 2 : ℕ) : ℚ) * 2 = ceil32 a := by
    exact_mod_cast Nat.div_mul_cancel heven
  have hlarge : ceil32 next ≤ ceil32 a / 2 := by
    have hQ : (ceil32 next : ℚ) ≤ (ceil32 a / 2 : ℕ) := by
      norm_num [fastParams] at hc hiden
      linarith
    exact_mod_cast hQ
  have hcoverage : ((ceil32 (cap / 2) / 16 : ℕ) : ℚ) ≤
      ((ceil32 a / 2 - ceil32 next : ℕ) : ℚ) := by
    have hdiv : ((ceil32 (cap / 2) / 16 : ℕ) : ℚ) ≤ (ceil32 (cap / 2) : ℚ) / 16 :=
      Nat.cast_div_le
    rw [Nat.cast_sub hlarge]
    norm_num [fastParams] at hc hiden
    linarith
  have hnat : ceil32 (cap / 2) / 16 ≤ ceil32 a / 2 - ceil32 next := by exact_mod_cast hcoverage
  change ceil32 (cap / 2) / 16 ≤ ceil32 (max 0 a) / 2 - ceil32 (max 0 next)
  rw [max_eq_right ha, max_eq_right hnext]
  exact hnat

end Paterson.Bags
