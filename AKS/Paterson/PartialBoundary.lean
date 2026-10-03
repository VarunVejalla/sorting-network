module

public import AKS.Paterson.StoredBalance

/-! # Boundary decay without descendant contributions

A small partial bag need not contain the entire usual large cohort. The
cohort used in the proof is the minimum of the usual supported cohort and
the actual available input count. This changes no comparator network.
Source: Paterson (1990), Section 5.
-/

@[expose] public section

namespace Paterson.Bags

def availableCohort (half available : ℕ) : ℕ := min (goodCohort half) available

theorem availableCohort_bounds (half available : ℕ) :
    availableCohort half available ≤ available ∧
      (availableCohort half available : ℚ) ≤ patersonAlpha0 * half ∧
      availableCohort half available ≤ half := by
  have h := goodCohort_bounds half
  exact ⟨Nat.min_le_right _ _,
    (Nat.cast_le.mpr (Nat.min_le_left _ _)).trans h.2.1,
    (Nat.min_le_left _ _).trans h.2.2⟩

/-- Old strange cohorts fit the actual first split whenever a nonempty
middle is sent down; virtual refinement uses the ideal half capacity. -/
theorem fast_partial_support {cap : ℚ} {half full : ℕ}
    (hcap : fastParams.minCapacity ≤ cap)
    (hhalf : (fastParams.lambda * cap - 64) / 2 ≤ (half : ℚ))
    (hfull : cap / 2 ≤ (full : ℚ)) :
    fastParams.mu * cap ≤ patersonAlpha0 * half ∧
      fastParams.mu * cap ≤ 2 * patersonMu * full := by
  norm_num [fastParams, patersonAlpha0_eq, patersonMu] at *
  constructor <;> linarith

/-- Even if the partial input cannot supply the usual cohort, the sibling
deficit bounds its shortage. The absent child contribution leaves sufficient
slack in the first-stranger invariant. -/
theorem fast_partial_fresh {cap reserve old : ℚ} {half available : ℕ}
    (hcap : fastParams.minCapacity ≤ cap)
    (hhalf : (half : ℚ) ≤ cap / 2 + 16)
    (hreserve : reserve ≤ ancestorReserve fastParams cap / 2 + 32)
    (hold : old ≤ fastParams.mu * cap)
    (havail : (half : ℚ) - reserve - old ≤ available) :
    (patersonDelta0 + refinementTailError) * old +
      ((half : ℚ) - availableCohort half available +
        patersonDelta0 * availableCohort half available) ≤
      fastParams.mu * (fastParams.nu * (fastParams.A * cap)) := by
  have hgood := goodCohort_bounds half
  have hr := (availableCohort_bounds half available).2.2
  have hrQ : (availableCohort half available : ℚ) ≤ half := by exact_mod_cast hr
  have hdelta : 0 ≤ patersonDelta0 := by norm_num [patersonDelta0]
  have hterm : patersonDelta0 * (availableCohort half available : ℚ) ≤
      patersonDelta0 * half := mul_le_mul_of_nonneg_left hrQ hdelta
  by_cases h : goodCohort half ≤ available
  · have heq : availableCohort half available = goodCohort half := Nat.min_eq_left h
    rw [heq] at *
    norm_num [fastParams, refinementTailError, patersonDelta0, patersonDelta2,
      patersonDelta3, patersonDelta4, patersonDelta5, patersonAlpha0_eq] at *
    linarith
  · have heq : availableCohort half available = available := Nat.min_eq_right (by omega)
    rw [heq] at *
    norm_num [fastParams, ancestorReserve, refinementTailError, patersonDelta0,
      patersonDelta2, patersonDelta3, patersonDelta4, patersonDelta5] at *
    linarith

/-- Higher-order decay at the bottom boundary has no incoming child term. -/
theorem partial_tail_arithmetic {cap : ℚ} (hc : 0 ≤ cap) {j : ℕ} (hj : 2 ≤ j) :
    (patersonDelta0 + refinementTailError) *
      (fastParams.mu * fastParams.delta ^ (j - 2) * (cap / fastParams.A)) ≤
      fastParams.mu * fastParams.delta ^ (j - 1) * (fastParams.nu * cap) := by
  have hnonneg : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 2) * (cap / fastParams.A) :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (div_nonneg hc (by linarith [fastParams.A_gt_one]))
  have h := mul_le_mul_of_nonneg_right partial_tail_budget hnonneg
  have hA : fastParams.A ≠ 0 := by norm_num [fastParams]
  rw [show j - 1 = (j - 2) + 1 by omega, pow_succ]
  convert h using 1 <;> field_simp [hA] <;> ring

end Paterson.Bags
