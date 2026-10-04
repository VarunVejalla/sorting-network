module

public import AKS.Paterson.RootSortedBins

/-! # Stranger budgets for the rebuilt upper bags -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem root_rebuild_level4_budget {root : ℚ} (hr : 0 ≤ root) {t L j : ℕ}
    (hL : L ≤ 4) (hj : 1 ≤ j) (hLj : L + j = 5) :
    2 * (64 * fastParams.mu * fastParams.delta ^ (6 - L) *
      capacity fastParams root t 6 / (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2)) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root t 4 := by
  have heq : 6 - L = 2 + (j - 1) := by omega
  have hfactor :
      2 * (64 * fastParams.mu * fastParams.delta ^ (6 - L) *
        capacity fastParams root t 6 / (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2)) =
          (32 / 35 : ℚ) * (fastParams.mu * fastParams.delta ^ (j - 1) *
            capacity fastParams root t 4) := by
    rw [heq, pow_add]
    norm_num [capacity, fastParams]
    ring
  rw [hfactor]
  have hn : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) *
      capacity fastParams root t 4 :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams hr _ _)
  nlinarith

theorem root_rebuild_level2_budget {root : ℚ} (hr : 0 ≤ root) {t L j : ℕ}
    (hL : L ≤ 2) (hj : 1 ≤ j) (hLj : L + j = 3) :
    2 * (64 * fastParams.mu * fastParams.delta ^ (6 - L) *
      capacity fastParams root t 6 / (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2)) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root t 2 := by
  have heq : 6 - L = 4 + (j - 1) := by omega
  have hfactor :
      2 * (64 * fastParams.mu * fastParams.delta ^ (6 - L) *
        capacity fastParams root t 6 / (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2)) =
          (2 / 315 : ℚ) * (fastParams.mu * fastParams.delta ^ (j - 1) *
            capacity fastParams root t 2) := by
    rw [heq, pow_add]
    norm_num [capacity, fastParams]
    ring
  rw [hfactor]
  have hn : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) *
      capacity fastParams root t 2 :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams hr _ _)
  nlinarith

end Paterson.Bags
