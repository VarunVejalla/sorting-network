module

public import AKS.Paterson.FastParams

/-! # Exact integer accounting for the proposed forest budget

This module isolates arithmetic for the shrinking schedule. The actual
forest depth and full sorting theorem are checked in `PatersonForestDepth`
and `PatersonForestSorts`; the final correction adds coefficient one.
-/

@[expose] public section

namespace Paterson.Bags

def idealStageCount (k : ℕ) : ℕ := 13 * ((k + 1) / 2)

theorem idealStageCount_le (k : ℕ) : 2 * idealStageCount k ≤ 13 * (k + 1) := by
  unfold idealStageCount
  omega

/-- The full initial growth through k levels is squeezed below one by the
ideal number of stages, without rounding 6.5 up to seven. -/
theorem idealStageCount_converges (k : ℕ) :
    (2 * fastParams.A) ^ k * fastParams.nu ^ idealStageCount k ≤ 1 := by
  let q := (k + 1) / 2
  have hk : k ≤ 2 * q := by dsimp [q]; omega
  have hgrowth : (2 * fastParams.A) ^ k ≤ (2 * fastParams.A) ^ (2 * q) :=
    pow_le_pow_right₀ (by norm_num [fastParams]) hk
  calc (2 * fastParams.A) ^ k * fastParams.nu ^ idealStageCount k
      ≤ (2 * fastParams.A) ^ (2 * q) * fastParams.nu ^ (13 * q) :=
        mul_le_mul_of_nonneg_right hgrowth (pow_nonneg fastParams.nu_pos.le _)
    _ = ((2 * fastParams.A) ^ 2 * fastParams.nu ^ 13) ^ q := by
      simp only [pow_mul, mul_pow]
    _ ≤ 1 := pow_le_one₀
      (mul_nonneg (pow_nonneg (by linarith [fastParams.A_gt_one]) _)
        (pow_nonneg fastParams.nu_pos.le _)) fastParams_shrink_certificate.le

/-- 989 per ideal stage and 561 per root level leave asymptotic coefficient
13979/2 = 6989.5. An actual scheduler must justify these two counts. -/
theorem proposed_depth_budget (k : ℕ) :
    2 * (989 * idealStageCount k + 561 * k) ≤ 13979 * k + 12857 := by
  have h := idealStageCount_le k
  omega

/-- The constant startup allowance fits below 7000*k from k = 613 onward,
if the construction's total cost is no larger than the proposed budget. -/
theorem proposed_depth_le_7000 {k : ℕ} (hk : 613 ≤ k) :
    989 * idealStageCount k + 561 * k ≤ 7000 * k := by
  have h := proposed_depth_budget k
  omega

end Paterson.Bags
