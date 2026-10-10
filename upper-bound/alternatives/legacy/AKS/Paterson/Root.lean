module

public import AKS.Paterson.Transition
public import AKS.Paterson.Schedule
public import AKS.Bitonic.TightDepth

/-! # Early root splitting: purity and exact-sort budgets

To absorb lattice rounding, split a tree while its root capacity is still
large, sorting all occupied registers above level six. The invariant shows
that deeper bags have no wrong-half values. The cardinality certificate below
accounts for root, levels two and four, and cold storage. It does not construct
the subsequent forest placement or prove its invariant.
Source: Paterson (1990), Sections 6 and 7.
-/

@[expose] public section

namespace Paterson.Bags

def rootCeiling : ℚ := fastParams.minCapacity / fastParams.nu ^ 2

theorem root_ceiling_pos : 0 < rootCeiling := by norm_num [rootCeiling, fastParams]

theorem fast_deep_error_lt_one {root : ℚ} (hr : root ≤ rootCeiling)
    (hroot : 0 ≤ root) {l : ℕ} (hl : 6 ≤ l) :
    fastParams.mu * fastParams.delta ^ (l - 1) * (root * fastParams.A ^ l) < 1 := by
  let d := l - 6
  have hl' : l = 6 + d := by dsimp [d]; omega
  have heq : fastParams.mu * fastParams.delta ^ (l - 1) * (root * fastParams.A ^ l) =
      (fastParams.mu * fastParams.delta ^ 5 * (root * fastParams.A ^ 6)) *
        (fastParams.delta * fastParams.A) ^ d := by
    rw [hl', show 6 + d - 1 = 5 + d by omega, pow_add, pow_add, mul_pow]
    ring
  have hratio : 0 ≤ fastParams.delta * fastParams.A ∧
      fastParams.delta * fastParams.A ≤ 1 := by norm_num [fastParams]
  have hpow : (fastParams.delta * fastParams.A) ^ d ≤ 1 :=
    pow_le_one₀ hratio.1 hratio.2
  have hnn : 0 ≤ fastParams.mu * fastParams.delta ^ 5 * (root * fastParams.A ^ 6) := by
    exact mul_nonneg (mul_nonneg fastParams.mu_pos.le
      (pow_nonneg fastParams.delta_pos.le _))
      (mul_nonneg hroot (pow_nonneg (by linarith [fastParams.A_gt_one]) _))
  rw [heq]
  apply (mul_le_of_le_one_right hnn hpow).trans_lt
  norm_num [fastParams, rootCeiling] at hr ⊢
  linarith

/-- The integer stranger count in a deep bag vanishes, so its values cannot
cross the root's two native halves. -/
theorem deep_half_strangers_zero {k : ℕ} {root : ℚ}
    (hr : root ≤ rootCeiling) (hroot : 0 ≤ root)
    (regs : Bag k → Finset (Fin (2 ^ k)))
    (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hinv : Invariant fastParams (fun b ↦ root * fastParams.A ^ b.l) regs w)
    (b : Bag k) (hl : 6 ≤ b.l) : b.strangers b.l w (regs b) = 0 := by
  have h := (hinv b b.l (by omega)).trans_lt (fast_deep_error_lt_one hr hroot hl)
  have hn : b.strangers b.l w (regs b) < 1 := by exact_mod_cast h
  omega

/-- Sum of the occupied upper bag capacities and simulated ancestor storage.
At the rounding threshold this fits the proved 561-round exact sorter. -/
theorem root_region_budget {root cold bag0 level2 level4 : ℚ}
    (hr : root ≤ rootCeiling)
    (hcold : cold ≤ ancestorReserve fastParams root)
    (h0 : bag0 ≤ root + 32)
    (h2 : level2 ≤ 4 * (root * fastParams.A ^ 2 + 32))
    (h4 : level4 ≤ 16 * (root * fastParams.A ^ 4 + 32)) :
    cold + bag0 + level2 + level4 < 2 ^ 33 := by
  norm_num [rootCeiling, fastParams, ancestorReserve] at *
  linarith

/-- Sorting the actual root region respects its depth budget once its
cardinality is obtained from the rounded placement's conservation identities. -/
theorem root_sort_depth_le {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (hsize : regs.card ≤ 2 ^ 33) :
    ((bitonicNetwork regs.card).scatterEmbed (2 ^ k) (regs.orderEmbOfFin rfl)).depth ≤ 561 :=
  (depth_scatterEmbed_le _ _ _).trans (bitonicNetwork_depth_le_561 hsize)

end Paterson.Bags
