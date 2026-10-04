module

public import AKS.Paterson.RootRebuildAllocation

/-! # Capacity and allocation clocks after removing one root level -/

@[expose] public section

namespace Paterson.Bags

def childRoot (root : ℚ) : ℚ := root * fastParams.A / fastParams.nu

theorem childRoot_nonneg {root : ℚ} (hr : 0 ≤ root) : 0 ≤ childRoot root :=
  div_nonneg (mul_nonneg hr (by linarith [fastParams.A_gt_one])) fastParams.nu_pos.le

theorem child_capacity (root : ℚ) (t l : ℕ) :
    capacity fastParams (childRoot root) (t + 1) l = capacity fastParams root t (l + 1) := by
  simp only [capacity, childRoot, pow_succ]
  field_simp [ne_of_gt fastParams.nu_pos]

theorem child_nativeWidth {k : ℕ} (hk : 1 ≤ k) (l : ℕ) :
    nativeWidth (k - 1) l = nativeWidth k (l + 1) := by
  have hp : (2 : ℚ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  simp only [nativeWidth, pow_succ]
  rw [hp]
  field_simp

theorem child_subtreeTotal (root : ℚ) {k : ℕ} (hk : 1 ≤ k) (t l : ℕ) :
    subtreeTotal (childRoot root) (k - 1) (t + 1) l = subtreeTotal root k t (l + 1) := by
  simp only [subtreeTotal, child_capacity, child_nativeWidth hk]

theorem child_bagTarget (root : ℚ) {k : ℕ} (hk : 1 ≤ k) (t l : ℕ) :
    bagTarget (childRoot root) (k - 1) (t + 1) l = bagTarget root k t (l + 1) := by
  simp only [bagTarget, child_subtreeTotal root hk,
    show t + 1 + l = t + (l + 1) by omega,
    show l + 2 + 1 = l + 1 + 2 by omega]

theorem child_coldTarget (root : ℚ) {k t : ℕ} (hk : 1 ≤ k) (hp : t % 2 = 0) :
    coldTarget (childRoot root) (k - 1) (t + 1) =
      2 ^ (k - 1) - 2 * subtreeTotal root k t 2 := by
  simp only [coldTarget, show (t + 1) % 2 ≠ 0 by omega, if_neg,
    child_subtreeTotal root hk, if_false]

end Paterson.Bags
