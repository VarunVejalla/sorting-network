module

public import AKS.Paterson.AllocatedSubtree

/-! # Separator size bounds for allocated bags -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem bagTarget_eq_scheduledBag (root : ℚ) (k t l : ℕ)
    (hp : (t + l) % 2 = 0) :
    bagTarget root k t l =
      scheduledBag fastParams (nativeWidth k l) (capacity fastParams root t l) := by
  have hw : nativeWidth k (l + 2) = nativeWidth k l / 4 := by
    rw [show l + 2 = (l + 1) + 1 by omega, nativeWidth_succ, nativeWidth_succ]
    ring
  have hc : capacity fastParams root t (l + 2) =
      fastParams.A ^ 2 * capacity fastParams root t l := by
    rw [show l + 2 = (l + 1) + 1 by omega, capacity_level_succ, capacity_level_succ]
    ring
  simp only [bagTarget, if_pos hp, subtreeTotal, scheduledBag, hw, hc]

theorem allocated_full_half_bounds {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t b.l)
    (hf : 0 ≤ nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l)) :
    capacity fastParams root t b.l / 2 - 64 < ((pl.regs b).card / 2 : ℕ) ∧
      (((pl.regs b).card / 2 : ℕ) : ℚ) < capacity fastParams root t b.l / 2 + 16 := by
  have heven : 2 ∣ (pl.regs b).card := by
    rw [ha.1 b]
    exact dvd_trans (by norm_num) (bagTarget_dvd root k t b.l)
  have hhalf : (2 : ℚ) * ((pl.regs b).card / 2 : ℕ) = (pl.regs b).card := by
    exact_mod_cast Nat.mul_div_cancel' heven
  have hsize := scheduledBag_full_bounds fastParams hf
    (show 128 ≤ capacity fastParams root t b.l by
      have hmin : (128 : ℚ) ≤ fastParams.minCapacity := by norm_num [fastParams]
      exact hmin.trans hc)
  rw [← bagTarget_eq_scheduledBag root k t b.l hp, ← ha.1 b] at hsize
  constructor <;> linarith [hsize.1, hsize.2]

theorem allocated_inactive_empty {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hp : (t + b.l) % 2 ≠ 0) : pl.regs b = ∅ := by
  apply card_eq_zero.mp
  rw [ha.1 b, bagTarget, if_neg hp]

end Paterson.Bags
