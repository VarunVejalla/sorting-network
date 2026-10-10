module

public import AKS.Paterson.AllocatedPartialBalance
public import AKS.Paterson.StoredFirstSource
public import AKS.Paterson.AllocatedFullTransition

/-! # Selecting full and partial networks on actual allocated bags

Only size and stage determine the choice. No input ranks enter this schedule.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem cast_network_depth {n m : ℕ} (h : n = m) (net : ComparatorNetwork n) :
    (h ▸ net).depth = net.depth := by cases h; rfl

theorem cast_separatorNetwork {n m : ℕ} (h : n = m) :
    (h ▸ separatorNetwork n) = separatorNetwork m := by cases h; rfl

theorem firstContract_cast {n m : ℕ} (h : n = m) (net : ComparatorNetwork n)
    (hg : FirstContract net) : FirstContract (h ▸ net) := by cases h; exact hg

theorem firstContract_of_even {m : ℕ} (net : ComparatorNetwork (2 * m))
    (hg : IsEpsilonAlphaHalver net patersonDelta0 patersonAlpha0) : FirstContract net := by
  intro q hq
  have hm : m = q := by omega
  subst q
  simpa using hg

theorem allocated_even {root : ℚ} {k t : ℕ} (pl : StoredPlacement k)
    (ha : AllocationInvariant root t pl) (b : Bag k) : 2 ∣ (pl.regs b).card := by
  rw [ha.1 b]
  exact dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)

theorem allocated_partial_fits {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hf : nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) ≤ 0) :
    (pl.regs b).card / 2 ≤ ceil32 (capacity fastParams root t b.l / 2) := by
  by_cases hp : (t + b.l) % 2 = 0
  · rw [ha.1 b, bagTarget_eq_scheduledBag _ _ _ _ hp]
    exact partial_half_fits (capacity_nonneg fastParams hr t b.l) hf
  · rw [allocated_inactive_empty pl ha b hp, card_empty]
    exact Nat.zero_le _

noncomputable def scheduledLocalNetwork {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k) :
    ComparatorNetwork (pl.regs b).card :=
  if hf : 0 ≤ nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) then
    separatorNetwork (pl.regs b).card
  else
    (Nat.mul_div_cancel' (allocated_even pl ha b)) ▸
      partialNetwork (ceil32 (capacity fastParams root t b.l / 2)) ((pl.regs b).card / 2)
        (allocated_partial_fits hr pl ha b (le_of_lt (lt_of_not_ge hf)))

theorem scheduledLocalNetwork_depth_le {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k) :
    (scheduledLocalNetwork hr pl ha b).depth ≤ 989 := by
  unfold scheduledLocalNetwork
  split_ifs
  · exact separatorNetwork_depth_le _
  · rw [cast_network_depth]
    exact partialNetwork_depth_le _ _ _

theorem scheduledLocalNetwork_firstContract {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k) :
    FirstContract (scheduledLocalNetwork hr pl ha b) := by
  unfold scheduledLocalNetwork
  split_ifs
  · intro m hm
    rw [cast_separatorNetwork]
    exact separatorNetwork_good m
  · apply firstContract_cast
    exact firstContract_of_even _ (partialNetwork_good _ _ _)

noncomputable def scheduledCompare {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) : ComparatorNetwork (2 ^ k) :=
  pl.compare (scheduledLocalNetwork hr pl ha)

theorem scheduledCompare_depth_le {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    (scheduledCompare hr pl ha).depth ≤ 989 :=
  pl.compare_depth_le _ 989 (scheduledLocalNetwork_depth_le hr pl ha)

end Paterson.Bags
