module

public import AKS.Paterson.AllocationSchedule

/-! # Preservation of the prescribed integer allocation

This module concerns actual register cardinalities, independently of the
stranger invariant. All rounding is inherited from coherent subtree totals.
-/

@[expose] public section

namespace Paterson.Bags

theorem target_interior_card {root : ℚ} (hr : 0 ≤ root) {k t l : ℕ}
    (hl : 1 ≤ l) (hc : fastParams.minCapacity ≤ capacity fastParams root t 0) :
    2 * splitParentCard (bagTarget root k t (l + 1)) (fringeTarget root k t (l + 1)) +
      splitChildCard (bagTarget root k t (l - 1)) (fringeTarget root k t (l - 1)) =
        bagTarget root k (t + 1) l := by
  have hcap : ∀ i, fastParams.minCapacity ≤ capacity fastParams root t i :=
    fun i ↦ hc.trans (root_capacity_le_level hr t i)
  by_cases hp : (t + 1 + l) % 2 = 0
  · have hparent : (t + (l - 1)) % 2 = 0 := by omega
    have hchild : (t + (l + 1)) % 2 = 0 := by omega
    have hsParent := (target_source_cards (k := k) (hcap (l - 1)) hparent).1
    have hsChild := (target_source_cards (k := k) (hcap (l + 1)) hchild).2
    have hnestParent := (subtreeTotal_nesting (k := k) (hcap (l - 1))).1
    have hnestChild := (subtreeTotal_nesting (k := k) (hcap (l + 1))).2
    rw [show l - 1 + 1 = l by omega, show l - 1 + 2 = l + 1 by omega] at hsParent hnestParent
    rw [show l + 1 + 1 = l + 2 by omega] at hsChild hnestChild
    rw [hsParent, hsChild, bagTarget, if_pos hp]
    omega
  · have hparent : (t + (l - 1)) % 2 ≠ 0 := by omega
    have hchild : (t + (l + 1)) % 2 ≠ 0 := by omega
    simp only [bagTarget, fringeTarget, if_neg hparent, if_neg hchild, if_neg hp,
      splitParentCard_zero_left, splitChildCard_zero_left, Nat.mul_zero, Nat.zero_add]

theorem allocation_leaf_empty {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : ¬ b.l < k) : (pl.regs b).card = 0 := by
  have hl : k ≤ b.l := by omega
  have hz := subtreeTotal_zero_of_deep (t := t) hl (hc.trans (root_capacity_le_level hr t b.l))
  rw [ha.1 b]
  simp only [bagTarget, hz, Nat.zero_sub]
  split_ifs <;> rfl

theorem allocationStep_interior_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : 1 ≤ b.l) (hk : b.l < k) :
    ((allocationStep root t pl).regs b).card = bagTarget root k (t + 1) b.l := by
  have hleaf : ∀ c : Bag k, ¬ c.l < k → (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hcl
    rw [allocation_leaf_empty hr hc pl ha c hcl]
    exact Nat.zero_le _
  rw [allocationStep, StoredPlacement.centralFeedRoute,
    pl.route_bag_card _ _ hleaf b hb, dif_pos hk]
  rw [ha.1 (b.left hk), ha.1 (b.right hk), ha.1 b.parent]
  simp only [Bag.left, Bag.right, Bag.parent]
  have ht := target_interior_card hr (k := k) hb hc
  omega

/-- The root can be refilled from the actual remaining storage, including
when its ideal children are clipped to empty. -/
theorem root_return_nesting {width cap : ℚ}
    (hc : fastParams.minCapacity ≤ cap) :
    2 * scheduledSubtree fastParams (width / 2) (fastParams.A * cap) ≤
      scheduledSubtree fastParams width (fastParams.nu * cap) := by
  let a := width - ancestorReserve fastParams (fastParams.nu * cap)
  let g := width / 2 - ancestorReserve fastParams (fastParams.A * cap)
  have hid : a - 2 * g = (2 * fastParams.A - fastParams.nu) * cap /
      (4 * fastParams.A ^ 2 - 1) := by
    dsimp [a, g, ancestorReserve]
    ring
  change 2 * ceil32 (max 0 g) ≤ ceil32 (max 0 a)
  by_cases hg : 0 ≤ g
  · have ha : 0 ≤ a := by norm_num [fastParams] at hc hid; linarith
    rw [max_eq_right hg, max_eq_right ha]
    have hl := le_ceil32 a
    have hu := ceil32_lt_add hg
    have hQ : (2 : ℚ) * ceil32 g ≤ ceil32 a := by
      norm_num [fastParams] at hc hid
      linarith
    exact_mod_cast hQ
  · rw [max_eq_left (le_of_not_ge hg), ceil32_of_nonpos (le_refl 0), Nat.mul_zero]
    exact Nat.zero_le _

theorem subtreeTotal_return_nesting {root : ℚ} {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0) :
    2 * subtreeTotal root k t 1 ≤ subtreeTotal root k (t + 1) 0 := by
  unfold subtreeTotal
  rw [nativeWidth_succ k 0, capacity_level_succ fastParams root t 0, capacity_stage_succ]
  exact root_return_nesting hc

theorem feedTarget_even (root : ℚ) (k t : ℕ) : 2 ∣ feedTarget root k t := by
  unfold feedTarget
  split_ifs
  · exact dvd_zero _
  · exact Nat.dvd_sub (dvd_trans (by norm_num) (subtreeTotal_dvd _ _ _ _)) (dvd_mul_right _ _)

theorem coldTarget_even (root : ℚ) (k t : ℕ) (hk : 1 ≤ k) : 2 ∣ coldTarget root k t := by
  apply Nat.dvd_sub (dvd_pow_self 2 (by omega))
  split_ifs
  · exact dvd_trans (by norm_num) (subtreeTotal_dvd _ _ _ _)
  · exact dvd_mul_right _ _

theorem feedTarget_fits {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0) :
    feedTarget root k t ≤ coldTarget root k t := by
  by_cases hp : t % 2 = 0
  · simp only [feedTarget, if_pos hp]
    exact Nat.zero_le _
  · have hsmall := subtreeTotal_return_nesting (k := k) hc
    have hwidth := root_total_le hr k (t + 1) hk
    simpa only [feedTarget, coldTarget, if_neg hp] using
      (root_feed_conservation (2 ^ k) _ _ hsmall hwidth).1

theorem allocationStep_leaf_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : 1 ≤ b.l) (hk : ¬ b.l < k) :
    ((allocationStep root t pl).regs b).card = bagTarget root k (t + 1) b.l := by
  have hleaf : ∀ c : Bag k, ¬ c.l < k → (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hcl
    rw [allocation_leaf_empty hr hc pl ha c hcl]
    exact Nat.zero_le _
  rw [allocationStep, StoredPlacement.centralFeedRoute,
    pl.route_bag_card _ _ hleaf b hb, dif_neg hk, Nat.zero_add, ha.1 b.parent]
  simp only [Bag.parent]
  have hz := subtreeTotal_zero_of_deep (t := t) (show k ≤ b.l + 1 by omega)
    (hc.trans (root_capacity_le_level hr t (b.l + 1)))
  have hsz : bagTarget root k t (b.l + 1) = 0 := by
    simp only [bagTarget, hz, Nat.zero_sub]
    split_ifs <;> rfl
  have ht := target_interior_card hr (k := k) hb hc
  rw [hsz, splitParentCard_zero_left, Nat.mul_zero, Nat.zero_add] at ht
  exact ht

theorem allocationStep_root_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    ((allocationStep root t pl).regs (Bag.root k)).card = bagTarget root k (t + 1) 0 := by
  have hk0 : 0 < k := by omega
  have hleaf : ∀ c : Bag k, ¬ c.l < k → (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hcl
    rw [allocation_leaf_empty hr hc pl ha c hcl]
    exact Nat.zero_le _
  have hfit : feedTarget root k t ≤ pl.cold.card := by rw [ha.2]; exact feedTarget_fits hr hk hc
  have heven : 2 ∣ pl.cold.card := by rw [ha.2]; exact coldTarget_even root k t (by omega)
  have hcount := centralFeed_card pl.cold (feedTarget root k t) heven (feedTarget_even _ _ _) hfit
  have hbase := pl.route_root_card (fun b ↦ fringeTarget root k t b.l)
    (centralFeed pl.cold (feedTarget root k t)) (centralFeed_subset _ _) hleaf hk0
  rw [hcount, ha.1 ((Bag.root k).left hk0), ha.1 ((Bag.root k).right hk0)] at hbase
  change ((allocationStep root t pl).regs (Bag.root k)).card =
    feedTarget root k t +
      (splitParentCard (bagTarget root k t 1) (fringeTarget root k t 1) +
        splitParentCard (bagTarget root k t 1) (fringeTarget root k t 1)) at hbase
  by_cases hp : t % 2 = 0
  · have hnext : (t + 1) % 2 ≠ 0 := by omega
    simpa only [bagTarget, fringeTarget, feedTarget, Nat.add_zero, if_pos hp,
      if_neg hnext, splitParentCard_zero_left, Nat.zero_add] using hbase
  · have hnext : (t + 1) % 2 = 0 := by omega
    have hchild : (t + 1) % 2 = 0 := hnext
    have hcapChild := hc.trans (root_capacity_le_level hr t 1)
    have hs := (target_source_cards (k := k) hcapChild hchild).2
    have hn := subtreeTotal_return_nesting (k := k) hc
    have hg := (subtreeTotal_nesting (k := k) hcapChild).2
    rw [hs] at hbase
    simp only [feedTarget, if_neg hp] at hbase
    rw [bagTarget, Nat.add_zero, if_pos hnext]
    norm_num only at hbase hn hg ⊢
    omega

theorem allocationStep_cold_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    (allocationStep root t pl).cold.card = coldTarget root k (t + 1) := by
  have hleaf : ∀ c : Bag k, ¬ c.l < k → (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hcl
    rw [allocation_leaf_empty hr hc pl ha c hcl]
    exact Nat.zero_le _
  have hfit : feedTarget root k t ≤ pl.cold.card := by rw [ha.2]; exact feedTarget_fits hr hk hc
  have heven : 2 ∣ pl.cold.card := by rw [ha.2]; exact coldTarget_even root k t (by omega)
  have hbase := pl.centralFeedRoute_cold_card (fun b ↦ fringeTarget root k t b.l)
    (feedTarget root k t) heven (feedTarget_even _ _ _) hfit hleaf
  rw [ha.2, ha.1 (Bag.root k)] at hbase
  change (allocationStep root t pl).cold.card = coldTarget root k t - feedTarget root k t +
    splitParentCard (bagTarget root k t 0) (fringeTarget root k t 0) at hbase
  by_cases hp : t % 2 = 0
  · have hnext : (t + 1) % 2 ≠ 0 := by omega
    have hs := (target_source_cards (k := k) hc (by simpa only [Nat.add_zero] using hp)).2
    rw [hs] at hbase
    simp only [feedTarget, coldTarget, if_pos hp, Nat.sub_zero] at hbase
    simp only [coldTarget, if_neg hnext]
    have hn := root_total_le hr k t hk
    have hsmall := (subtreeTotal_nesting (k := k) hc).2
    norm_num only at hbase hsmall ⊢
    omega
  · have hnext : (t + 1) % 2 = 0 := by omega
    simp only [feedTarget, coldTarget, bagTarget, fringeTarget, Nat.add_zero, if_neg hp,
      splitParentCard_zero_left, Nat.add_zero] at hbase
    simp only [coldTarget, if_pos hnext]
    have hn := root_total_le hr k (t + 1) hk
    have hs := subtreeTotal_return_nesting (k := k) hc
    omega

/-- Every prescribed bag and storage cardinality is obtained by actual
register routing, including full, partial, empty, and leaf levels. -/
theorem allocationStep_preserves {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    AllocationInvariant root (t + 1) (allocationStep root t pl) := by
  refine ⟨?_, allocationStep_cold_card hr hk hc pl ha⟩
  intro b
  by_cases hb : b.l = 0
  · have heq : b = Bag.root k := by
      apply Bag.ext hb
      have hx := b.hx
      simp only [hb, pow_zero] at hx
      change b.x = 0
      omega
    subst b
    exact allocationStep_root_card hr hk hc pl ha
  · by_cases hlevel : b.l < k
    · exact allocationStep_interior_card hr hc pl ha b (by omega) hlevel
    · exact allocationStep_leaf_card hr hc pl ha b (by omega) hlevel

end Paterson.Bags
