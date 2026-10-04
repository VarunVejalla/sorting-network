module

public import AKS.Paterson.DescendantRegisters

/-! # Cold storage is forced by the actual bag cardinalities -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem leaf_card_of_bag_cards {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (hs : ∀ b, (pl.regs b).card = bagTarget root k t b.l)
    (b : Bag k) (hb : ¬ b.l < k) : (pl.regs b).card = 0 := by
  have hz := subtreeTotal_zero_of_deep (t := t) (show k ≤ b.l by omega)
    (hc.trans (root_capacity_le_level hr t b.l))
  rw [hs b]
  simp only [bagTarget, hz, Nat.zero_sub]
  split_ifs <;> rfl

theorem subtree_card_of_bag_cards {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (hs : ∀ b, (pl.regs b).card = bagTarget root k t b.l)
    (b : Bag k) (hb : 1 ≤ b.l) :
    (subregs pl.collapse b).card = subtreeContent root k t b.l := by
  by_cases hk : b.l < k
  · rw [subregs_card_split' pl.collapse b hk, pl.collapse_regs_of_pos b hb, hs b,
      subtree_card_of_bag_cards hr hc pl hs (b.left hk) (by change 1 ≤ b.l + 1; omega),
      subtree_card_of_bag_cards hr hc pl hs (b.right hk) (by change 1 ≤ b.l + 1; omega)]
    simp only [Bag.left, Bag.right]
    by_cases hp : (t + b.l) % 2 = 0
    · have hchild : (t + (b.l + 1)) % 2 ≠ 0 := by omega
      obtain ⟨hsmall, hlarge⟩ := subtreeTotal_nesting (k := k)
        (hc.trans (root_capacity_le_level hr t b.l))
      simp only [bagTarget, subtreeContent, if_pos hp, if_neg hchild]
      have heq : b.l + 1 + 1 = b.l + 2 := by omega
      rw [heq]
      omega
    · have hchild : (t + (b.l + 1)) % 2 = 0 := by omega
      simp only [bagTarget, subtreeContent, if_neg hp, if_pos hchild]
      omega
  · rw [subregs, dif_neg hk, pl.collapse_regs_of_pos b hb,
      leaf_card_of_bag_cards hr hc pl hs b hk]
    have hz := subtreeTotal_zero_of_deep (show k ≤ b.l by omega)
      (hc.trans (root_capacity_le_level hr t b.l))
    have hz' := subtreeTotal_zero_of_deep (show k ≤ b.l + 1 by omega)
      (hc.trans (root_capacity_le_level hr t (b.l + 1)))
    simp only [subtreeContent, hz, hz', Nat.mul_zero]
    split_ifs <;> rfl
termination_by k - b.l
decreasing_by all_goals simp only [Bag.left, Bag.right]; omega

theorem subregs_root_univ {k : ℕ} (pl : Placement k) : subregs pl (Bag.root k) = univ := by
  apply eq_univ_of_forall
  intro i
  obtain ⟨b, hi⟩ := pl.complete i
  apply mem_subregs_of_desc pl (Bag.root k) b (by change 0 ≤ b.l; omega) _ hi
  change b.x / 2 ^ (b.l - 0) = 0
  rw [Nat.sub_zero, Nat.div_eq_of_lt b.hx]

theorem allocationInvariant_of_bag_cards {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hk : 1 ≤ k) (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (hs : ∀ b, (pl.regs b).card = bagTarget root k t b.l) :
    AllocationInvariant root t pl := by
  refine ⟨hs, ?_⟩
  have htotal := congrArg card (subregs_root_univ pl.collapse)
  have hk0 : (Bag.root k).l < k := hk
  have hroot : pl.collapse.regs (Bag.root k) = pl.regs (Bag.root k) ∪ pl.cold := by
    simp only [StoredPlacement.collapse, if_true]
  rw [subregs_card_split' pl.collapse (Bag.root k) hk0, hroot,
    card_union_of_disjoint (pl.cold_disjoint (Bag.root k)).symm, hs (Bag.root k),
    subtree_card_of_bag_cards hr hc pl hs ((Bag.root k).left hk0) (by change 1 ≤ 0 + 1; omega),
    subtree_card_of_bag_cards hr hc pl hs ((Bag.root k).right hk0) (by change 1 ≤ 0 + 1; omega),
    card_univ, Fintype.card_fin] at htotal
  change bagTarget root k t 0 + pl.cold.card + subtreeContent root k t 1 +
    subtreeContent root k t 1 = 2 ^ k at htotal
  by_cases hp : t % 2 = 0
  · have hchild : (t + 1) % 2 ≠ 0 := by omega
    have hnest := subtreeTotal_grand_le (k := k) hc
    simp only [bagTarget, subtreeContent, coldTarget, Nat.add_zero, if_pos hp,
      if_neg hchild] at htotal ⊢
    norm_num only at htotal hnest ⊢
    omega
  · have hchild : (t + 1) % 2 = 0 := by omega
    simp only [bagTarget, subtreeContent, coldTarget, Nat.add_zero, if_neg hp,
      if_pos hchild] at htotal ⊢
    omega

end Paterson.Bags
