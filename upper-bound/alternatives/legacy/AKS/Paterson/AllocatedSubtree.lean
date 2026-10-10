module

public import AKS.Paterson.AllocationInitial

/-! # Actual subtree totals from the rounded allocation invariant -/

@[expose] public section

namespace Paterson.Bags

def subtreeContent (root : ℚ) (k t l : ℕ) : ℕ :=
  if (t + l) % 2 = 0 then subtreeTotal root k t l else 2 * subtreeTotal root k t (l + 1)

theorem allocated_subtree_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : 1 ≤ b.l) :
    (subregs pl.collapse b).card = subtreeContent root k t b.l := by
  by_cases hk : b.l < k
  · rw [subregs_card_split' pl.collapse b hk, pl.collapse_regs_of_pos b hb, ha.1 b,
      allocated_subtree_card hr hc pl ha (b.left hk) (by change 1 ≤ b.l + 1; omega),
      allocated_subtree_card hr hc pl ha (b.right hk) (by change 1 ≤ b.l + 1; omega)]
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
      allocation_leaf_empty hr hc pl ha b hk]
    have hz := subtreeTotal_zero_of_deep (show k ≤ b.l by omega)
      (hc.trans (root_capacity_le_level hr t b.l))
    have hz' := subtreeTotal_zero_of_deep (show k ≤ b.l + 1 by omega)
      (hc.trans (root_capacity_le_level hr t (b.l + 1)))
    simp only [subtreeContent, hz, hz', Nat.mul_zero]
    split_ifs <;> rfl
termination_by k - b.l
decreasing_by all_goals simp only [Bag.left, Bag.right]; omega

/-- The parent size and the sibling's actual subtree total use one coherent
rounded parent total. This is the conservation premise of the cohort proof. -/
theorem allocated_parent_coherence {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.parent.l) % 2 = 0) :
    (pl.regs b.parent).card + 2 * (subregs pl.collapse (b.sibling hb)).card =
      subtreeTotal root k t b.parent.l := by
  rw [ha.1 b.parent, allocated_subtree_card hr hc pl ha (b.sibling hb)
    (by rw [Bag.sibling_level_eq]; exact hb), Bag.sibling_level_eq]
  have hs : (t + b.l) % 2 ≠ 0 := by change (t + (b.l - 1)) % 2 = 0 at hp; omega
  simp only [bagTarget, subtreeContent, if_pos hp, if_neg hs]
  have hlevel : b.parent.l + 2 = b.l + 1 := by change b.l - 1 + 2 = b.l + 1; omega
  rw [hlevel]
  obtain ⟨hsmall, hlarge⟩ := subtreeTotal_nesting (k := k)
    (hc.trans (root_capacity_le_level hr t b.parent.l))
  rw [hlevel] at hsmall
  omega

end Paterson.Bags
