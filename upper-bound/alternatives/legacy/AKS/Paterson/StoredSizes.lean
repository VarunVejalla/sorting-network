module

public import AKS.Paterson.StoredRouting

/-! # Exact cardinalities of storage-aware register reassignment -/

@[expose] public section

namespace Paterson.Bags.StoredPlacement

open Finset

theorem route_bag_card {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k)))
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b)
    (b : Bag k) (hb : 1 ≤ b.l) :
    ((pl.route f feed).regs b).card =
      (if h : b.l < k then
        splitParentCard (pl.regs (b.left h)).card (f (b.left h)) +
        splitParentCard (pl.regs (b.right h)).card (f (b.right h)) else 0) +
      splitChildCard (pl.regs b.parent).card (f b.parent) := by
  rw [pl.route_regs_of_pos f feed hleaf b hb]
  let parts := fun c ↦ split (pl.regs c) (f c)
  have sub_p : ∀ c, (parts c).toParent ⊆ pl.regs c := fun _ ↦ split_toParent_subset _ _
  have sub_l : ∀ c, (parts c).toLeft ⊆ pl.regs c := fun _ ↦ split_toLeft_subset _ _
  have sub_r : ∀ c, (parts c).toRight ⊆ pl.regs c := fun _ ↦ split_toRight_subset _ _
  change (stageRegs parts b).card = _
  simp only [stageRegs, if_neg (show b.l ≠ 0 by omega)]
  by_cases hk : b.l < k
  · rw [dif_pos hk, dif_pos hk]
    have dlr : Disjoint (parts (b.left hk)).toParent (parts (b.right hk)).toParent :=
      Disjoint.mono (sub_p _) (sub_p _)
        (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.right]))
    by_cases he : b.x % 2 = 0
    · rw [if_pos he]
      have dcp : Disjoint ((parts (b.left hk)).toParent ∪ (parts (b.right hk)).toParent)
          (parts b.parent).toLeft := disjoint_union_left.mpr
        ⟨Disjoint.mono (sub_p _) (sub_l _)
          (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.parent]; omega)),
         Disjoint.mono (sub_p _) (sub_l _)
          (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.right, Bag.parent]; omega))⟩
      rw [card_union_of_disjoint dcp, card_union_of_disjoint dlr]
      simp only [parts, split_toParent_card, split_toLeft_card]
    · rw [if_neg he]
      have dcp : Disjoint ((parts (b.left hk)).toParent ∪ (parts (b.right hk)).toParent)
          (parts b.parent).toRight := disjoint_union_left.mpr
        ⟨Disjoint.mono (sub_p _) (sub_r _)
          (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.parent]; omega)),
         Disjoint.mono (sub_p _) (sub_r _)
          (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.right, Bag.parent]; omega))⟩
      rw [card_union_of_disjoint dcp, card_union_of_disjoint dlr]
      simp only [parts, split_toParent_card, split_toRight_card]
  · rw [dif_neg hk, dif_neg hk, empty_union, Nat.zero_add]
    split_ifs <;> simp only [parts, split_toLeft_card, split_toRight_card]

theorem route_root_card {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (hfeed : feed ⊆ pl.cold)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b)
    (hk : 0 < k) :
    ((pl.route f feed).regs (Bag.root k)).card = feed.card +
      (splitParentCard (pl.regs ((Bag.root k).left hk)).card (f ((Bag.root k).left hk)) +
        splitParentCard (pl.regs ((Bag.root k).right hk)).card (f ((Bag.root k).right hk))) := by
  rw [pl.route_root_regs f feed hfeed hleaf, dif_pos hk]
  have dlr : Disjoint
      (split (pl.regs ((Bag.root k).left hk)) (f ((Bag.root k).left hk))).toParent
      (split (pl.regs ((Bag.root k).right hk)) (f ((Bag.root k).right hk))).toParent :=
    Disjoint.mono (split_toParent_subset _ _) (split_toParent_subset _ _)
      (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.right]))
  have df : Disjoint feed
      ((split (pl.regs ((Bag.root k).left hk)) (f ((Bag.root k).left hk))).toParent ∪
        (split (pl.regs ((Bag.root k).right hk)) (f ((Bag.root k).right hk))).toParent) :=
    disjoint_union_right.mpr
      ⟨(pl.cold_disjoint _).mono hfeed (split_toParent_subset _ _),
       (pl.cold_disjoint _).mono hfeed (split_toParent_subset _ _)⟩
  rw [card_union_of_disjoint df, card_union_of_disjoint dlr,
    split_toParent_card, split_toParent_card]

end Paterson.Bags.StoredPlacement
