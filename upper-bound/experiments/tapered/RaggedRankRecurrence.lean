import RaggedExecution
import FrontierRankCounting
import RaggedSlotMass
import OutsiderOutsideMass
import AKS.Chvatal.Lemma41Real
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Strict descendants of an address, with the current address removed. -/
def strictSubtreeBags (d : Nat) (w : KBag 64 d) : Finset (KBag 64 d) :=
  (subtreeBags 64 d (by norm_num) w).filter (fun z => z.l ≠ w.l)

/-- Wires currently stored strictly below `w` in an address-dependent
ragged placement. -/
noncomputable def raggedStrictSubtreeKeys {d : Nat}
    (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    Finset (Fin (64 ^ d)) :=
  (strictSubtreeBags d w).biUnion (raggedPlacement P nets v t).regs

/-- All wires outside the current register and its strict descendant storage. -/
noncomputable def raggedOutsideSubtreeKeys {d : Nat}
    (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    Finset (Fin (64 ^ d)) :=
  Finset.univ \ ((raggedPlacement P nets v t).regs w ∪
    raggedStrictSubtreeKeys P nets v t w)

/-- The actual outside storage is covered by registers of bags other than the
current bag and its strict descendants. This is the exact ownership cover
needed before splitting outside storage into incomparable sibling registers
and ancestor/frontier registers. -/
def raggedOutsideBags (d : Nat) (w : KBag 64 d) : Finset (KBag 64 d) :=
  Finset.univ.filter (fun b => b ≠ w ∧ b ∉ strictSubtreeBags d w)

/-- Tree-theoretic classification of an outside bag. A shallower bag is
either the actual ancestor containing `w`, or it separates from `w` at their
common level. A deeper bag outside the strict subtree must separate there. -/
theorem outside_bag_ancestor_or_separated {d : Nat} (w b : KBag 64 d)
    (hb : b ∈ raggedOutsideBags d w) :
    (b.l < w.l ∧ b = w.ancestor (w.l - b.l)) ∨
      b.ancestor (outsiderSeparationRank w b) ≠
        w.ancestor (w.l - min w.l b.l) := by
  have hout := (Finset.mem_filter.mp hb).2
  have hb0 : b.ancestor 0 = b := by
    apply KBag.ext <;> simp [KBag.ancestor]
  have hw0 : w.ancestor 0 = w := by
    apply KBag.ext <;> simp [KBag.ancestor]
  by_cases hlevel : b.l < w.l
  · by_cases heq : b = w.ancestor (w.l - b.l)
    · exact Or.inl ⟨hlevel, heq⟩
    · right
      simp only [outsiderSeparationRank]
      rw [Nat.min_eq_right (Nat.le_of_lt hlevel), show b.l - b.l = 0 by omega, hb0]
      exact heq
  · right
    have hle : w.l ≤ b.l := by omega
    have hdepth : b.l - w.l ≤ d - w.l := Nat.sub_le_sub_right b.hl w.l
    have hsep : b.ancestor (b.l - w.l) ≠ w := by
      intro heq
      have hpos : 0 < b.l - w.l := by
        by_contra hn
        have hz : b.l - w.l = 0 := by omega
        apply hout.1
        apply KBag.ext
        · have hl := congrArg KBag.l heq
          simp [KBag.ancestor, hz] at hl
          omega
        · have hx := congrArg KBag.x heq
          simpa [KBag.ancestor, hz] using hx
      have hdesc : b ∈ descendants 64 d (by norm_num) w (b.l - w.l) := by
        rw [mem_descendants]
        constructor
        · omega
        · have hx := congrArg KBag.x heq
          simpa [KBag.ancestor] using hx
      have hsub : b ∈ subtreeBags 64 d (by norm_num) w := by
        unfold subtreeBags
        apply Finset.mem_biUnion.mpr
        exact ⟨b.l - w.l, Finset.mem_range.mpr (by omega), hdesc⟩
      exact hout.2 (Finset.mem_filter.mpr ⟨hsub, by omega⟩)
    simp only [outsiderSeparationRank]
    rw [Nat.min_eq_left hle, show w.l - w.l = 0 by omega, hw0]
    exact hsep

/-- Outside bags which are actual strict ancestors of the selected node. -/
def raggedAncestorBags (d : Nat) (w : KBag 64 d) : Finset (KBag 64 d) :=
  (raggedOutsideBags d w).filter
    (fun b => b.l < w.l ∧ b = w.ancestor (w.l - b.l))

/-- Outside bags whose native intervals separate from the selected node at a
common ancestor level. These are exactly the bags eligible for the tapered
stranger-order charge. -/
def raggedSeparatedOutsideBags (d : Nat) (w : KBag 64 d) : Finset (KBag 64 d) :=
  (raggedOutsideBags d w).filter
    (fun b => ¬(b.l < w.l ∧ b = w.ancestor (w.l - b.l)))

theorem raggedOutsideBags_eq_ancestor_union_separated {d : Nat}
    (w : KBag 64 d) :
    raggedOutsideBags d w = raggedAncestorBags d w ∪
      raggedSeparatedOutsideBags d w := by
  ext b
  simp only [raggedAncestorBags, raggedSeparatedOutsideBags,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem raggedSeparatedOutsideBags_separation {d : Nat} (w b : KBag 64 d)
    (hb : b ∈ raggedSeparatedOutsideBags d w) :
    b.ancestor (outsiderSeparationRank w b) ≠
      w.ancestor (w.l - min w.l b.l) := by
  have hclass := outside_bag_ancestor_or_separated w b
    (Finset.mem_filter.mp hb).1
  rcases hclass with hanc | hsep
  · exact False.elim ((Finset.mem_filter.mp hb).2 hanc)
  · exact hsep

theorem raggedOutsideSubtreeKeys_subset_outside_bag_cover
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    raggedOutsideSubtreeKeys P nets v t w ⊆
      (raggedOutsideBags d w).biUnion (raggedPlacement P nets v t).regs := by
  intro k hk
  have hknot := (Finset.mem_sdiff.mp hk).2
  obtain ⟨b, hbk⟩ := (raggedPlacement P nets v t).complete k
  have hbne : b ≠ w := by
    intro heq
    subst b
    exact hknot (Finset.mem_union_left _ hbk)
  have hbnot : b ∉ strictSubtreeBags d w := by
    intro hb
    have hmem : k ∈ raggedStrictSubtreeKeys P nets v t w := by
      unfold raggedStrictSubtreeKeys
      exact Finset.mem_biUnion.mpr ⟨b, hb, hbk⟩
    exact hknot (Finset.mem_union_right _ hmem)
  exact Finset.mem_biUnion.mpr ⟨b,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbne, hbnot⟩, hbk⟩

/-- Conversely, an outside bag's register cannot overlap the current register
or any strict descendant register, by placement disjointness. Hence the cover
above is an equality, giving a canonical, schedule-indexed partition of the
O-side by bag address. -/
theorem raggedOutside_bag_cover_subset_outsideSubtreeKeys
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    (raggedOutsideBags d w).biUnion (raggedPlacement P nets v t).regs ⊆
      raggedOutsideSubtreeKeys P nets v t w := by
  intro k hk
  obtain ⟨b, hb, hbk⟩ := Finset.mem_biUnion.mp hk
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hinside
  rcases Finset.mem_union.mp hinside with hcurrent | hdesc
  · have hne := (raggedPlacement P nets v t).disjoint b w
      ((Finset.mem_filter.mp hb).2.1)
    exact (Finset.disjoint_left.mp hne) hbk hcurrent
  · unfold raggedStrictSubtreeKeys at hdesc
    obtain ⟨z, hz, hzk⟩ := Finset.mem_biUnion.mp hdesc
    have hne : b ≠ z := by
      intro heq
      subst z
      exact (Finset.mem_filter.mp hb).2.2 hz
    exact (Finset.disjoint_left.mp ((raggedPlacement P nets v t).disjoint b z hne)) hbk hzk

theorem raggedOutsideSubtreeKeys_eq_outside_bag_cover
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    raggedOutsideSubtreeKeys P nets v t w =
      (raggedOutsideBags d w).biUnion (raggedPlacement P nets v t).regs :=
  Finset.Subset.antisymm
    (raggedOutsideSubtreeKeys_subset_outside_bag_cover P nets v t w)
    (raggedOutside_bag_cover_subset_outsideSubtreeKeys P nets v t w)

theorem raggedOutsideSubtreeKeys_subset_ancestor_separated_cover
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d) :
    raggedOutsideSubtreeKeys P nets v t w ⊆
      (raggedAncestorBags d w).biUnion (raggedPlacement P nets v t).regs ∪
        (raggedSeparatedOutsideBags d w).biUnion (raggedPlacement P nets v t).regs := by
  intro k hk
  rw [raggedOutsideSubtreeKeys_eq_outside_bag_cover] at hk
  obtain ⟨b, hb, hbk⟩ := Finset.mem_biUnion.mp hk
  rw [raggedOutsideBags_eq_ancestor_union_separated] at hb
  rcases Finset.mem_union.mp hb with ha | hs
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, ha, hbk⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hs, hbk⟩)

/-- A key interval is an actual global rank prefix slice. -/
def keyInterval (lo hi : Nat) : Finset (Fin (64 ^ d)) :=
  Finset.univ.filter (fun k => lo ≤ k.val ∧ k.val < hi)

theorem keyInterval_card {d lo hi : Nat} (hlo : lo ≤ hi)
    (hhi : hi ≤ 64 ^ d) : (keyInterval (d := d) lo hi).card = hi - lo := by
  classical
  let I := keyInterval (d := d) lo hi
  calc
    I.card = (Finset.Ico lo hi).card := by
      apply Finset.card_bij (fun k _ => k.val)
      · intro k hk
        exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hk).2
      · intro k hk k' hk' heq
        exact Fin.ext heq
      · intro x hx
        rcases Finset.mem_Ico.mp hx with ⟨hlo', hhi'⟩
        refine ⟨⟨x, lt_of_lt_of_le hhi' hhi⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlo', hhi'⟩⟩, rfl⟩
    _ = hi - lo := by rw [Nat.card_Ico]

/-- Actual ragged placements split every rank cut into the current bag,
strict descendant storage, and the complement (all storage outside that
subtree). Thus the generic three-way counting lemma applies directly to the
global execution. The only nonstructural hypotheses are the desired bounds
`D` on descendant prefix mass and `O` on outside prefix mass. -/
theorem ragged_rank_cut_recurrence
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (w : KBag 64 d)
    (lo hi D O : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ 64 ^ d)
    (hD : D ≤ (raggedStrictSubtreeKeys P nets v t w ∩
      keyInterval (d := d) lo hi).card)
    (hO : (raggedOutsideSubtreeKeys P nets v t w ∩
      keyInterval (d := d) lo hi).card ≤ O) :
    (((raggedPlacement P nets v t).regs w ∩
      keyInterval (d := d) lo hi).card) ≤ hi - lo - D + O := by
  let pl := raggedPlacement P nets v t
  let K := pl.regs w
  let S := raggedStrictSubtreeKeys P nets v t w
  let X := raggedOutsideSubtreeKeys P nets v t w
  let I := keyInterval (d := d) lo hi
  have hKS : Disjoint K S := by
    unfold S raggedStrictSubtreeKeys strictSubtreeBags
    rw [Finset.disjoint_biUnion_right]
    intro z hz
    apply pl.disjoint w z
    intro heq
    have hstrict := (Finset.mem_filter.mp hz).2
    subst z
    exact hstrict rfl
  have hKX : Disjoint K X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxX
    have hxnot := (Finset.mem_sdiff.mp hxX).2
    exact hxnot (Finset.mem_union_left _ hx)
  have hSX : Disjoint S X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxX
    have hxnot := (Finset.mem_sdiff.mp hxX).2
    exact hxnot (Finset.mem_union_right _ hx)
  have hcover : I ⊆ K ∪ S ∪ X := by
    intro x hx
    by_cases hKSx : x ∈ K ∪ S
    · exact Finset.mem_union_left _ hKSx
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, hKSx⟩)
  have hI : I.card = hi - lo := by
    exact keyInterval_card hlo hhi
  have h := prefix_count_le_of_three_way_cover K S X I (hi - lo) D O
    hKS hKX hSX hcover hI (by simpa [S, I] using hD)
    (by simpa [X, I] using hO)
  simpa [K, I] using h

end Tapered945
