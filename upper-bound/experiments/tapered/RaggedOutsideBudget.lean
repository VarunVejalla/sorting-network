import TaperedSubtreeMass
import RaggedRankRecurrence

namespace Tapered945

open Chvatal

/-- The actual strict ancestors' registers are disjoint from strict
descendant storage. -/
theorem ragged_ancestor_registers_disjoint_strict_subtree {d : Nat}
    (pl : Placement 64 d) (q : KBag 64 d) :
    Disjoint ((raggedAncestorBags d q).biUnion pl.regs)
      ((strictSubtreeBags d q).biUnion pl.regs) := by
  apply Finset.disjoint_left.mpr
  intro k hkA hkS
  obtain ⟨a, ha, hak⟩ := Finset.mem_biUnion.mp hkA
  obtain ⟨s, hs, hsk⟩ := Finset.mem_biUnion.mp hkS
  have hal : a.l < q.l := (Finset.mem_filter.mp ha).2.1
  have hsq : q.l ≤ s.l := subtreeBags_l_ge (by norm_num) q s
    (Finset.mem_filter.mp hs).1
  have hneq : a ≠ s := by
    intro heq
    have := congrArg KBag.l heq
    omega
  exact (Finset.disjoint_left.mp (pl.disjoint a s hneq)) hak hsk

/-- The strict ancestors' aggregate native-prefix mass is bounded by the
strict-descendant subtree defect plus its order-two-and-higher spill. The
identity and budget are left explicit for the integer scheduler to provide. -/
theorem ragged_ancestor_native_prefix_mass_upper {d t : Nat}
    (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (q : KBag 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t (raggedPlacement P nets v t) perm)
    (I : Finset (Fin (64 ^ d))) (hI : I ⊆ nativeKeys q)
    (D B : Nat)
    (hMass : (nativeWireKeys q perm).card = D +
      ((strictSubtreeBags d q).biUnion (raggedPlacement P nets v t).regs).card)
    (hBudget : (∑ z ∈ strictSubtreeBags d q,
      mu * delta ^ (z.l - q.l) * candidateReferenceCapacity d z.l t) ≤ B) :
    ((((raggedAncestorBags d q).biUnion
      (raggedPlacement P nets v t).regs).image perm ∩ I).card ≤ D + B) := by
  let pl := raggedPlacement P nets v t
  let A := (raggedAncestorBags d q).biUnion pl.regs
  have hlocal := ambient_set_native_bound_of_strict_subtree_mass
    pl perm hP q A D B (ragged_ancestor_registers_disjoint_strict_subtree pl q)
    hMass hBudget
  let pre := A.filter (fun x => perm x ∈ I)
  have himage : pre.image perm = A.image perm ∩ I := by
    ext k
    constructor
    · intro hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      change x ∈ A.filter (fun x => perm x ∈ I) at hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, hx.2⟩
    · intro hk
      change k ∈ A.image perm ∩ I at hk
      rcases Finset.mem_inter.mp hk with ⟨himg, hxI⟩
      obtain ⟨x, hxA, hxk⟩ := Finset.mem_image.mp himg
      subst k
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      change x ∈ A.filter (fun x => perm x ∈ I)
      exact Finset.mem_filter.mpr ⟨hxA, hxI⟩
  have hpre : pre ⊆ A ∩ nativeWireKeys q perm := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_inter.mpr
    refine ⟨hx'.1, ?_⟩
    have hnativeKey : perm x ∈ nativeKeys q := hI hx'.2
    have hnative : q.Native (perm x) id := (Finset.mem_filter.mp hnativeKey).2
    have hnative' : q.Native x perm := by
      simpa [KBag.Native] using hnative
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnative'⟩
  rw [← himage]
  rw [Finset.card_image_of_injective _ hperm]
  exact (Finset.card_le_card hpre).trans hlocal

end Tapered945
