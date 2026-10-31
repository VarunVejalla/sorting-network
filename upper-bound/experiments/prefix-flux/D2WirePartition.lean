import D2StaticAddressPartition

open Finset

namespace Chvatal.D2WirePartition

/-- If the current bags partition all wires, and each bag is split into
pairwise-disjoint pieces that are assigned to next-stage bags, then the
next-stage bags also partition all wires. The hypotheses separate the purely
combinatorial routing invariant from the D2 schedule and comparator proofs. -/
theorem routed_bags_partition
    {α I J : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (source : I → Finset α) (piece : I → J → Finset α)
    (hsource_cover : Finset.univ.biUnion source = Finset.univ)
    (hsource_disjoint : ∀ i i', i ≠ i' → Disjoint (source i) (source i'))
    (hpiece_subset : ∀ i j, piece i j ⊆ source i)
    (hpiece_cover : ∀ i, Finset.univ.biUnion (piece i) = source i)
    (hpiece_disjoint : ∀ i j j', j ≠ j' → Disjoint (piece i j) (piece i j')) :
    (∀ j j', j ≠ j' →
      Disjoint (Finset.univ.biUnion (fun i => piece i j))
        (Finset.univ.biUnion (fun i => piece i j'))) ∧
      Finset.univ.biUnion (fun j => Finset.univ.biUnion (fun i => piece i j)) =
        Finset.univ := by
  constructor
  · intro j j' hj
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hxi⟩
    rcases Finset.mem_biUnion.mp hx' with ⟨i', _, hxi'⟩
    have hsi : x ∈ source i := hpiece_subset i j hxi
    have hsi' : x ∈ source i' := hpiece_subset i' j' hxi'
    by_cases heq : i = i'
    · subst i'
      exact (Finset.disjoint_left.mp (hpiece_disjoint i j j' hj)) hxi hxi'
    · exact (Finset.disjoint_left.mp (hsource_disjoint i i' heq)) hsi hsi'
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, ⟨i, hxi⟩⟩
      trivial
    · intro _
      have hxsource : x ∈ Finset.univ.biUnion source := by
        rw [hsource_cover]
        simp
      rcases Finset.mem_biUnion.mp hxsource with ⟨i, _, hxi⟩
      have hxpieces : x ∈ Finset.univ.biUnion (piece i) := by
        rw [hpiece_cover i]
        exact hxi
      rcases Finset.mem_biUnion.mp hxpieces with ⟨j, _, hxij⟩
      exact ⟨j, ⟨i, hxij⟩⟩

end Chvatal.D2WirePartition
