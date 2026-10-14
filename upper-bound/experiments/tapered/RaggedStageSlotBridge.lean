import RaggedTreeRoute
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- The keys occupying a parent split's physical down-slot after one actual
ragged stage are precisely the local node-network outputs at the corresponding
input rank positions. This is the execution bridge needed before charging a
slotwise wrong-key estimate to the routed child register. -/
theorem ragged_stage_downslot_keys_eq_local_outputs
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d)
    (split : RaggedWireSplit ((P t).sets b)) (j : Fin 64) :
    (raggedDownSet ((P t).sets b) split.up split.widths j.val).image
        (raggedX P nets v (t + 1)) =
      ((Finset.univ : Finset (Fin ((P t).sets b).card)).filter
        (fun k => slotLo split.up split.widths j.val ≤ k.val ∧
          k.val < slotHi split.up split.widths j.val)).image
        (fun k => (nets t b ((P t).sets b).card).exec
          (fun i => raggedX P nets v t (((P t).sets b).orderEmbOfFin rfl i)) k) := by
  classical
  ext key
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hlo, hhi, rfl⟩ := mem_blockOf_iff.mp hw
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo, hhi⟩, ?_⟩
    rw [raggedX]
    exact (stageNet_exec_inside ((P t).sets)
      ((P t).disjoint) (nets t) (raggedX P nets v t) b k).symm
  · rintro ⟨k, hk, rfl⟩
    have hk' := (Finset.mem_filter.mp hk).2
    refine ⟨((P t).sets b).orderEmbOfFin rfl k,
      mem_blockOf_iff.mpr ⟨k, hk'.1, hk'.2, rfl⟩, ?_⟩
    rw [raggedX]
    exact stageNet_exec_inside ((P t).sets)
      ((P t).disjoint) (nets t) (raggedX P nets v t) b k

/-- The actual post-stage keys from a parent down-slot are all present in the
routed register of the corresponding child. -/
theorem ragged_stage_downslot_keys_subset_child
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (splits : ∀ t b, RaggedWireSplit ((P t).sets b))
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (c : KBag 64 d)
    (hc : 1 ≤ c.l)
    (hstep : P (t + 1) = (P t).route (splits t) raggedTreeDestination) :
    ((raggedDownSet ((P t).sets (c.parent (by norm_num)))
      (splits t (c.parent (by norm_num))).up
      (splits t (c.parent (by norm_num))).widths (c.x % 64)).image
        (raggedX P nets v (t + 1))) ⊆
      ((P (t + 1)).sets c).image (raggedX P nets v (t + 1)) := by
  rw [hstep]
  change _ ⊆ (routeRaggedWires (P t).sets (splits t)
    raggedTreeDestination c).image (raggedX P nets v (t + 1))
  apply Finset.image_mono
  exact raggedTreeRoute_parent_port_subset_all_depth (P t) (splits t) c hc

end Tapered945
