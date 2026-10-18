import AdaptivePaddedWitness
import RaggedStageSlotBridge

namespace Tapered945

open Chvatal

/-- A selected physical down-port after a ragged stage is exactly the local
separator output slot. Consequently an input rank-window estimate can be
charged directly to the actual parent contribution routed to the child. -/
theorem adaptive_ragged_parent_slot_wrong_le {d : Nat}
    (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d)
    (w : AdaptivePaddedWitness ((P t).sets b).card)
    (split : RaggedWireSplit ((P t).sets b)) (j : Fin 64)
    (xr : Fin ((P t).sets b).card → Fin (64 ^ d)) (hxr : Function.Injective xr)
    (hxrEq : xr = fun i => raggedX P nets v t
      (((P t).sets b).orderEmbOfFin rfl i))
    (hnet : nets t b ((P t).sets b).card = w.network)
    (L H lo hi : Nat)
    (hL : L = slotLo split.up split.widths j.val)
    (hH : H = slotHi split.up split.widths j.val)
    (hLa : L ≤ ((P t).sets b).card)
    (hHa : H ≤ ((P t).sets b).card) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      L ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ < H ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A) :
    (((((raggedDownSet ((P t).sets b) split.up split.widths j.val).image
      (raggedX P nets v (t + 1))).image Fin.val).filter
      (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤
      A + 2 * (((1 / 2^21 : Real) / 2) *
        ((w.retainedRows + 1) * w.columns) + w.columns) := by
  rw [ragged_stage_downslot_keys_eq_local_outputs P nets v t b split j]
  have hxr' : Function.Injective (fun i =>
      raggedX P nets v t (((P t).sets b).orderEmbOfFin rfl i)) := by
    simpa [← hxrEq] using hxr
  let xr' := fun i : Fin ((P t).sets b).card =>
    raggedX P nets v t (((P t).sets b).orderEmbOfFin rfl i)
  have hA' := hA
  rw [hxrEq] at hA'
  have hA'' : ((((keySet xr').image Fin.val).filter (fun κ =>
      L ≤ BW.rankN ((keySet xr').image Fin.val) κ ∧
      BW.rankN ((keySet xr').image Fin.val) κ < H ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A := by
    simpa [xr'] using hA'
  rw [hnet]
  simpa [xr', hL, hH, Finset.image_image] using
    w.output_slot_wrong_le xr' hxr' L H lo hi hLa hHa A hA''

end Tapered945
