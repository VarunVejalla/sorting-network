import AKS.Chvatal.StrangerBounds

/-!
Scratch lemma for the direct-multiway transfer audit.

This file lives outside `upper-bound/best`; it generalizes the children-send
union bound without substituting the current geometric outsider invariant.
-/

namespace Chvatal

open Finset

theorem strangers_children_profile_le
    {d : Nat} {t : Nat}
    (pl : Placement 64 d) (b : KBag 64 d) (hbd : b.l < d)
    (j : Nat) (hj : 1 <= j)
    (S : Finset (Fin (64 ^ d)))
    (hS : S ⊆ Finset.univ.biUnion
      (fun i : Fin 64 => pl.regs (b.child i.val i.isLt hbd)))
    (profile : Fin 64 -> Rat)
    (hprofile : forall i : Fin 64,
      ((b.child i.val i.isLt hbd).strangers (j + 1) id
        (pl.regs (b.child i.val i.isLt hbd)) : Rat) <= profile i) :
    (b.strangers j id S : Rat) <= Finset.univ.sum profile := by
  calc
    (b.strangers j id S : Rat)
        <= Finset.univ.sum
          (fun i : Fin 64 =>
            ((b.strangers j id
              (pl.regs (b.child i.val i.isLt hbd)) : Nat) : Rat)) := by
          exact_mod_cast (b.strangers_mono j id hS).trans
            (strangers_biUnion_le d b j id
              (fun i : Fin 64 => pl.regs (b.child i.val i.isLt hbd)))
    _ <= Finset.univ.sum profile := by
          apply Finset.sum_le_sum
          intro i hi
          rw [strangers_child_eq d b hbd j hj i id
            (pl.regs (b.child i.val i.isLt hbd))]
          exact hprofile i

end Chvatal
