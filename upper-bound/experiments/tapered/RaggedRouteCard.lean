import RaggedExecution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Tapered945

open Chvatal

/-- Each port's cardinality is its specified integer flow. -/
theorem raggedWirePort_card {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (p : Option (Fin 64)) :
    (raggedWirePort split p).card =
      match p with
      | none => split.up
      | some j => split.widths j.val := by
  cases p with
  | none => exact raggedUpSet_card split
  | some j => exact raggedDownSet_card split j.val j.isLt

/-- The cardinality of a routed bag is the sum of the actual source-port
contributions assigned to it. The summands are disjoint because the source
registers partition the wires and every local ragged split partitions its
register. This is the accounting bridge needed to turn a flow table into an
actual variable-width placement. -/
theorem routeRaggedWires_card_eq_port_sum
    {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B)
    (hsource : ∀ b c, b ≠ c → Disjoint (S b) (S c)) (target : B) :
    (routeRaggedWires S splits destination target).card =
      ∑ x ∈ (Finset.univ : Finset (B × Option (Fin 64))).filter
        (fun x => destination x.1 x.2 = target),
          (raggedWirePort (splits x.1) x.2).card := by
  classical
  let I := (Finset.univ : Finset (B × Option (Fin 64))).filter
    (fun x => destination x.1 x.2 = target)
  let port := fun x : B × Option (Fin 64) => raggedWirePort (splits x.1) x.2
  have hroute : routeRaggedWires S splits destination target = I.biUnion port := by
    ext w
    rw [mem_routeRaggedWires]
    simp only [I, port, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, p, hd, hw⟩
      exact ⟨(b, p), hd, hw⟩
    · rintro ⟨⟨b, p⟩, hd, hw⟩
      exact ⟨b, p, hd, hw⟩
  have hdisj : (I : Set (B × Option (Fin 64))).PairwiseDisjoint port := by
    intro x hx y hy hxy
    change Disjoint (raggedWirePort (splits x.1) x.2)
      (raggedWirePort (splits y.1) y.2)
    by_cases hsrc : x.1 = y.1
    · have hport : x.2 ≠ y.2 := by
        intro heq
        apply hxy
        exact Prod.ext hsrc heq
      rw [← hsrc]
      exact raggedWirePort_disjoint (splits x.1) x.2 y.2 hport
    · exact Finset.disjoint_of_subset_left
        (raggedWirePort_subset (splits x.1) x.2)
        (Finset.disjoint_of_subset_right
          (raggedWirePort_subset (splits y.1) y.2) (hsource x.1 y.1 hsrc))
  rw [hroute, Finset.card_biUnion hdisj]

/-- The same port-sum formula is available directly on the routed global
ownership partition used by `raggedPlacement`. -/
theorem RaggedWirePartition.route_card_eq_port_sum {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (destination : KBag 64 d → Option (Fin 64) → KBag 64 d)
    (target : KBag 64 d) :
    ((P.route splits destination).sets target).card =
      ∑ x ∈ (Finset.univ : Finset (KBag 64 d × Option (Fin 64))).filter
        (fun x => destination x.1 x.2 = target),
          (raggedWirePort (splits x.1) x.2).card := by
  exact routeRaggedWires_card_eq_port_sum P.sets splits destination P.disjoint target

end Tapered945
