import RaggedTreeFlowBridge
import Mathlib.Tactic

namespace Tapered945

/-! Historical conditional ordinary-flow interface. Its frontier-error
premises concern ordinary occupancy and are not the tapered frontier
invariant. Use `FrontierIntegerSchedule` for the initialized, shape-specific
actual ownership/count schedule and its coherent routed transitions. -/

open Chvatal

/-- An address that enters at the next step without an ordinary interior
parent. By the schedule classification these are exactly frontier addresses. -/
def candidateFrontierChildAddress (d t : Nat) (q : KBag 64 d) : Prop :=
  (q.l + 1 = candidateAlpha d t ∧
    candidateAlpha d t = candidateAlpha d (t + 1) + 1) ∨
  (q.l = candidateOmega t + 1 ∧
    candidateOmega (t + 1) = candidateOmega t + 1)

/-- A frontier's actual routed size is enough to invoke the same checked
integerizer used at an ordinary node. The real frontier calculation therefore
only needs to prove this single discrepancy bound. -/
theorem candidate_frontier_flow_of_count_error {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht : t < candidateTf d)
    (q : KBag 64 d) (hq : candidateScheduledActive d (t+1) q)
    (Pnext : RaggedWirePartition d)
    (herror : |candidateActualNextFlowError Pnext t q| ≤ 69) :
    Nonempty (LocalIntegerFlow q
      (candidateReferenceCapacity d q.l (t+1))
      (candidateActualNextFlowError Pnext t q) ((Pnext.sets q).card)) := by
  have htNext : t + 1 ≤ candidateTf d := by omega
  have hcapacity := candidate_active_capacity_lower d hd (t+1) htNext q.l hq.1.1
  have hcount : ((Pnext.sets q).card : Rat) =
      (1 - 1 / cap) * candidateReferenceCapacity d q.l (t+1) +
        candidateActualNextFlowError Pnext t q := by
    unfold candidateActualNextFlowError
    ring
  exact local_integer_flow_nonempty q _ _ _ hcapacity herror hcount

/-- Given one actual current-stage flow table, the ordinary rule supplies
flows for every interior-generated next address. If the caller supplies
actual-cardinality flows for the two exceptional frontier families, every
scheduled next address has a compatible local flow. -/
theorem candidate_next_actual_flow_nonempty {d : Nat}
    (hd : 14 ≤ d) (P Pnext : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (hnext : Pnext = P.route
      (activeFlowWireSplits P (candidateScheduledActive d t)
        (fun q => candidateReferenceCapacity d q.l t) eta F)
      raggedTreeDestination)
    (hfrontierError : ∀ q, candidateScheduledActive d (t+1) q →
      candidateFrontierChildAddress d t q →
      |candidateActualNextFlowError Pnext t q| ≤ 69) :
    ∀ q, candidateScheduledActive d (t+1) q →
      Nonempty (LocalIntegerFlow q (candidateReferenceCapacity d q.l (t+1))
        (candidateActualNextFlowError Pnext t q) ((Pnext.sets q).card)) := by
  intro q hq
  rcases candidate_next_active_interior_or_frontier hd t ht q hq with
    hinterior | htop | hbottom
  · exact candidate_interior_actual_flow_nonempty hd P Pnext t ht eta F hnext q hinterior
  · exact candidate_frontier_flow_of_count_error hd t ht q hq Pnext
      (hfrontierError q hq (Or.inl htop))
  · exact candidate_frontier_flow_of_count_error hd t ht q hq Pnext
      (hfrontierError q hq (Or.inr hbottom))

/-- Choose one local flow per next active address, so repeated descriptions of
an address cannot create incompatible flow choices. The count index is the
actual routed register cardinality. -/
noncomputable def chooseCandidateNextActualFlows {d : Nat}
    (hd : 14 ≤ d) (P Pnext : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (hnext : Pnext = P.route
      (activeFlowWireSplits P (candidateScheduledActive d t)
        (fun q => candidateReferenceCapacity d q.l t) eta F)
      raggedTreeDestination)
    (hfrontierError : ∀ q, candidateScheduledActive d (t+1) q →
      candidateFrontierChildAddress d t q →
      |candidateActualNextFlowError Pnext t q| ≤ 69) :
    ∀ q, candidateScheduledActive d (t+1) q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l (t+1))
        (candidateActualNextFlowError Pnext t q) ((Pnext.sets q).card) := by
  classical
  intro q hq
  exact Classical.choice
    (candidate_next_actual_flow_nonempty hd P Pnext t ht eta F hnext
      hfrontierError q hq)

end Tapered945
