import FrontierBandGeometry
import FrontierWireFlow

namespace Tapered945

open Chvatal

def scheduledActualCount (shape : ScheduledFlowShape) (B C e : Rat) (count : Nat)
    (herr : |(count : Rat) - scheduledFlowTarget shape B C e| ≤ 69) :
    ScheduledFlowCount shape B C e where
  count := count
  error := (count : Rat) - scheduledFlowTarget shape B C e
  count_eq := by ring
  error_le := herr

theorem candidate_flow_mode_reservoir_gate (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (hb : candidateScheduledActive d t b)
    (hshape : candidateFlowMode d t b = .bottomExpansion ∨
      candidateFlowMode d t b = .bootstrap) :
    candidateReferenceCapacity d b.l t / 256 ≤ candidateNativeCapacity d b.l := by
  have hlow : b.l = candidateOmega t ∧
      candidateOmega (t + 1) = candidateOmega t + 1 := by
    by_cases h1 : t = 1
    · subst t
      have hfront := candidate_frontiers_stage_one d hd
      have hbl : b.l = 1 := by
        have hlo := hb.1.1
        have hhi := hb.1.2
        omega
      constructor
      · omega
      · norm_num [candidateOmega, candidateOmegaBase, Chvatal.ceilParity]
    · unfold candidateFlowMode at hshape
      split_ifs at hshape <;> simp_all
  rw [hlow.1, candidate_native_binary d _ (candidate_omega_le_depth d hd t (by
    unfold candidateTerminalCutoff at ht; omega))]
  exact candidate_bottom_expansion_integer_scale d hd t (by
    unfold candidateTerminalCutoff at ht; omega) hlow.2

/-- The numerical part of the scheduler invariant, measured on one actual
wire partition. Bootstrap and terminal states use their native count target;
interior and frontier states use their distinct rational targets. -/
structure CandidateActualCounts (d t : Nat) (P : RaggedWirePartition d) : Prop where
  even : ∀ b, Even (P.sets b).card
  inactive : ∀ b, ¬ candidateScheduledActive d t b → (P.sets b).card = 0
  error : ∀ b, candidateScheduledActive d t b →
    |((P.sets b).card : Rat) - candidateFlowTarget d t b| ≤ 69

/-- Choose each source's frontier-specific split once, indexed by its actual
register cardinality. Repeated uses of an address share this same choice. -/
noncomputable def chooseCandidateSourceFlows {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) :
    ScheduledEvenFlow (candidateFlowMode d t b) (candidateNativeCapacity d b.l)
      (candidateReferenceCapacity d b.l t) (bagAddressDebt b) (P.sets b).card := by
  apply Classical.choice
  exact scheduled_even_flow_nonempty (candidateFlowMode d t b) _ _ _
    (scheduledActualCount _ _ _ _ (P.sets b).card (H.error b hb))
    (H.even b) (candidate_active_capacity_lower d hd t (by
      unfold candidateTerminalCutoff at ht; omega) b.l hb.1.1)
    (candidate_flow_mode_reservoir_gate d hd t ht0 ht b hb)
    (bagAddressDebt_bounds b)

noncomputable def candidateEvenFlowSplits {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d) :
    EvenFlowSplit (P.sets b).card := by
  classical
  exact if hb : candidateScheduledActive d t b then
    (chooseCandidateSourceFlows hd t ht0 ht P H b hb).split
  else wholeUpEvenSplit (P.sets b).card (H.even b)

theorem candidateEvenFlowSplits_active {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) :
    candidateEvenFlowSplits hd t ht0 ht P H b =
      (chooseCandidateSourceFlows hd t ht0 ht P H b hb).split := by
  simp [candidateEvenFlowSplits, hb]

theorem candidateEvenFlowSplits_inactive_up {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d)
    (hb : ¬ candidateScheduledActive d t b) :
    (candidateEvenFlowSplits hd t ht0 ht P H b).up = 0 := by
  simp [candidateEvenFlowSplits, hb, wholeUpEvenSplit, H.inactive b hb]

noncomputable def candidateActualEvenStep {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) : RaggedWirePartition d :=
  routeEvenFlows P (candidateEvenFlowSplits hd t ht0 ht P H)

theorem candidateActualEvenStep_even {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht0 : 1 ≤ t)
    (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d) :
    Even ((candidateActualEvenStep hd t ht0 ht P H).sets b).card :=
  routeEvenFlows_card_even P _ b

theorem EvenFlowSplit.block_zero_of_whole {count : Nat} (F : EvenFlowSplit count)
    (hup : F.up = count) (j : Fin 64) : F.blocks j = 0 := by
  have hj : F.blocks j ≤ ∑ k, F.blocks k :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (F.blocks k)) (Finset.mem_univ j)
  have ht := F.total
  rw [hup, Nat.sub_self] at ht
  omega

section SourcePorts

variable {d t : Nat} (hd : 14 ≤ d) (ht0 : 1 ≤ t)
  (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
  (H : CandidateActualCounts d t P)

local notation "F" => candidateEvenFlowSplits hd t ht0 ht P H

theorem candidate_source_up_error (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) :
    |((F b).up : Rat) - scheduledUpTarget (candidateFlowMode d t b)
      (candidateReferenceCapacity d b.l t) (bagAddressDebt b) (P.sets b).card| ≤ 1 := by
  rw [candidateEvenFlowSplits_active hd t ht0 ht P H b hb]
  exact (chooseCandidateSourceFlows hd t ht0 ht P H b hb).up_error

theorem candidate_source_block_error (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (j : Fin 64) :
    |((F b).blocks j : Rat) - scheduledDownTarget (candidateFlowMode d t b)
      (candidateNativeCapacity d b.l) (candidateReferenceCapacity d b.l t)
      (bagAddressDebt b) j| ≤ evenFlowBlockError := by
  rw [candidateEvenFlowSplits_active hd t ht0 ht P H b hb]
  exact (chooseCandidateSourceFlows hd t ht0 ht P H b hb).block_error j

theorem candidate_source_advance_up (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hmode : candidateFlowMode d t b = .topAdvance) :
    (F b).up = 0 := by
  rw [candidateEvenFlowSplits_active hd t ht0 ht P H b hb]
  exact (chooseCandidateSourceFlows hd t ht0 ht P H b hb).advance_up hmode

theorem candidate_source_whole_up (b : KBag 64 d)
    (hb : candidateScheduledActive d t b)
    (hmode : candidateFlowMode d t b = .bottomContraction) :
    (F b).up = (P.sets b).card := by
  rw [candidateEvenFlowSplits_active hd t ht0 ht P H b hb]
  exact (chooseCandidateSourceFlows hd t ht0 ht P H b hb).whole_up (Or.inl hmode)

end SourcePorts

end Tapered945
