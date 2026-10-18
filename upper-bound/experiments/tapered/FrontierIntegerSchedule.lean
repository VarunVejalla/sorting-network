import FrontierBootstrapSchedule
import FrontierCountStep

namespace Tapered945

open Chvatal

theorem candidate_first_partition_invariant (d : Nat) (hd : 14 ≤ d) :
    CandidateFlowInvariant d 1 (candidateFirstPartition d hd) := by
  refine ⟨candidate_first_partition_counts d hd, ?_, ?_⟩
  · intro h; norm_num at h
  · intro h; norm_num at h

/-- The actual ownership partitions and their count invariants are built
together. Each successor uses one coherent source table on the preceding
partition. The index is stage minus one; the raw-root route is separate. -/
noncomputable def candidateFlowTrace (d : Nat) (hd : 14 ≤ d) :
    (i : Nat) → i + 1 ≤ candidateTerminalCutoff d →
      {P : RaggedWirePartition d // CandidateFlowInvariant d (i + 1) P}
  | 0, _ => ⟨candidateFirstPartition d hd, candidate_first_partition_invariant d hd⟩
  | i + 1, hi =>
    let prev := candidateFlowTrace d hd i (by omega)
    ⟨candidateActualEvenStep hd (i + 1) (by omega) (by omega)
        prev.val prev.property.toCandidateActualCounts,
      candidate_flow_invariant_step hd (by omega) (by omega) prev.val
        prev.property.toCandidateActualCounts prev.property⟩

noncomputable def candidateIntegerStage (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t ≤ candidateTerminalCutoff d) :
    RaggedWirePartition d := (candidateFlowTrace d hd (t - 1) (by omega)).val

theorem candidate_integer_stage_invariant (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t ≤ candidateTerminalCutoff d) :
    CandidateFlowInvariant d t (candidateIntegerStage d hd t ht0 ht) := by
  have htime : t - 1 + 1 = t := by omega
  simpa only [htime, candidateIntegerStage] using
    (candidateFlowTrace d hd (t - 1) (by omega : t - 1 + 1 ≤ candidateTerminalCutoff d)).property

theorem candidate_integer_stage_step (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) :
    candidateIntegerStage d hd (t + 1) (by omega) (by omega) =
      candidateActualEvenStep hd t ht0 ht (candidateIntegerStage d hd t ht0 ht.le)
        (candidate_integer_stage_invariant d hd t ht0 ht.le).toCandidateActualCounts := by
  cases t with
  | zero => omega
  | succ i => rfl

theorem candidate_terminal_cutoff_pos (d : Nat) (hd : 14 ≤ d) :
    1 ≤ candidateTerminalCutoff d := by
  unfold candidateTerminalCutoff candidateTf
  omega

/-- One globally time-indexed ownership schedule, frozen after the terminal
cutoff so that it can be passed directly to `raggedX` and `raggedPlacement`. -/
noncomputable def candidateIntegerSchedule (d : Nat) (hd : 14 ≤ d)
    (t : Nat) : RaggedWirePartition d :=
  if ht0 : t = 0 then RaggedWirePartition.initial d
  else if ht : t ≤ candidateTerminalCutoff d then
    candidateIntegerStage d hd t (by omega) ht
  else candidateIntegerStage d hd (candidateTerminalCutoff d)
    (candidate_terminal_cutoff_pos d hd) le_rfl

theorem candidate_integer_schedule_initial (d : Nat) (hd : 14 ≤ d) :
    candidateIntegerSchedule d hd 0 = RaggedWirePartition.initial d := by
  simp [candidateIntegerSchedule]

theorem candidate_integer_schedule_bootstrap (d : Nat) (hd : 14 ≤ d) :
    candidateIntegerSchedule d hd 1 =
      routeEvenFlows (candidateIntegerSchedule d hd 0) (candidateInitialFlows d hd) := by
  have hcut := candidate_terminal_cutoff_pos d hd
  simp [candidateIntegerSchedule, hcut, candidateIntegerStage, candidateFlowTrace,
    candidateFirstPartition]

theorem candidate_integer_schedule_invariant (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t ≤ candidateTerminalCutoff d) :
    CandidateFlowInvariant d t (candidateIntegerSchedule d hd t) := by
  simpa only [candidateIntegerSchedule, dif_neg (by omega : t ≠ 0), dif_pos ht] using
    candidate_integer_stage_invariant d hd t ht0 ht

theorem candidate_integer_schedule_step (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) :
    candidateIntegerSchedule d hd (t + 1) =
      candidateActualEvenStep hd t ht0 ht (candidateIntegerSchedule d hd t)
        (candidate_integer_schedule_invariant d hd t ht0 ht.le).toCandidateActualCounts := by
  simpa only [candidateIntegerSchedule, dif_neg (by omega : t + 1 ≠ 0),
    dif_neg (by omega : t ≠ 0), dif_pos (by omega : t + 1 ≤ candidateTerminalCutoff d),
    dif_pos ht.le] using candidate_integer_stage_step d hd t ht0 ht

/-- Every transition, including the initial root split, is realized by one
global even-port table and the physical tree router. -/
theorem candidate_integer_schedule_routed (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTerminalCutoff d) :
    ∃ F : ∀ b : KBag 64 d, EvenFlowSplit ((candidateIntegerSchedule d hd t).sets b).card,
      candidateIntegerSchedule d hd (t + 1) =
        routeEvenFlows (candidateIntegerSchedule d hd t) F := by
  by_cases ht0 : t = 0
  · subst t
    exact ⟨candidateInitialFlows d hd, candidate_integer_schedule_bootstrap d hd⟩
  · have ht1 : 1 ≤ t := by omega
    exact ⟨candidateEvenFlowSplits hd t ht1 ht (candidateIntegerSchedule d hd t)
      (candidate_integer_schedule_invariant d hd t ht1 ht.le).toCandidateActualCounts,
      candidate_integer_schedule_step d hd t ht1 ht⟩

/-- Any complete six-stage segment has actual partition invariants at all
seven states and a coherent physical split table at each transition. This
includes upper clipping phases. -/
theorem candidate_six_stage_integer_cycle (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 1 ≤ t) (ht : t + 6 ≤ candidateTerminalCutoff d) :
    (∀ i : Fin 7, CandidateFlowInvariant d (t + i.val)
      (candidateIntegerSchedule d hd (t + i.val))) ∧
    (∀ i : Fin 6,
      ∃ F : ∀ b : KBag 64 d,
        EvenFlowSplit ((candidateIntegerSchedule d hd (t + i.val)).sets b).card,
        candidateIntegerSchedule d hd (t + i.val + 1) =
          routeEvenFlows (candidateIntegerSchedule d hd (t + i.val)) F) := by
  constructor
  · intro i
    exact candidate_integer_schedule_invariant d hd _ (by omega) (by have := i.isLt; omega)
  · intro i
    exact candidate_integer_schedule_routed d hd _ (by have := i.isLt; omega)

/-- At the scale-matched terminal meeting, only level `d-7` is occupied and
each register differs from its native `64^7` target by at most 69 wires.
This is an ownership/count theorem, not a statement about sorted ranks. -/
theorem candidate_integer_terminal_counts (d : Nat) (hd : 14 ≤ d) :
    (∀ b : KBag 64 d,
      Even ((candidateIntegerSchedule d hd (candidateTerminalCutoff d)).sets b).card) ∧
    (∀ b : KBag 64 d, b.l = d - 7 →
      |(((candidateIntegerSchedule d hd (candidateTerminalCutoff d)).sets b).card : Rat) -
        (64 ^ 7 : Rat)| ≤ 69) ∧
    (∀ b : KBag 64 d, b.l ≠ d - 7 →
      ((candidateIntegerSchedule d hd (candidateTerminalCutoff d)).sets b).card = 0) := by
  have I := candidate_integer_schedule_invariant d hd (candidateTerminalCutoff d)
    (candidate_terminal_cutoff_pos d hd) le_rfl
  have hs := candidate_terminal_cutoff_scale d hd
  have hmeet : candidateAlpha d (candidateTerminalCutoff d) =
      candidateOmega (candidateTerminalCutoff d) := hs.1.trans hs.2.1.symm
  refine ⟨I.even, ?_, ?_⟩
  · intro b hb
    have hactive : candidateScheduledActive d (candidateTerminalCutoff d) b := by
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hp := candidate_alpha_parity d (candidateTerminalCutoff d)
      omega
    have herr := I.error b hactive
    rw [candidate_flow_target_formula, if_pos (Or.inr hmeet)] at herr
    simpa only [candidateNativeCapacity, hb, show d - (d - 7) = 7 by omega] using herr
  · intro b hb
    apply I.inactive b
    intro hactive
    have hlo := hactive.1.1
    have hhi := hactive.1.2
    omega

end Tapered945
