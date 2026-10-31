import D2ScheduleReserve

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputsTolerant
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

/-! A single all-time induction packages stage preservation on the actual
candidate run. The sender-input provider is still the substantive open
obligation; this theorem makes its exact scope explicit. -/

theorem d2FlowCandidateRun_preserves_inv_of_tolerant_all_inputs
    (d n : Nat) (initial : D2FlowTree d)
    (hinitial : d2FlowTreeInv 8192 initial)
    (hinputs : ∀ t, t < n →
      d2FlowStageInvInputsTolerant 8192
        (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d initial t)) :
    d2FlowTreeInv 8192 (d2FlowCandidateRun d initial n) := by
  induction n with
  | zero => simpa [d2FlowCandidateRun] using hinitial
  | succ n ih =>
      have hprev : d2FlowTreeInv 8192 (d2FlowCandidateRun d initial n) := by
        apply ih
        intro t ht
        exact hinputs t (by omega)
      have hstep := d2FlowStage_preserves_inv_of_tolerant_inputs
        (d2FlowCandidateRun d initial n) hprev (hinputs n (by omega))
      simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hstep

theorem d2FlowCandidate_terminal_inv_of_tolerant_all_inputs
    (d : Nat)
    (hinputs : ∀ t, t < tfD2 d →
      d2FlowStageInvInputsTolerant 8192
        (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (tfD2 d)) := by
  exact d2FlowCandidateRun_preserves_inv_of_tolerant_all_inputs
    d (tfD2 d) (d2FlowTreeInitial 8192 d)
    (d2FlowTreeInitial_inv 8192 d) hinputs

end Chvatal.D2Reserve
