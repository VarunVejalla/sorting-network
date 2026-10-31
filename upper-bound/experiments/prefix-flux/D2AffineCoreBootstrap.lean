import D2StrongFlowCoreInputs

namespace Chvatal.D2Reserve

private theorem d2FlowStageAffineCoreInputs_of_inactive_tail
    {active : Nat → Bool} {role : Nat → D2Role} {cap : Nat → Nat}
    {h i : Nat} (tree : D2FlowTree h)
    (hinactive : ∀ j, i ≤ j → active j = false) :
    d2FlowStageAffineCoreInputs active role cap i tree := by
  induction h generalizing i with
  | zero =>
      cases tree
      trivial
  | succ h ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageAffineCoreInputs]
          refine ⟨?_, ?_⟩
          · intro j
            exact ih (i := i + 1) (children j) (by
              intro k hk
              exact hinactive k (by omega))
          · simp [hinactive i (by omega)]

/-- The initial candidate snapshot satisfies the full affine core contract:
only its root is active, as a top-descending sender with zero deficit. -/
theorem d2FlowCandidateRun_initial_affine_core (d : Nat) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive d 0 i)
      (fun i => d2FlowCandidateRole d 0 i)
      (fun i => d2FlowCandidateCapacity d i 0) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 0) := by
  cases d with
  | zero =>
      simp [d2FlowCandidateRun, d2FlowTreeInitial,
        d2FlowStageAffineCoreInputs]
  | succ d =>
      have hchildren : ∀ j : Fin 8,
          d2FlowStageAffineCoreInputs
            (fun i => d2FlowCandidateActive (d + 1) 0 i)
            (fun i => d2FlowCandidateRole (d + 1) 0 i)
            (fun i => d2FlowCandidateCapacity (d + 1) i 0) 1
            (d2FlowTreeFull 8192 d) := by
        intro j
        apply d2FlowStageAffineCoreInputs_of_inactive_tail
        intro k hk
        simp [d2FlowCandidateActive]
        omega
      have hrole : d2FlowCandidateRole (d + 1) 0 0 = .topDesc := by
        simp [d2FlowCandidateRole]
      simp only [d2FlowCandidateRun, d2FlowTreeInitial,
        d2FlowStageAffineCoreInputs, d2FlowCandidateActive, if_pos]
      rw [hrole]
      exact ⟨hchildren, by simp⟩

end Chvatal.D2Reserve
