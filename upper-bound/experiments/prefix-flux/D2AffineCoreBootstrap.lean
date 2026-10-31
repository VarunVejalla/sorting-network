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

/-- The first post-bootstrap snapshot also satisfies the affine core
contract. Its only active senders are the level-one top-rise nodes; the
bootstrap has reset each such node to zero while leaving its grandchildren
full, so both endpoint reserves hold. -/
theorem d2FlowCandidateRun_stage1_affine_core (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 1 i)
      (fun i => d2FlowCandidateRole (d + 2) 1 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 1) 0
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 1) := by
  have hshape : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 1 =
      .node 0 0 0 (fun _ => .node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)) := by
    rw [d2FlowCandidateRun]
    change d2FlowCandidateStage (d + 2) 0
      (d2FlowTreeInitial 8192 (d + 2)) = _
    simpa using d2FlowCandidateBootstrap_shape (d + 1)
  have hsender : d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 1 i)
      (fun i => d2FlowCandidateRole (d + 2) 1 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 1) 1
      (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)) := by
    have hstrict := d2FlowCandidateBootstrap_sender_inputs (d := d) hd
    simp only [d2FlowStageInvInputs] at hstrict
    have hactive : d2FlowCandidateActive (d + 2) 1 1 = true := by
      simp [d2FlowCandidateActive]
    have hrole : d2FlowCandidateRole (d + 2) 1 1 = .topRise := by
      rw [d2FlowCandidateRole_matches_schedule (by omega)]
      exact d2ScheduleRole_first_sender (by omega)
    simp only [d2FlowStageAffineCoreInputs]
    refine ⟨?_, ?_⟩
    · intro j
      apply d2FlowStageAffineCoreInputs_of_inactive_tail
      intro k hk
      simp [d2FlowCandidateActive]
      omega
    · simp only [hactive, if_pos, hrole]
      rcases hstrict with ⟨_, hlocal⟩
      simp only [hactive, if_pos, hrole] at hlocal
      rcases hlocal with ⟨_, _, _, _, _, hleft, hright⟩
      exact ⟨trivial, ⟨trivial, hleft, hright⟩⟩
  rw [hshape]
  change (∀ j : Fin 8, d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 1 i)
      (fun i => d2FlowCandidateRole (d + 2) 1 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 1) 1
      (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) ∧ True
  exact ⟨fun _ => hsender, trivial⟩

end Chvatal.D2Reserve
