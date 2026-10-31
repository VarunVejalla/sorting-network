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

/-! ### Stage-two boundary sender -/

/-- The newly active stage-two bottom-descending boundary sender satisfies
the sharper affine core profile.  The existing strict-input theorem supplies
the endpoint reserves; the exact two-point deficit profile supplies the
stronger affine inequality. -/
theorem d2FlowCandidateStage2_boundary_affine_sender
    (d : Nat) (hd : 5 ≤ d) (G low high : Nat)
    (hG : G = 0 ∨ G = 2 ^ (3 * d + 7))
    (hbal : low + high = G) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 2 i)
      (fun i => d2FlowCandidateRole (d + 2) 2 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 2) 2
      (.node G low high (fun _ => d2FlowTreeFull 8192 (d - 1))) := by
  have hstrict := d2FlowCandidateStage2_sender_inputs d hd G low high hG hbal
  have hrole := d2FlowCandidateStage2_boundary_role d hd
  have hcap : d2FlowCandidateCapacity (d + 2) 2 2 = 2 ^ (3 * d + 17) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hprofile : 8192 * G + 7 ≤
      15 * d2FlowCandidateCapacity (d + 2) 2 2 := by
    rw [hcap]
    rcases hG with hG | hG
    · simp [hG]
      have hx : 0 < 2 ^ (3 * d + 17) := by positivity
      omega
    · rw [hG]
      have hp : 2 ^ (3 * d + 17) = 1024 * 2 ^ (3 * d + 7) := by
        rw [show 3 * d + 17 = 10 + (3 * d + 7) by omega, pow_add]
        norm_num
      rw [hp]
      have hx : 0 < 2 ^ (3 * d + 7) := by positivity
      omega
  simp only [d2FlowStageAffineCoreInputs]
  refine ⟨?_, ?_⟩
  · intro j
    exact d2FlowStageAffineCoreInputs_of_inactive_tail
      (i := 3) (tree := d2FlowTreeFull 8192 (d - 1)) (by
        intro k hk
        simp [d2FlowCandidateActive]
        omega)
  · rcases hrole with ⟨hactive, hrole⟩
    simp only [hactive, if_pos, hrole]
    simp only [d2FlowStageInvInputs] at hstrict
    rcases hstrict with ⟨_, hlocal⟩
    simp only [hactive, if_pos, hrole] at hlocal
    rcases hlocal with ⟨hbalance, _, _, _, _, hleft, hright⟩
    exact ⟨hbalance, hprofile, hleft, hright⟩

/-- Each child left by the first sender is an affine-core stage-two sender.
All eight children are active; only the two endpoint deficits are nonzero. -/
theorem d2FlowCandidateStage1_child_stage2_affine
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 2 i)
      (fun i => d2FlowCandidateRole (d + 2) 2 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 2) 2
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) j) := by
  rw [d2FlowCandidateStage1_child_tree d hd j]
  cases d with
  | zero => omega
  | succ d' =>
      by_cases h0 : j.val = 0
      · simpa [h0, d2FlowTreeSetRoot, d2FlowTreeFull] using
          (d2FlowCandidateStage2_boundary_affine_sender (d := d' + 1) (by omega)
            (2 ^ (3 * (d' + 1) + 7))
            (2 ^ (3 * (d' + 1) + 7)) 0 (Or.inr rfl) (by simp))
      · by_cases h7 : j.val = 7
        · simpa [h0, h7, d2FlowTreeSetRoot, d2FlowTreeFull] using
            (d2FlowCandidateStage2_boundary_affine_sender (d := d' + 1) (by omega)
              (2 ^ (3 * (d' + 1) + 7)) 0
              (2 ^ (3 * (d' + 1) + 7)) (Or.inr rfl) (by simp))
        · simpa [h0, h7, d2FlowTreeSetRoot, d2FlowTreeFull] using
            (d2FlowCandidateStage2_boundary_affine_sender (d := d' + 1) (by omega)
              0 0 0 (Or.inl rfl) (by simp))

/-- The entire first-sender subtree satisfies the affine stage-two contract. -/
theorem d2FlowCandidateStage1_subtree_stage2_affine
    (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 2 i)
      (fun i => d2FlowCandidateRole (d + 2) 2 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 2) 1
      (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
        (d2FlowCandidateRole (d + 2) 1)
        (d2FlowCandidateQuota (d + 2) 1)
        (d + 1) 1 (.node 0 0 0
          (fun _ => d2FlowTreeFull 8192 d))) := by
  have hfalse : d2FlowCandidateActive (d + 2) 2 1 = false := by
    simp [d2FlowCandidateActive]
  cases htree : d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)) with
  | node G low high children =>
      simp only [d2FlowStageAffineCoreInputs]
      refine ⟨?_, ?_⟩
      · intro j
        have hchild : children j = d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
              (d2FlowCandidateRole (d + 2) 1)
              (d2FlowCandidateQuota (d + 2) 1)
              (d + 1) 1 (.node 0 0 0
                (fun _ => d2FlowTreeFull 8192 d))) j := by
          rw [htree]
          rfl
        rw [hchild]
        exact d2FlowCandidateStage1_child_stage2_affine d hd j
      · simp [hfalse]

/-- The complete stage-two run snapshot satisfies the affine core provider. -/
theorem d2FlowCandidateRun_stage2_affine_core (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 2 i)
      (fun i => d2FlowCandidateRole (d + 2) 2 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 2) 0
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2) := by
  have htree : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 2 =
      .node 0 0 0 (fun _ =>
        d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0
            (fun _ => d2FlowTreeFull 8192 d))) := by
    rw [show d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2 =
          d2FlowCandidateStage (d + 2) 1
            (d2FlowCandidateRun (d + 2)
              (d2FlowTreeInitial 8192 (d + 2)) 1) by rfl,
      show d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 1 =
          d2FlowCandidateStage (d + 2) 0
            (d2FlowTreeInitial 8192 (d + 2)) by rfl,
      d2FlowCandidateBootstrap_shape (d + 1)]
    simp [d2FlowCandidateStage, d2FlowStage, d2FlowCandidateActive,
      d2FlowTreeSetRoot, d2FlowTreeFull]
  rcases d2FlowCandidateStage2_root_role d hd with ⟨hactive, hrole⟩
  rw [htree]
  simp only [d2FlowStageAffineCoreInputs]
  refine ⟨?_, ?_⟩
  · intro j
    exact d2FlowCandidateStage1_subtree_stage2_affine d hd
  · simp [hactive, hrole]

/-! ### Stage-three local affine cases -/

/-- At level three the stage-three sender is bottom-rising, so the strict
input contract already contains exactly the affine local requirement: balance.
All its children lie below the active band. -/
theorem d2FlowCandidateStage3_affine_at3_of_strict
    {d h : Nat} (hd : 5 ≤ d) (tree : D2FlowTree h)
    (hstrict : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3)
      3 tree) :
    d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (d + 2) 3 k)
      (fun k => d2FlowCandidateRole (d + 2) 3 k)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3) 3
      tree := by
  rcases d2FlowCandidateStage3_frontiers d hd with
    ⟨_, _, hactive, hrole⟩
  cases htree : tree with
  | leaf G low high => trivial
  | node G low high children =>
      rw [htree] at hstrict
      simp only [d2FlowStageInvInputs] at hstrict
      rcases hstrict with ⟨hchildren, hlocal⟩
      simp only [d2FlowStageAffineCoreInputs]
      refine ⟨?_, ?_⟩
      · intro j
        apply d2FlowStageAffineCoreInputs_of_inactive_tail (children j)
        intro k hk
        simp [d2FlowCandidateActive, tfD2]
        omega
      · simp only [hactive, if_pos, hrole] at hlocal ⊢
        rcases hlocal with ⟨hbal, _⟩
        exact ⟨hbal, trivial⟩

/-- At level two stage three is inactive; its recursive children are the
bottom-rising level-three senders handled above. -/
theorem d2FlowCandidateStage3_affine_at2_of_strict
    {d h : Nat} (hd : 5 ≤ d) (tree : D2FlowTree h)
    (hstrict : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3) 2 tree) :
    d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (d + 2) 3 k)
      (fun k => d2FlowCandidateRole (d + 2) 3 k)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3) 2 tree := by
  have hfalse : d2FlowCandidateActive (d + 2) 3 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases htree : tree with
  | leaf G low high => trivial
  | node G low high children =>
      rw [htree] at hstrict
      simp only [d2FlowStageInvInputs] at hstrict
      rcases hstrict with ⟨hchildren, _⟩
      simp only [d2FlowStageAffineCoreInputs]
      refine ⟨?_, ?_⟩
      · intro j
        exact d2FlowCandidateStage3_affine_at3_of_strict hd
          (children j) (by simpa [htree] using hchildren j)
      · simp [hfalse]

/-- The first-sender subtree at stage three has a zero-deficit top-rise root;
its strict local theorem supplies endpoint reserves, while its level-two
children are converted by the bottom-rise/inactive lemmas above. -/
theorem d2FlowCandidateStage3_firstSenderSubtree_affine
    (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 3 i)
      (fun i => d2FlowCandidateRole (d + 2) 3 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 3) 1
      (d2FlowTreeSetRoot (d2FlowCandidateStage2_firstSenderSubtree d) 0 0 0) := by
  have hstrict := d2FlowCandidateStage3_firstSenderSubtree_topRise_inputs d hd
  have hactive : d2FlowCandidateActive (d + 2) 3 1 = true :=
    (d2FlowCandidateStage3_frontiers d hd).1
  have hrole : d2FlowCandidateRole (d + 2) 3 1 = .topRise :=
    (d2FlowCandidateStage3_frontiers d hd).2.1
  have htree : d2FlowTreeSetRoot
      (d2FlowCandidateStage2_firstSenderSubtree d) 0 0 0 =
      .node 0 0 0 (fun j =>
        d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) j) := by
    cases d2FlowCandidateStage2_firstSenderSubtree d
    rfl
  rw [htree]
  simp only [d2FlowStageInvInputs] at hstrict
  simp only [d2FlowStageAffineCoreInputs]
  refine ⟨?_, ?_⟩
  · intro j
    exact d2FlowCandidateStage3_affine_at2_of_strict hd _ (hstrict.1 j)
  · simp only [hactive, if_pos, hrole]
    have hlocal := hstrict.2
    simp only [hactive, if_pos, hrole] at hlocal
    rcases hlocal with ⟨_, hfields⟩
    rcases hfields with ⟨_, _, _, _, hleft, hright⟩
    exact ⟨trivial, trivial, hleft, hright⟩

/-- The full candidate run after stage two satisfies the affine core contract
needed to start the general provider induction. -/
theorem d2FlowCandidateRun_stage3_affine_core (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive (d + 2) 3 i)
      (fun i => d2FlowCandidateRole (d + 2) 3 i)
      (fun i => d2FlowCandidateCapacity (d + 2) i 3) 0
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 3) := by
  have hshape := d2FlowCandidateRun_stage2_shape d hd
  have hfalse : d2FlowCandidateActive (d + 2) 3 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  rw [hshape]
  simp only [d2FlowStageAffineCoreInputs]
  refine ⟨?_, ?_⟩
  · intro j
    simpa using d2FlowCandidateStage3_firstSenderSubtree_affine d hd
  · simp [hfalse]


end Chvatal.D2Reserve
