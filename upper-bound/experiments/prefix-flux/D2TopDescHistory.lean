import D2CoreProviderReserveStep

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
set_option linter.unnecessarySeqFocus false

/-- The reserve invariant projects to every subtree selected by a path. -/
theorem d2FlowTreeInv_atPath
    {scale h n : Nat} (tree : D2FlowTree (h + n))
    (path : D2FlowPath n) (hinv : d2FlowTreeInv scale tree) :
    d2FlowTreeInv scale (d2FlowTreeAtPath n tree path) := by
  induction path generalizing h with
  | nil => simpa [d2FlowTreeAtPath] using hinv
  | @cons n port tail ih =>
      cases tree with
      | node G low high children =>
          have hinvNode : d2FlowTreeInv scale (.node G low high children) := by
            simpa using hinv
          have hchildInv : d2FlowTreeInv scale (children port) := by
            simp only [d2FlowTreeInv] at hinvNode
            exact hinvNode.2.2.2 port
          simpa [d2FlowTreeAtPath] using
            ih (h := h) (tree := children port) hchildInv

/-- At positive tree height, invariant and zero root deficit force exact
endpoint balance. -/
theorem d2FlowTreeInv_root_balance_of_zero_local
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (hscale : 0 < scale)
    (hz : d2FlowTreeRootDeficit tree = 0) :
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  cases tree with
  | node G low high children =>
      have hG : G = 0 := by simpa [d2FlowTreeRootDeficit] using hz
      have hinvNode : d2FlowTreeInv scale (.node G low high children) := by
        simpa using hinv
      have hlt : G < scale * 8 ^ (h + 1) := by rw [hG]; positivity
      have hbalance := hinvNode.2.2.1 hlt
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance

/-- A zero-root child inside an invariant tree is automatically balanced. -/
theorem d2FlowTreeInv_child_balance_of_zero
    {h i : Nat} (tree : D2FlowTree ((h + 2) + i))
    (hinv : d2FlowTreeInv 8192 tree) (path : D2FlowPath i)
    (port : Fin 8) (hzero : d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowTreeAtPath i tree path) port) = 0) :
    (d2FlowTreeRootData
      (d2FlowTreeChild (d2FlowTreeAtPath i tree path) port)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowTreeAtPath i tree path) port)).2.2 = 0 := by
  have hparentInv := d2FlowTreeInv_atPath (scale := 8192)
    (h := h + 2) tree path hinv
  cases hparent : d2FlowTreeAtPath i tree path with
  | node G low high children =>
      have hchildInv : d2FlowTreeInv 8192 (children port) := by
        have hinvNode : d2FlowTreeInv 8192 (.node G low high children) := by
          simpa [hparent] using hparentInv
        simp only [d2FlowTreeInv] at hinvNode
        exact hinvNode.2.2.2 port
      have hzero' : d2FlowTreeRootDeficit (children port) = 0 := by
        simpa [hparent] using hzero
      have hbalance := d2FlowTreeInv_root_balance_of_zero_local
        (tree := children port) hchildInv (by decide) hzero'
      change (d2FlowTreeRootData (children port)).2.1 +
        (d2FlowTreeRootData (children port)).2.2 = 0
      calc
        (d2FlowTreeRootData (children port)).2.1 +
            (d2FlowTreeRootData (children port)).2.2 =
          d2FlowTreeRootDeficit (children port) := hbalance
        _ = 0 := hzero'

/-- Under the full reserve invariant, an explicitly zero-root active child
has balanced endpoints. This supplies the balance field for the `topDesc` and
`topRise` cases of the affine-core local contract. -/
theorem d2FlowCandidateRun_zero_child_balanced_of_inv
    {h i t G low high : Nat} (path : D2FlowPath i) (port : Fin 8)
    (children : Fin 8 → D2FlowTree h)
    (hnode : d2FlowTreeChild
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 2 + i)
          (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port =
      .node G low high children)
    (hinv : d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)))
    (hzero : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) = 0) :
    low + high = G := by
  have hbalance := d2FlowTreeInv_child_balance_of_zero
    (h := h) (i := i)
    (d2FlowCandidateRun (h + 2 + i)
      (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) hinv path port hzero
  rw [hnode] at hbalance hzero
  have hG : G = 0 := by simpa [d2FlowTreeRootDeficit] using hzero
  change low + high = 0 at hbalance
  omega

/-- At arbitrary path depth, a top-descending parent writes zero root data
to the selected child through the path context's actual overwrite callback. -/
theorem d2FlowTreePathContext_parent_topDesc_overwrite_zero
    {h n i j : Nat} (initial : D2FlowTree (h + (n + 1)))
    (path : D2FlowPath (n + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (step : Nat)
    (hlevel : j + 1 = i + (n + 1))
    (ha : active step j = true) (hr : role step j = .topDesc) :
    (d2FlowTreePathContext (n + 1) initial path i
      active role quota overwrite).overwrite step =
      (0, 0, 0) := by
  induction n generalizing h i j active role quota overwrite with
  | zero =>
      cases path with
      | cons port tail =>
          cases tail with
          | nil =>
              have hji : j = i := by omega
              subst j
              simp only [d2FlowTreePathContext]
              change d2FlowTreeRootData
                (d2FlowTreeChild
                  (d2FlowStage (active step) (role step)
                    (quota step) (h + 1) i
                    (d2FlowTreeRunWithParentOverwrites initial i
                      active role quota overwrite step)) port) =
                (0, 0, 0)
              cases htree : d2FlowTreeRunWithParentOverwrites initial i
                  active role quota overwrite step with
              | node G low high children =>
                  exact d2FlowStage_topDesc_child_rootdata children
                    (by simpa using ha) (by simpa using hr) port
  | succ n ih =>
      cases path with
      | cons port tail =>
          cases initial with
          | node G low high children =>
              simp only [d2FlowTreePathContext]
              exact ih (h := h) (i := i + 1) (j := j)
                (children port) tail active role quota
                (fun m => d2FlowTreeChildOverwrite
                  (fun k => d2FlowTreeRunWithParentOverwrites
                    (.node G low high children) i
                    active role quota overwrite k)
                  (i := i) active role quota port m)
                (by omega) ha hr

/-- If every ancestor on a path is inactive, a stage projects exactly to
the recursive stage at the selected subtree. -/
theorem d2FlowStage_path_eq_of_inactive_prefix
    {h n i : Nat} (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) (tree : D2FlowTree (h + n))
    (path : D2FlowPath n)
    (hinactive : ∀ k, k < n → active (i + k) = false) :
    d2FlowTreeAtPath n
        (d2FlowStage active role quota (h + n) i tree) path =
      d2FlowStage active role quota h (i + n)
        (d2FlowTreeAtPath n tree path) := by
  induction path generalizing h i with
  | nil => rfl
  | @cons n port tail ih =>
      cases tree with
      | node G low high children =>
          have hparent : active i = false := by
            simpa using hinactive 0 (by omega)
          have htail : ∀ k, k < n → active (i + 1 + k) = false := by
            intro k hk
            have h := hinactive (k + 1) (by omega)
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
          have hchild := d2FlowStage_inactive_child
            (active := active) (role := role) (quota := quota)
            (h := h + n) (i := i) (G := G) (low := low) (high := high)
            children hparent port
          simp only [d2FlowTreeAtPath, Nat.add_succ]
          rw [hchild]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (h := h) (i := i + 1) (tree := children port) htail

/-- The actual candidate run gives zero root deficit at any path node whose
immediate parent is active and top-descending at the preceding stage. -/
theorem d2FlowCandidateRun_parent_topDesc_root_zero_at_path
    {h i t : Nat} (hi : 1 ≤ i) (path : D2FlowPath i)
    (ha : d2FlowCandidateActive (h + 1 + i) t (i - 1) = true)
    (hr : d2FlowCandidateRole (h + 1 + i) t (i - 1) = .topDesc) :
    d2FlowTreeRootDeficit
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 1 + i)
          (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) = 0 := by
  classical
  cases i with
  | zero => omega
  | succ i =>
      let d := h + 1 + (i + 1)
      let initial := d2FlowTreeInitial 8192 d
      let active := d2FlowCandidateRunActive d
      let role := d2FlowCandidateRunRole d
      let quota := d2FlowCandidateRunQuota d
      let overwrite := d2FlowCandidateRunOverwrite d initial
      let ctx := d2FlowTreePathContext (i + 1) initial path 0
        active role quota overwrite
      have hlevel : ctx.level = i + 1 := by
        simpa [ctx, active, role, quota, overwrite, d, initial] using
          d2FlowTreePathContext_level initial path 0 active role quota overwrite
      have hctxOverwrite : ctx.overwrite t = (0, 0, 0) := by
        exact d2FlowTreePathContext_parent_topDesc_overwrite_zero
          (h := h + 1) (n := i) (i := 0) (j := i)
          initial path
          (d2FlowCandidateRunActive d)
          (d2FlowCandidateRunRole d)
          (d2FlowCandidateRunQuota d)
          (d2FlowCandidateRunOverwrite d initial) t
          (by omega)
          (by simpa [active, d] using ha)
          (by simpa [role, d] using hr)
      have hpath := d2FlowCandidateRun_path_as_history
        (initial := initial) (path := path) (step := t + 1)
      rw [hpath, d2FlowTreePathHistory_eq_context_run]
      rw [show ctx.level = i + 1 by exact hlevel]
      rw [d2FlowTreeRunWithParentOverwrites]
      rw [d2FlowTreeSetRoot_deficit]
      change (ctx.overwrite t).1 = 0
      rw [hctxOverwrite]

/-- Two consecutive inactive parent updates expose the child's own two
stages. A top-descending first child stage preserves its zero root, and an
inactive second child stage preserves it again. -/
theorem d2FlowStage_inactive_parent_two_stage_child_root_zero
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree (h + 1))
    (active0 active1 : Nat → Bool) (role0 role1 : Nat → D2Role)
    (quota0 quota1 : Nat → D2Role → Nat) (port : Fin 8)
    (hparent0 : active0 i = false) (hparent1 : active1 i = false)
    (hchild0 : active0 (i + 1) = true) (hrole0 : role0 (i + 1) = .topDesc)
    (hchild1 : active1 (i + 1) = false)
    (hGzero : d2FlowTreeRootDeficit (children port) = 0) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active1 role1 quota1 (h + 2) i
          (d2FlowStage active0 role0 quota0 (h + 2) i
            (.node G low high children))) port) = 0 := by
  have hfirstChild := d2FlowStage_inactive_child
    (active := active0) (role := role0) (quota := quota0)
    (h := h + 1) (i := i) (G := G) (low := low) (high := high)
    children hparent0 port
  cases hfirstEq : d2FlowStage active0 role0 quota0 (h + 2) i
      (.node G low high children) with
  | node G' low' high' children' =>
      have hsecondChild := d2FlowStage_inactive_child
        (active := active1) (role := role1) (quota := quota1)
        (h := h + 1) (i := i) (G := G') (low := low') (high := high')
        children' hparent1 port
      have hchildTreeEq : children' port =
          d2FlowStage active0 role0 quota0 (h + 1) (i + 1)
            (children port) := by
        have hchildProj := congrArg
          (fun tree => d2FlowTreeChild tree port) hfirstEq
        calc
          children' port = d2FlowTreeChild
              (d2FlowStage active0 role0 quota0 (h + 2) i
                (.node G low high children)) port := by
            simpa using hchildProj.symm
          _ = _ := hfirstChild
      rw [hsecondChild, hchildTreeEq]
      have hchildFirstRoot : d2FlowTreeRootDeficit
          (d2FlowStage active0 role0 quota0 (h + 1) (i + 1)
            (children port)) = 0 := by
        cases hchildTree : children port with
        | node Gc lc hc grandchildren =>
            have hGc : Gc = 0 := by
              simpa [hchildTree] using hGzero
            rw [d2FlowStage_active_node_deficit grandchildren hchild0, hrole0]
            simp [hGc]
      rw [d2FlowStage_root_deficit_of_inactive
        (active := active1) (role := role1) (quota := quota1)
        (i := i + 1) (tree := d2FlowStage active0 role0 quota0
          (h + 1) (i + 1) (children port)) hchild1]
      exact hchildFirstRoot

/-- The repeated-frontier zero source also works for a child of an arbitrary
parent path. The entire prefix above that parent is inactive for both stages,
so the core contract at `t-1` projects to the child and its zero survives. -/
theorem d2FlowCandidateRun_priorTopDesc_child_root_zero
    {h i t : Nat} (hd : 7 ≤ h + 2 + i) (ht : 3 ≤ t)
    (path : D2FlowPath i) (port : Fin 8)
    (hprevFront : i + 1 ≤ alpha (h + 2 + i) (t - 1))
    (hnowFront : i + 2 ≤ alpha (h + 2 + i) t)
    (hprevActive : active (h + 2 + i) (tfD2 (h + 2 + i)) (i + 1) (t - 1))
    (hprevRole : d2ScheduleRole (h + 2 + i) (i + 1) (t - 1) = .topDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1))) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) = 0 := by
  classical
  let d := h + 2 + i
  let initial := d2FlowTreeInitial 8192 d
  have hprevFront' : i + 1 ≤ alpha d (t - 1) := by simpa [d] using hprevFront
  have hnowFront' : i + 2 ≤ alpha d t := by simpa [d] using hnowFront
  have hprevActiveBool : d2FlowCandidateActive d (t - 1) (i + 1) = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t - 1)
      (i := i + 1) (by omega)]
    have hactive' : active d (tfD2 d) (i + 1) (t - 1) := by
      simpa [d] using hprevActive
    simp [hactive']
  have hprevRoleCandidate :
      d2FlowCandidateRole d (t - 1) (i + 1) = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t - 1) (by omega)]
    simpa [d] using hprevRole
  have hparentInactive0 : d2FlowCandidateActive d (t - 1) i = false := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t - 1)
      (i := i) (by omega)]
    have hbelow : i < alpha d (t - 1) := by omega
    have hfalse : ¬ active d (tfD2 d) i (t - 1) := by
      intro ha
      have hf := (active_iff_frontiers (d := d) (tf := tfD2 d)
        (i := i) (t := t - 1) (by omega)).1 ha
      omega
    simp [hfalse]
  have hparentInactive1 : d2FlowCandidateActive d t i = false := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := i) (by omega)]
    have hbelow : i < alpha d t := by omega
    have hfalse : ¬ active d (tfD2 d) i t := by
      intro ha
      have hf := (active_iff_frontiers (d := d) (tf := tfD2 d)
        (i := i) (t := t) (by omega)).1 ha
      omega
    simp [hfalse]
  have hchildInactive1 : d2FlowCandidateActive d t (i + 1) = false := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := i + 1) (by omega)]
    have hbelow : i + 1 < alpha d t := by omega
    have hfalse : ¬ active d (tfD2 d) (i + 1) t := by
      intro ha
      have hf := (active_iff_frontiers (d := d) (tf := tfD2 d)
        (i := i + 1) (t := t) (by omega)).1 ha
      omega
    simp [hfalse]
  have hcorePath := d2FlowStageAffineCoreInputs_atPath
    (active := fun k => d2FlowCandidateActive d (t - 1) k)
    (role := fun k => d2FlowCandidateRole d (t - 1) k)
    (cap := fun k => d2FlowCandidateCapacity d k (t - 1))
    (tree := d2FlowCandidateRun d initial (t - 1)) path hcore
  simp only [Nat.zero_add] at hcorePath
  let parentPrev := d2FlowTreeAtPath i
    (d2FlowCandidateRun d initial (t - 1)) path
  cases hparentPrev : parentPrev with
  | node G low high children =>
      change d2FlowStageAffineCoreInputs
        (fun k => d2FlowCandidateActive d (t - 1) k)
        (fun k => d2FlowCandidateRole d (t - 1) k)
        (fun k => d2FlowCandidateCapacity d k (t - 1)) i parentPrev at hcorePath
      rw [hparentPrev] at hcorePath
      simp only [d2FlowStageAffineCoreInputs] at hcorePath
      rcases hcorePath with ⟨hchildrenCore, _⟩
      have hchildCore := hchildrenCore port
      have hchildRootZero : d2FlowTreeRootDeficit (children port) = 0 := by
        cases hchildTree : children port with
        | node cG clo chi cchildren =>
            rw [hchildTree] at hchildCore
            simp only [d2FlowStageAffineCoreInputs] at hchildCore
            rcases hchildCore with ⟨_, hchildLocal⟩
            simp only [hprevActiveBool, if_pos] at hchildLocal
            simp [hprevRoleCandidate] at hchildLocal
            rcases hchildLocal with ⟨_, hchildGzero⟩
            simp [d2FlowTreeRootDeficit, hchildGzero]
      have hchildPrevRole :
          d2FlowCandidateRole d (t - 1) (i + 1) = .topDesc :=
        hprevRoleCandidate
      have hprojectPrev : d2FlowTreeAtPath i
          (d2FlowCandidateStage d (t - 1)
            (d2FlowCandidateRun d initial (t - 1))) path =
          d2FlowStage (d2FlowCandidateActive d (t - 1))
            (d2FlowCandidateRole d (t - 1))
            (d2FlowCandidateQuota d (t - 1)) (h + 2) i
            (d2FlowTreeAtPath i (d2FlowCandidateRun d initial (t - 1)) path) := by
        have hinactive : ∀ k, k < i →
            d2FlowCandidateActive d (t - 1) k = false := by
          intro k hk
          rw [d2FlowCandidateActive_matches_schedule (d := d)
            (t := t - 1) (i := k) (by omega)]
          have hbelow : k < alpha d (t - 1) := by omega
          have hfalse : ¬ active d (tfD2 d) k (t - 1) := by
            intro ha
            have hf := (active_iff_frontiers (d := d) (tf := tfD2 d)
              (i := k) (t := t - 1) (by omega)).1 ha
            omega
          simp [hfalse]
        simpa [d2FlowCandidateStage, d] using
          d2FlowStage_path_eq_of_inactive_prefix
            (h := h + 2) (n := i) (i := 0)
            (active := d2FlowCandidateActive d (t - 1))
            (role := d2FlowCandidateRole d (t - 1))
            (quota := d2FlowCandidateQuota d (t - 1))
            (d2FlowCandidateRun d initial (t - 1)) path
            (by simpa using hinactive)
      have hprojectNow : d2FlowTreeAtPath i
          (d2FlowCandidateStage d t
            (d2FlowCandidateRun d initial t)) path =
          d2FlowStage (d2FlowCandidateActive d t)
            (d2FlowCandidateRole d t)
            (d2FlowCandidateQuota d t) (h + 2) i
            (d2FlowTreeAtPath i (d2FlowCandidateRun d initial t) path) := by
        have hinactive : ∀ k, k < i → d2FlowCandidateActive d t k = false := by
          intro k hk
          rw [d2FlowCandidateActive_matches_schedule (d := d)
            (t := t) (i := k) (by omega)]
          have hbelow : k < alpha d t := by omega
          have hfalse : ¬ active d (tfD2 d) k t := by
            intro ha
            have hf := (active_iff_frontiers (d := d) (tf := tfD2 d)
              (i := k) (t := t) (by omega)).1 ha
            omega
          simp [hfalse]
        simpa [d2FlowCandidateStage, d] using
          d2FlowStage_path_eq_of_inactive_prefix
            (h := h + 2) (n := i) (i := 0)
            (active := d2FlowCandidateActive d t)
            (role := d2FlowCandidateRole d t)
            (quota := d2FlowCandidateQuota d t)
            (d2FlowCandidateRun d initial t) path
            (by simpa using hinactive)
      have hrunT : d2FlowCandidateRun d initial t =
          d2FlowCandidateStage d (t - 1)
            (d2FlowCandidateRun d initial (t - 1)) := by
        rw [show t = (t - 1) + 1 by omega, d2FlowCandidateRun]
        rw [show (t - 1) + 1 - 1 = t - 1 by omega]
      have hrunNext : d2FlowCandidateRun d initial (t + 1) =
          d2FlowCandidateStage d t (d2FlowCandidateRun d initial t) := rfl
      have hparentT : d2FlowTreeAtPath i
          (d2FlowCandidateRun d initial t) path =
          d2FlowStage (d2FlowCandidateActive d (t - 1))
            (d2FlowCandidateRole d (t - 1))
            (d2FlowCandidateQuota d (t - 1)) (h + 2) i parentPrev := by
        rw [hrunT]
        simpa [d2FlowCandidateStage, d] using hprojectPrev
      have hparentNext : d2FlowTreeAtPath i
          (d2FlowCandidateRun d initial (t + 1)) path =
          d2FlowStage (d2FlowCandidateActive d t)
            (d2FlowCandidateRole d t)
            (d2FlowCandidateQuota d t) (h + 2) i
            (d2FlowTreeAtPath i (d2FlowCandidateRun d initial t) path) := by
        rw [hrunNext]
        simpa [d2FlowCandidateStage, d] using hprojectNow
      rw [hparentNext, hparentT]
      rw [hparentPrev]
      exact d2FlowStage_inactive_parent_two_stage_child_root_zero
        children
        (d2FlowCandidateActive d (t - 1)) (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d (t - 1)) (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d (t - 1)) (d2FlowCandidateQuota d t) port
        hparentInactive0 hparentInactive1 hprevActiveBool hchildPrevRole
        hchildInactive1 (by simpa [hparentPrev] using hchildRootZero)

theorem active_false_below_alpha_local {d tf j t : Nat}
    (ht : 2 ≤ t) (hbelow : j < alpha d t) :
    ¬ active d tf j t := by
  intro ha
  have hfront := (active_iff_frontiers (d := d) (tf := tf)
    (i := j) (t := t) ht).1 ha
  omega

/-- A candidate stage viewed below a fully inactive prefix is exactly the
local recursive stage at the selected node. -/
theorem d2FlowCandidateStage_path_eq_of_frontier_prefix
    {h i t : Nat} (hd : 7 ≤ h + 1 + i) (ht : 2 ≤ t)
    (hlower : i ≤ alpha (h + 1 + i) t)
    (tree : D2FlowTree (h + 1 + i)) (path : D2FlowPath i) :
    d2FlowTreeAtPath i
        (d2FlowCandidateStage (h + 1 + i) t tree) path =
      d2FlowStage (d2FlowCandidateActive (h + 1 + i) t)
        (d2FlowCandidateRole (h + 1 + i) t)
        (d2FlowCandidateQuota (h + 1 + i) t) (h + 1) i
        (d2FlowTreeAtPath i tree path) := by
  classical
  let d := h + 1 + i
  have hinactive : ∀ k, k < i → d2FlowCandidateActive d t k = false := by
    intro k hk
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := k) (by omega)]
    have hbelow : k < alpha d t := by
      change i ≤ alpha d t at hlower
      omega
    have hfalse : ¬ active d (tfD2 d) k t :=
      active_false_below_alpha_local ht hbelow
    simp [hfalse]
  simpa [d, d2FlowCandidateStage] using
    d2FlowStage_path_eq_of_inactive_prefix
      (h := h + 1) (n := i) (i := 0)
      (active := d2FlowCandidateActive d t)
      (role := d2FlowCandidateRole d t)
      (quota := d2FlowCandidateQuota d t)
      tree path (by simpa using hinactive)

theorem omega_prev_le_succ_local {t : Nat} (ht : 3 ≤ t) :
    omega t ≤ omega (t - 1) + 1 := by
  have hmn : (t - 1 + 4) / 3 ≤ (t + 4) / 3 := by omega
  have hnm : (t + 4) / 3 ≤ (t - 1 + 4) / 3 + 1 := by omega
  have hpar : (t - 1) % 2 ≠ t % 2 := by omega
  have hceil := ceilParity_step_reverse_le hmn hnm hpar
  have hnow : omega t = ceilParity ((t + 4) / 3) t := by
    simp [omega, show t ≠ 0 by omega, show t ≠ 1 by omega]
  have hprev : omega (t - 1) =
      ceilParity ((t - 1 + 4) / 3) (t - 1) := by
    simp [omega, show t - 1 ≠ 0 by omega, show t - 1 ≠ 1 by omega]
  rw [hnow, hprev]
  exact hceil

/-- An active top-descending sender has one of the three two-stage frontier
histories in `alpha_topDesc_two_step_patterns`. The last two histories have
an active top-descending parent at the intervening stage; the first has a
same-level top-descending predecessor. -/
theorem active_topDesc_two_stage_frontier_cases {d tf i t : Nat}
    (ht : 4 ≤ t) (ha : active d tf i t)
    (hr : d2ScheduleRole d i t = .topDesc) :
    (i = alpha d (t - 2) ∧ alpha d (t - 1) = i + 1) ∨
    (i = alpha d (t - 2) ∧ alpha d (t - 1) + 1 = i) ∨
    (alpha d (t - 2) + 2 = i ∧ alpha d (t - 1) + 1 = i) := by
  have hfront := (active_iff_frontiers (d := d) (tf := tf)
    (i := i) (t := t) (by omega)).1 ha
  have hi : i = alpha d t := by
    unfold d2ScheduleRole at hr
    split_ifs at hr <;> simp_all
  have hdesc : alpha d t < alpha d (t + 1) := by
    unfold d2ScheduleRole at hr
    simp only [if_pos hi] at hr
    split_ifs at hr <;> simp_all
  obtain ⟨_, hpatterns⟩ :=
    alpha_topDesc_two_step_patterns (d := d) ht hdesc
  subst i
  rcases hpatterns with hfirst | hrest
  · exact Or.inl ⟨by omega, hfirst.2⟩
  · rcases hrest with hsecond | hthird
    · exact Or.inr (Or.inl ⟨by omega, hsecond.2⟩)
    · exact Or.inr (Or.inr ⟨by omega, hthird.2⟩)

/-- In the two predecessor patterns where the top frontier is at `i-1` at
the intervening stage, that node is an active top-descending parent. -/
theorem active_topDesc_intervening_parent {d tf i t : Nat}
    (ht : 4 ≤ t) (ha : active d tf i t)
    (hr : d2ScheduleRole d i t = .topDesc)
    (hprev : alpha d (t - 1) + 1 = i) :
    active d tf (i - 1) (t - 1) ∧
      d2ScheduleRole d (i - 1) (t - 1) = .topDesc := by
  have hfront := (active_iff_frontiers (d := d) (tf := tf)
    (i := i) (t := t) (by omega)).1 ha
  have htop : i = alpha d t := by
    unfold d2ScheduleRole at hr
    split_ifs at hr <;> simp_all
  have hparentEq : i - 1 = alpha d (t - 1) := by omega
  have hpar : (i - 1) % 2 = (t - 1) % 2 := by
    have h := hfront.2.2.2
    omega
  have hupper := omega_prev_le_succ_local (t := t) (by omega)
  have hactiveParent : active d tf (i - 1) (t - 1) := by
    apply (active_iff_frontiers (d := d) (tf := tf)
      (i := i - 1) (t := t - 1) (by omega)).2
    refine ⟨by omega, ?_, ?_, hpar⟩
    · rw [hparentEq]
    · have hparentUpper : i - 1 ≤ omega (t - 1) := by omega
      exact hparentUpper
  have hmove : alpha d (t - 1) < alpha d ((t - 1) + 1) := by
    rw [show t - 1 + 1 = t by omega]
    omega
  have hroleParent :
      d2ScheduleRole d (i - 1) (t - 1) = .topDesc := by
    simp [d2ScheduleRole, hparentEq, hmove]
  exact ⟨hactiveParent, hroleParent⟩

/-- Every active top-descending sender has one of the two zero-root sources:
the sender itself was top-descending two stages ago, or its parent is
top-descending at the intervening stage. -/
theorem active_topDesc_has_two_stage_reset_source {d i t : Nat}
    (hd : 7 ≤ d) (ht : 4 ≤ t)
    (ha : active d (tfD2 d) i t)
    (hr : d2ScheduleRole d i t = .topDesc) :
    (active d (tfD2 d) (i - 1) (t - 1) ∧
        d2ScheduleRole d (i - 1) (t - 1) = .topDesc ∧ 1 ≤ i) ∨
    (active d (tfD2 d) i (t - 2) ∧
        d2ScheduleRole d i (t - 2) = .topDesc ∧
        i = alpha d (t - 2) ∧ alpha d (t - 1) = i + 1) := by
  have hcases := active_topDesc_two_stage_frontier_cases ht ha hr
  rcases hcases with hfirst | hrest
  · right
    have hfront := (active_iff_frontiers (d := d) (tf := tfD2 d)
      (i := i) (t := t) (by omega)).1 ha
    have htime : t - 2 < tfD2 d := by omega
    have hgap := alpha_gap_before_tf hd (by omega) htime
    have hlevel : alpha d (t - 2) + 1 ≤ (t - 2 + 4) / 3 := hgap
    have homega : (t - 2 + 4) / 3 ≤ omega (t - 2) := by
      have hge : 2 ≤ t - 2 := by omega
      have ht0 : t - 2 ≠ 0 := by omega
      have ht1 : t - 2 ≠ 1 := by omega
      simp only [omega, if_neg ht0, if_neg ht1]
      exact (ceilParity_bounds ((t - 2 + 4) / 3) (t - 2)).1
    have hpar : i % 2 = (t - 2) % 2 := by
      have h := hfront.2.2.2
      omega
    have hpriorActive : active d (tfD2 d) i (t - 2) := by
      apply (active_iff_frontiers (d := d) (tf := tfD2 d)
        (i := i) (t := t - 2) (by omega)).2
      refine ⟨by omega, ?_, ?_, hpar⟩
      · rw [hfirst.1]
      · have : i ≤ omega (t - 2) := by omega
        exact this
    have hmove : alpha d (t - 2) < alpha d (t - 1) := by
      omega
    have hmove' : alpha d (t - 2) < alpha d ((t - 2) + 1) := by
      simpa [show t - 2 + 1 = t - 1 by omega] using hmove
    have hpriorRole :
        d2ScheduleRole d i (t - 2) = .topDesc := by
      simp [d2ScheduleRole, hfirst.1, hmove']
    exact ⟨hpriorActive, hpriorRole, hfirst.1, hfirst.2⟩
  · rcases hrest with hsecond | hthird
    · rcases active_topDesc_intervening_parent ht ha hr hsecond.2 with
        ⟨hparentActive, hparentRole⟩
      exact Or.inl ⟨hparentActive, hparentRole, by omega⟩
    · rcases active_topDesc_intervening_parent ht ha hr hthird.2 with
        ⟨hparentActive, hparentRole⟩
      exact Or.inl ⟨hparentActive, hparentRole, by omega⟩

/-- If the same sender was top-descending two stages earlier, its zero-root
contract survives the inactive intervening stage in the actual candidate
run. The inactive ancestor prefix lets the path reduce to the local two
recursive stages. -/
theorem d2FlowCandidateRun_priorTopDesc_root_zero_after_inactive_stage
    {h i t : Nat} (hd : 7 ≤ h + 1 + i) (ht : 4 ≤ t)
    (hprevFront : i = alpha (h + 1 + i) (t - 2))
    (hinterFront : i + 1 ≤ alpha (h + 1 + i) (t - 1))
    (hprevActive : active (h + 1 + i) (tfD2 (h + 1 + i)) i (t - 2))
    (hprevRole : d2ScheduleRole (h + 1 + i) i (t - 2) = .topDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateRole (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k (t - 2)) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2)))
    (path : D2FlowPath i) :
    d2FlowTreeRootDeficit
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 1 + i)
          (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) = 0 := by
  classical
  let d := h + 1 + i
  have hprevFront' : i = alpha d (t - 2) := by
    simpa [d] using hprevFront
  have hinterFront' : i + 1 ≤ alpha d (t - 1) := by
    simpa [d] using hinterFront
  have hprevActiveBool : d2FlowCandidateActive d (t - 2) i = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t - 2)
      (i := i) (by omega)]
    have hprevActive' : active d (tfD2 d) i (t - 2) := by
      simpa [d] using hprevActive
    simp [hprevActive']
  have hinterActiveBool : d2FlowCandidateActive d (t - 1) i = false := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t - 1)
      (i := i) (by omega)]
    have hnot : ¬ active d (tfD2 d) i (t - 1) := by
      intro hactive
      have hfront := (active_iff_frontiers (d := d) (tf := tfD2 d)
        (i := i) (t := t - 1) (by omega)).1 hactive
      change i + 1 ≤ alpha d (t - 1) at hinterFront'
      omega
    simp [hnot]
  have hprevRoleCandidate :
      d2FlowCandidateRole d (t - 2) i = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t - 2) (by omega)]
    exact hprevRole
  have hcorePath := d2FlowStageAffineCoreInputs_atPath
    (active := fun k => d2FlowCandidateActive d (t - 2) k)
    (role := fun k => d2FlowCandidateRole d (t - 2) k)
    (cap := fun k => d2FlowCandidateCapacity d k (t - 2))
    (tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2))
    path hcore
  simp only [Nat.zero_add] at hcorePath
  let prior := d2FlowTreeAtPath i
    (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2)) path
  cases hprior : prior with
  | node G low high children =>
      have hlocal := hcorePath
      change d2FlowStageAffineCoreInputs
        (fun k => d2FlowCandidateActive d (t - 2) k)
        (fun k => d2FlowCandidateRole d (t - 2) k)
        (fun k => d2FlowCandidateCapacity d k (t - 2)) i prior at hlocal
      rw [hprior] at hlocal
      simp only [d2FlowStageAffineCoreInputs, hprevActiveBool,
        if_pos] at hlocal
      rcases hlocal with ⟨_, hlocal⟩
      simp [hprevRoleCandidate] at hlocal
      rcases hlocal with ⟨_, hGzero⟩
      have hfirstRoot :
          d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d (t - 2))
              (d2FlowCandidateRole d (t - 2))
              (d2FlowCandidateQuota d (t - 2)) (h + 1) i
              (.node G low high children)) = 0 := by
        rw [d2FlowStage_active_node_deficit children hprevActiveBool]
        rw [hprevRoleCandidate, hGzero]
        rfl
      have hfirstFront : i ≤ alpha d (t - 2) := by omega
      have hsecondFront : i ≤ alpha d (t - 1) := by
        omega
      have hprojectFirst :=
        d2FlowCandidateStage_path_eq_of_frontier_prefix
        (h := h) (i := i) (t := t - 2) (by omega) (by omega)
          hfirstFront
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2)) path
      have hprojectSecond :=
        d2FlowCandidateStage_path_eq_of_frontier_prefix
        (h := h) (i := i) (t := t - 1) (by omega) (by omega)
          hsecondFront
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path
      have hrunPrev :
          d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1) =
            d2FlowCandidateStage d (t - 2)
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2)) := by
        rw [show t - 1 = (t - 2) + 1 by omega, d2FlowCandidateRun]
      have hrunNow :
          d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t =
            d2FlowCandidateStage d (t - 1)
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) := by
        rw [show t = (t - 1) + 1 by omega, d2FlowCandidateRun]
        have hidx : (t - 1) + 1 - 1 = t - 1 := by omega
        rw [hidx]
      have hpathPrev :
          d2FlowTreeAtPath i
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path =
            d2FlowStage (d2FlowCandidateActive d (t - 2))
              (d2FlowCandidateRole d (t - 2))
              (d2FlowCandidateQuota d (t - 2)) (h + 1) i prior := by
        rw [hrunPrev]
        simpa [d2FlowCandidateStage, d] using hprojectFirst
      have hpathNow :
          d2FlowTreeAtPath i
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path =
            d2FlowStage (d2FlowCandidateActive d (t - 1))
              (d2FlowCandidateRole d (t - 1))
              (d2FlowCandidateQuota d (t - 1)) (h + 1) i
              (d2FlowTreeAtPath i
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path) := by
        rw [hrunNow]
        simpa [d2FlowCandidateStage, d] using hprojectSecond
      have hrootPrev : d2FlowTreeRootDeficit
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path) = 0 := by
        rw [hpathPrev, hprior]
        exact hfirstRoot
      rw [hpathNow]
      calc
        d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d (t - 1))
              (d2FlowCandidateRole d (t - 1))
              (d2FlowCandidateQuota d (t - 1)) (h + 1) i
              (d2FlowTreeAtPath i
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path)) =
            d2FlowTreeRootDeficit
              (d2FlowTreeAtPath i
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)) path) := by
          exact d2FlowStage_root_deficit_of_inactive
            (active := d2FlowCandidateActive d (t - 1))
            (role := d2FlowCandidateRole d (t - 1))
            (quota := d2FlowCandidateQuota d (t - 1))
            (i := i) _ hinterActiveBool
        _ = 0 := hrootPrev

/-- Every active top-descending node has zero root deficit in the actual
candidate run, provided the affine core contract holds two snapshots earlier.
The schedule splits between an immediate parent reset and the repeated
same-level top-descending history. -/
theorem d2FlowCandidateRun_active_topDesc_root_zero_of_prior_core
    {h i t : Nat} (hd : 7 ≤ h + 1 + i) (ht : 4 ≤ t)
    (ha : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hr : d2ScheduleRole (h + 1 + i) i t = .topDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateRole (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k (t - 2)) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2)))
    (path : D2FlowPath i) :
    d2FlowTreeRootDeficit
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 1 + i)
          (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) = 0 := by
  classical
  let d := h + 1 + i
  rcases active_topDesc_has_two_stage_reset_source hd ht ha hr with
    ⟨hparentActive, hparentRole, hi⟩ |
    ⟨hpriorActive, hpriorRole, hpriorFront, hinterFront⟩
  · have hparentActiveBool : d2FlowCandidateActive d (t - 1) (i - 1) = true := by
      rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t - 1)
        (i := i - 1) (by omega)]
      have hparentActive' : active d (tfD2 d) (i - 1) (t - 1) := by
        simpa [d] using hparentActive
      simp [hparentActive']
    have hparentRoleCandidate :
        d2FlowCandidateRole d (t - 1) (i - 1) = .topDesc := by
      rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t - 1) (by omega)]
      exact hparentRole
    simpa [show t - 1 + 1 = t by omega] using
      d2FlowCandidateRun_parent_topDesc_root_zero_at_path
        (h := h) (i := i) (t := t - 1) hi path
        (by simpa [d] using hparentActiveBool)
        (by simpa [d] using hparentRoleCandidate)
  · exact d2FlowCandidateRun_priorTopDesc_root_zero_after_inactive_stage
      (h := h) (i := i) (t := t) hd ht hpriorFront
      (by omega) hpriorActive hpriorRole hcore path

/-- A top-descending child has zero root at the next snapshot. The schedule's
two-stage split either gives an immediately resetting top-descending parent,
or the same child as a top-descending sender two snapshots earlier; the latter
uses the prior-snapshot affine core contract. -/
theorem d2FlowCandidateRun_active_topDesc_child_root_zero_of_prior_core
    {h i t : Nat} (hd : 7 ≤ h + 2 + i) (ht : 3 ≤ t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i))
      (i + 1) (t + 1))
    (hchildRole : d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .topDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1))) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) = 0 := by
  classical
  let d := h + 2 + i
  rcases active_topDesc_has_two_stage_reset_source
      (d := d) (i := i + 1) (t := t + 1) hd (by omega)
      hchildActive hchildRole with
    ⟨hparentActive, hparentRole, hi⟩ | ⟨hpriorActive, hpriorRole,
      hpriorFront, hinterFront⟩
  · have hparentActiveBool : d2FlowCandidateActive d t i = true := by
      rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
        (i := i) (by omega)]
      have hactive' : active d (tfD2 d) i t := by
        simpa [d] using hparentActive
      simp [hactive']
    have hparentRoleCandidate : d2FlowCandidateRole d t i = .topDesc := by
      rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t) (by omega)]
      exact hparentRole
    cases hnode : d2FlowTreeAtPath i
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path with
    | node G low high children =>
        have hzero := d2FlowCandidateRun_topDesc_parent_child_zero_at_path
          (h := h + 1) (i := i) (t := t) path children hnode
          (by simpa [d] using hparentActiveBool)
          (by simpa [d] using hparentRoleCandidate) port
        simpa [d] using hzero
  · exact d2FlowCandidateRun_priorTopDesc_child_root_zero
      (h := h) (i := i) (t := t) hd (by omega) path port
      (by
        have htidx : t + 1 - 2 = t - 1 := by omega
        rw [htidx] at hpriorFront
        exact le_of_eq hpriorFront)
      (by
        have htidx : t + 1 - 1 = t := by omega
        rw [htidx] at hinterFront
        exact le_of_eq hinterFront.symm)
      hpriorActive hpriorRole hcore

/-- Role-complete active-child transition interface. Every active child at the
next snapshot either has the exact zero-root contract required by `topDesc`,
or the affine profile required by the ordinary roles. The two branches use
the appropriate prior core snapshots. -/
theorem d2FlowCandidateRun_active_child_zero_or_affine_profile
    {h i t : Nat} (hd : 7 ≤ h + 2 + i) (ht : 3 ≤ t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i))
      (i + 1) (t + 1))
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1)))
    (hcoreNow : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) t k)
      (fun k => d2FlowCandidateRole (h + 2 + i) t k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k t) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) t)) :
    (d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .topDesc ∧
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 2 + i)
              (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) = 0) ∨
    (d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) ≠ .topDesc ∧
      8192 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 2 + i)
              (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) + 7 ≤
      15 * d2FlowCandidateCapacity (h + 2 + i) (i + 1) (t + 1)) := by
  classical
  let d := h + 2 + i
  by_cases htop : d2ScheduleRole d (i + 1) (t + 1) = .topDesc
  · left
    refine ⟨by simpa [d] using htop, ?_⟩
    have hzero := d2FlowCandidateRun_active_topDesc_child_root_zero_of_prior_core
      (h := h) (i := i) (t := t) hd ht path port hchildActive
      (by simpa [d] using htop) (by simpa [d] using hcorePrev)
    simpa [d] using hzero
  · right
    refine ⟨htop, ?_⟩
    have hprofile :=
      d2FlowCandidateRun_core_provider_affine_profile_at_active_nonTopDesc_child
        (h := h + 1) (i := i) (t := t) (G := 0) (low := 0) (high := 0)
        (by simpa [d] using hd) (by omega)
        path port hchildActive htop (by simpa [d] using hcoreNow)
    simpa [d] using hprofile

/-- Role-shaped root obligations for an active child at the next snapshot.
This matches the local cases in the affine core: exact zero for `topDesc` and
`topRise`, no additional root condition for `botRise`, and the affine profile
for `mid` and `botDesc`. -/
theorem d2FlowCandidateRun_active_child_role_root_contract
    {h i t : Nat} (hd : 7 ≤ h + 2 + i) (ht : 3 ≤ t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i))
      (i + 1) (t + 1))
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1)))
    (hcoreNow : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) t k)
      (fun k => d2FlowCandidateRole (h + 2 + i) t k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k t) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) t)) :
    let root := d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port)
    match d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) with
    | .topDesc => root = 0
    | .botRise => True
    | .topRise => root = 0 ∧
        8192 * root + 7 ≤ 15 * d2FlowCandidateCapacity
          (h + 2 + i) (i + 1) (t + 1)
    | .mid | .botDesc =>
        8192 * root + 7 ≤ 15 * d2FlowCandidateCapacity
          (h + 2 + i) (i + 1) (t + 1) := by
  classical
  let d := h + 2 + i
  let root := d2FlowTreeRootDeficit
    (d2FlowTreeChild
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) path) port)
  have hprofile (hrole : d2ScheduleRole d (i + 1) (t + 1) ≠ .topDesc) :
      8192 * root + 7 ≤ 15 * d2FlowCandidateCapacity d (i + 1) (t + 1) := by
    have hresult :=
      d2FlowCandidateRun_core_provider_affine_profile_at_active_nonTopDesc_child
        (h := h + 1) (i := i) (t := t) (G := 0) (low := 0) (high := 0)
        (by simpa [d] using hd) (by omega) path port hchildActive
        (by simpa [d] using hrole) (by simpa [d] using hcoreNow)
    simpa [root, d] using hresult
  change match d2ScheduleRole d (i + 1) (t + 1) with
    | .topDesc => root = 0
    | .botRise => True
    | .topRise => root = 0 ∧
        8192 * root + 7 ≤ 15 * d2FlowCandidateCapacity d (i + 1) (t + 1)
    | .mid | .botDesc =>
        8192 * root + 7 ≤ 15 * d2FlowCandidateCapacity d (i + 1) (t + 1)
  cases hrole : d2ScheduleRole d (i + 1) (t + 1) with
  | topDesc =>
      have hzero := d2FlowCandidateRun_active_topDesc_child_root_zero_of_prior_core
        (h := h) (i := i) (t := t) hd ht path port hchildActive
        (by simpa [d] using hrole) (by simpa [d] using hcorePrev)
      simpa [hrole, root, d] using hzero
  | botRise => trivial
  | topRise =>
      have hzero := d2FlowCandidateRun_active_topRise_root_zero_at_any_parent_path
        (h := h + 1) (i := i) (t := t) (by simpa [d] using hd) (by omega)
        path hchildActive (by simpa [d] using hrole) port
      have hnotTD : d2ScheduleRole d (i + 1) (t + 1) ≠ .topDesc := by
        rw [hrole]
        decide
      refine ⟨?_, hprofile hnotTD⟩
      simpa [root, d] using hzero
  | mid => exact hprofile (by simp [hrole])
  | botDesc => exact hprofile (by simp [hrole])

/-- The role/profile transition also supplies the balance field required by
the affine core. A top-descending child has zero root from the two-stage
history and is balanced by the next invariant. Every other active child has a
top-descending or ordinary active parent, both of which write balanced data. -/
theorem d2FlowCandidateRun_active_child_balanced_of_prior_core
    {h i t : Nat} (hd : 7 ≤ h + 2 + i) (ht : 3 ≤ t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i))
      (i + 1) (t + 1))
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1)))
    (hinvNext : d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1))) :
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port)).2.1 +
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port)).2.2 =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) := by
  classical
  let d := h + 2 + i
  let child := d2FlowTreeChild
    (d2FlowTreeAtPath i
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) path) port
  have hzeroBalance (hzero : d2FlowTreeRootDeficit child = 0) :
      (d2FlowTreeRootData child).2.1 + (d2FlowTreeRootData child).2.2 =
        d2FlowTreeRootDeficit child := by
    cases hnode : child with
    | node G low high children =>
        have hbal := d2FlowCandidateRun_zero_child_balanced_of_inv
          (path := path) (port := port) (children := children)
          (by simpa [child] using hnode) (by simpa [d] using hinvNext)
          (by simpa [child] using hzero)
        simpa [hnode, d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbal
  by_cases htop : d2ScheduleRole d (i + 1) (t + 1) = .topDesc
  · have hzero := d2FlowCandidateRun_active_topDesc_child_root_zero_of_prior_core
      (h := h) (i := i) (t := t) (by simpa [d] using hd) ht path port
      hchildActive (by simpa [d] using htop) (by simpa [d] using hcorePrev)
    exact hzeroBalance (by simpa [child] using hzero)
  · have hparentCases := active_nonTop_parent_role_cases
      (d := d) (tf := tfD2 d) (i := i + 1) (t := t + 1)
      (by omega) (by omega) hchildActive htop
    have hparentActive : d2FlowCandidateActive d t i = true := by
      rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
        (i := i) (by omega)]
      exact decide_eq_true hparentCases.1
    have hparentRoles : d2FlowCandidateRole d t i = .topDesc ∨
        d2FlowCandidateRole d t i = .topRise ∨
        d2FlowCandidateRole d t i = .mid ∨
        d2FlowCandidateRole d t i = .botDesc := by
      rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t)
        (i := i) (by omega)]
      exact hparentCases.2
    cases hnode : d2FlowTreeAtPath i
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path with
    | node G low high children =>
        rcases hparentRoles with hreset | hregular
        · have hzero := d2FlowCandidateRun_topDesc_parent_child_zero_at_path
            (h := h + 1) (i := i) (t := t) path children hnode
            (by simpa [d] using hparentActive)
            (by simpa [d] using hreset) port
          exact hzeroBalance (by simpa [child, d] using hzero)
        · rcases hregular with hrise | hregular
          · exact d2FlowCandidateRun_regular_parent_child_balanced
              (h := h) (i := i) (t := t) path children hnode hparentActive
              (Or.inl hrise) port
          · rcases hregular with hmid | hbot
            · exact d2FlowCandidateRun_regular_parent_child_balanced
                (h := h) (i := i) (t := t) path children hnode hparentActive
                (Or.inr (Or.inl hmid)) port
            · exact d2FlowCandidateRun_regular_parent_child_balanced
                (h := h) (i := i) (t := t) path children hnode hparentActive
                (Or.inr (Or.inr hbot)) port

end Chvatal.D2Reserve
