import D2Stage18Frontier
import D2Stage17LevelOneStartupInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- Push a stage through eight child projections, leaving the final child
action at its level-seven ancestor. -/
theorem d2FlowStage_path8_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 8))
    (j k m l q r s u : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowStage active role quota (h + 8) i tree) j) k) m) l) q) r) s) u =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 7)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild tree j) k) m) l) q) r) s)) u := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

private theorem d2FlowStageInvInputs_inactive_tail
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    (i : Nat) : ∀ {h : Nat} (tree : D2FlowTree h),
      (∀ t, i ≤ t → active t = false) →
      d2FlowStageInvInputs scale active role quota cap i tree := by
  intro h
  induction h generalizing i with
  | zero =>
      intro tree _
      cases tree
      simp [d2FlowStageInvInputs]
  | succ h ih =>
      intro tree hinactive
      cases tree with
      | node G low high children =>
          have hfalse : active i = false := hinactive i (Nat.le_refl i)
          simp only [d2FlowStageInvInputs, hfalse]
          refine ⟨?_, trivial⟩
          intro j
          exact ih (i + 1) (children j) (by
            intro t ht
            exact hinactive t (by omega))

/-- The Stage-17 level-seven bottom-descending cut writes balanced root data
into each level-eight child. Thus every actual Stage-18 level-eight sender
has the balance field needed by its bottom-rise branch. -/
theorem d2FlowCandidateRun_stage18_levelEight_balanced
    (height : Nat) (hd : 6 <= height)
    (j k m l q r s u : Fin 8) :
    let d := height + 8
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run18 j) k) m) l) q) r) s) u
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun (height + 8) (d2FlowTreeInitial 8192 (height + 8)) 18
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run17 j) k) m) l) q) r) s
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 17 7 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inr (Or.inr rfl))
  have hrole : d2FlowCandidateRole d 17 7 = .botDesc :=
    d2FlowCandidateRole_stage17_bottom hd14
  have hlocal :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 1) 7 parent) u)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 1) 7 parent) u)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 1) 7 parent) u) := by
    cases hp : parent with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive
          (Or.inr (Or.inr hrole)) u
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  change (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run18 j) k) m) l) q) r) s) u)).2.1 +
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run18 j) k) m) l) q) r) s) u)).2.2 =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run18 j) k) m) l) q) r) s) u)
  rw [hrun18]
  simp only [d2FlowCandidateStage]
  rw [d2FlowStage_path8_projection]
  simpa [parent, d, initial] using hlocal

/-- Below the Stage-18 bottom boundary all levels are inactive, so their
recursive input predicate follows just from the tree shape. -/
theorem d2FlowCandidateRun_stage18_levelEight_inputs
    (height : Nat) (hd : 6 <= height)
    (j k m l q r s u : Fin 8) :
    let d := height + 8
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run18 j) k) m) l) q) r) s) u
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 8 tree := by
  obtain ⟨h, rfl⟩ : ∃ h, height = h + 1 := ⟨height - 1, by omega⟩
  let d := (h + 1) + 8
  let run18 : D2FlowTree ((h + 1) + 8) :=
    d2FlowCandidateRun ((h + 1) + 8)
      (d2FlowTreeInitial 8192 ((h + 1) + 8)) 18
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) r) s) u
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 18 8 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15
    · simp [hsmall]
    · simp [hsmall]
  have hrole : d2FlowCandidateRole d 18 8 = .botRise :=
    d2FlowCandidateRole_stage18_bottom hd14
  have hchildren : ∀ t : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
        (d2FlowCandidateQuota d 18)
        (fun x => d2FlowCandidateCapacity d x 18) 9
        (d2FlowTreeChild tree t) := by
    intro t
    apply d2FlowStageInvInputs_inactive_tail
      (scale := 8192) (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (cap := fun x => d2FlowCandidateCapacity d x 18) 9
    · intro i hi
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hlevels := (d2FlowCandidateActive_stage18_iff hd14).mp ht
      by_cases hsmall : d <= 15 <;> simp [hsmall] at hlevels <;> omega
  have hbalance := d2FlowCandidateRun_stage18_levelEight_balanced
    (h + 1) (by omega) j k m l q r s u
  dsimp [d, run18, tree] at hbalance
  cases htree : tree with
  | node G low high children =>
      dsimp [tree] at htree
      rw [htree] at hbalance
      have hb : low + high = G := by
        simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
      have hchildren' : ∀ t : Fin 8,
          d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
            (d2FlowCandidateQuota d 18)
            (fun x => d2FlowCandidateCapacity d x 18) 9 (children t) := by
        intro t
        simpa [tree, htree, d] using hchildren t
      dsimp [tree]
      rw [htree]
      simp [d2FlowStageInvInputs, d, hactive, hrole]
      exact ⟨(by simpa [d] using hchildren'), hb⟩

end Chvatal.D2Reserve
