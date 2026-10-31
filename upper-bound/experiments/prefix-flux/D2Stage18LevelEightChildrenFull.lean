import D2Stage18LevelEightInputs

namespace Chvatal.D2Reserve

/-- Through Run 18, every actual level-eight sender retains its native full
level-nine children. The level-eight sender itself is inactive during these
18 updates, and all deeper levels are inactive as well. -/
theorem d2FlowCandidateRun_stage18_levelEight_children_full
    (childDepth : Nat) (hd : 7 <= childDepth)
    (path : D2FlowPath 8) (u : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeAtPath 8
        (d2FlowCandidateRun (childDepth + 9)
          (d2FlowTreeInitial 8192 (childDepth + 9)) 18) path) u =
      d2FlowTreeFull 8192 childDepth := by
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let active := d2FlowCandidateRunActive d
  let role := d2FlowCandidateRunRole d
  let quota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let context := d2FlowTreePathContext 8 initial path 0 active role quota overwrite
  have hinitial : d2FlowTreeAtPath 8 initial path =
      d2FlowTreeFull 8192 (childDepth + 1) := by
    cases path with
    | cons first tail =>
        change d2FlowTreeAtPath 7
          (d2FlowTreeFull 8192 (childDepth + 8)) tail =
            d2FlowTreeFull 8192 (childDepth + 1)
        convert d2FlowTreeFull_atPath (h := childDepth + 1) (n := 7)
          8192 tail using 1 <;> congr 1 <;> omega
  have hcontextInitial : context.initial =
      d2FlowTreeFull 8192 (childDepth + 1) := by
    rw [d2FlowTreePathContext_initial_eq_atPath]
    exact hinitial
  have hcontextLevel : context.level = 8 := by
    rw [d2FlowTreePathContext_level_eq]
  have hpath := d2FlowCandidateRun_path_as_history
    (h := childDepth + 1) (n := 8) (initial := initial)
    (path := path) (step := 18)
  rw [show d2FlowCandidateRun d initial 18 =
      d2FlowCandidateRun (childDepth + 9) initial 18 by rfl] at hpath
  rw [hpath, d2FlowTreePathHistory_eq_context_run]
  change d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites context.initial context.level
        active role quota context.overwrite 18) u =
    d2FlowTreeFull 8192 childDepth
  rw [hcontextLevel, hcontextInitial]
  have hrun : d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites
        (d2FlowTreeFull 8192 (childDepth + 1)) 8 active role quota
        context.overwrite 18) u =
      d2FlowTreeChild (d2FlowTreeFull 8192 (childDepth + 1)) u := by
    apply d2FlowTreeRun_child_eq_of_inactive_or_botRise
      (active := active) (role := role) (quota := quota)
      (overwrite := context.overwrite) (steps := 18) (i := 8)
    · intro k hk
      left
      change d2FlowCandidateActive d k 8 = false
      by_cases hk0 : k = 0
      · subst k
        simp [d2FlowCandidateActive] <;> omega
      · by_cases hk1 : k = 1
        · subst k
          simp [d2FlowCandidateActive] <;> omega
        · unfold d2FlowCandidateActive
          simp only [if_neg hk0, if_neg hk1]
          apply Bool.eq_false_of_not_eq_true
          intro hv
          have hp := of_decide_eq_true hv
          dsimp [tfD2] at hp
          omega
    · intro k hk q hq
      change d2FlowCandidateActive d k q = false
      by_cases hk0 : k = 0
      · subst k
        simp [d2FlowCandidateActive] <;> omega
      · by_cases hk1 : k = 1
        · subst k
          simp [d2FlowCandidateActive] <;> omega
        · unfold d2FlowCandidateActive
          simp only [if_neg hk0, if_neg hk1]
          apply Bool.eq_false_of_not_eq_true
          intro hv
          have hp := of_decide_eq_true hv
          dsimp [tfD2] at hp
          omega
  rw [hrun]
  simp [d2FlowTreeFull, d2FlowTreeChild]

end Chvatal.D2Reserve
