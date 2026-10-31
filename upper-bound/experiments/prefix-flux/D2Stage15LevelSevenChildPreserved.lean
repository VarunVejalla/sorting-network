import D2Stage15LevelSevenPathHistory

namespace Chvatal.D2Reserve

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Through the first fifteen scheduled updates, every actual level-seven
node retains its immediate children. -/
theorem d2FlowCandidateRun_stage15_levelSeven_child_preserved
    (height : Nat) (hh : 6 <= height)
    (initial : D2FlowTree (height + 8))
    (path : D2FlowPath 7) (u : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeAtPath 7 (d2FlowCandidateRun (height + 8) initial 15) path) u =
    d2FlowTreeChild (d2FlowTreeAtPath 7 initial path) u := by
  let active := d2FlowCandidateRunActive (height + 1 + 7)
  let role := d2FlowCandidateRunRole (height + 1 + 7)
  let quota := d2FlowCandidateRunQuota (height + 1 + 7)
  let overwrite := d2FlowCandidateRunOverwrite (height + 1 + 7) initial
  let context := d2FlowTreePathContext 7 initial path 0 active role quota overwrite
  have hroot : ∀ k, k < 15 ->
      active k 7 = false \/
        (active k 7 = true ∧ role k 7 = .botRise) := by
    intro k hk
    left
    simpa only [active, d2FlowCandidateRunActive,
      show height + 8 = height + 1 + 7 by omega] using
      d2FlowCandidateActive_stageBefore15_levelSeven_false height k hk
  have hdeep : ∀ k, k < 15 -> ∀ q, 7 < q ->
      active k q = false := by
    intro k hk q hq
    simpa only [active, d2FlowCandidateRunActive,
      show height + 8 = height + 1 + 7 by omega] using
      d2FlowCandidateActive_stageBefore15_deeper_false height k hk q hq
  have hrun : d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites context.initial context.level
        active role quota context.overwrite 15) u =
      d2FlowTreeChild context.initial u := by
    have hlevel : context.level = 7 := by
      rw [d2FlowTreePathContext_level_eq]
    rw [hlevel]
    exact d2FlowTreeRun_child_eq_of_inactive_or_botRise
      (initial := context.initial) (active := active) (role := role)
      (quota := quota) (overwrite := context.overwrite)
      (steps := 15) (i := 7) hroot hdeep u
  calc
    d2FlowTreeChild
        (d2FlowTreeAtPath 7
          (d2FlowCandidateRun (height + 8) initial 15) path) u =
      d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites context.initial context.level
          active role quota context.overwrite 15) u := by
      rw [d2FlowCandidateRun_stage15_levelSeven_path_history height initial path]
    _ = d2FlowTreeChild context.initial u := hrun
    _ = d2FlowTreeChild (d2FlowTreeAtPath 7 initial path) u := by
      rw [← d2FlowTreePathContext_initial_eq_atPath]

end Chvatal.D2Reserve
