import D2Stage15LevelSevenChildPreserved

namespace Chvatal.D2Reserve

/-- After Stage 15, every actual level-seven node still has its native full
level-eight children: the schedule preserves the children, and those
children were full in the initial tree. -/
theorem d2FlowCandidateRun_stage15_levelSeven_children_full
    (height : Nat) (hh : 6 <= height)
    (path : D2FlowPath 7) (u : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeAtPath 7
        (d2FlowCandidateRun (height + 8)
          (d2FlowTreeInitial 8192 (height + 8)) 15) path) u =
      d2FlowTreeFull 8192 height := by
  have hinitial :
      d2FlowTreeAtPath 7 (d2FlowTreeInitial 8192 (height + 8)) path =
        d2FlowTreeFull 8192 (height + 1) := by
    cases path with
    | cons first tail =>
        change d2FlowTreeAtPath 6
          (d2FlowTreeFull 8192 (height + 7)) tail =
            d2FlowTreeFull 8192 (height + 1)
        convert d2FlowTreeFull_atPath (h := height + 1) (n := 6)
          8192 tail using 1 <;> congr 1 <;> omega
  calc
    d2FlowTreeChild
        (d2FlowTreeAtPath 7
          (d2FlowCandidateRun (height + 8)
            (d2FlowTreeInitial 8192 (height + 8)) 15) path) u =
      d2FlowTreeChild
        (d2FlowTreeAtPath 7 (d2FlowTreeInitial 8192 (height + 8)) path) u :=
      d2FlowCandidateRun_stage15_levelSeven_child_preserved
        height hh (d2FlowTreeInitial 8192 (height + 8)) path u
    _ = d2FlowTreeFull 8192 height := by
      rw [hinitial]
      simp [d2FlowTreeFull, d2FlowTreeChild]

end Chvatal.D2Reserve
