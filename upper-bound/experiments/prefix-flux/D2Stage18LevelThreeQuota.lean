import D2Stage18LevelTwoQuota

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- After Stage 17, each level-three child below a level-two sender carries
at least the Stage-17 level-three middle quota. The intervening level two is
inactive, so it preserves the level-three sender's root write. -/
theorem d2FlowCandidateRun_stage18_levelTwo_child_quota_floor
    (childDepth : Nat) (hd : 9 <= childDepth) (j k m : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    d2FlowCandidateQuota d 17 3 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let run18 := d2FlowCandidateRun d initial 18
  let parent := d2FlowTreeChild (d2FlowTreeChild run17 j) k
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run18 j) k) m
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive17_3 : d2FlowCandidateActive d 17 3 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inl rfl)
  have hrole17_3 : d2FlowCandidateRole d 17 3 = .mid :=
    d2FlowCandidateRole_stage17_mid3 hd14
  have hinactive17_2 : d2FlowCandidateActive d 17 2 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage17_iff hd14).mp ht
    omega
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 17)
        (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
        (childDepth + 5) 2 parent) m := by
    change d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run18 j) k) m = _
    rw [hrun18]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path3_projection
      (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (h := childDepth + 4) (i := 0) run17 j k m
  cases hnode : parent with
  | node G low high children =>
      have hchildEq : d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (childDepth + 5) 2 (.node G low high children)) m =
          d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (childDepth + 4) 3 (children m) := by
        exact d2FlowStage_inactive_child children hinactive17_2 m
      cases hchild : children m with
      | node G3 low3 high3 grandchildren =>
          have hdef := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 17)
            (role := d2FlowCandidateRole d 17)
            (quota := d2FlowCandidateQuota d 17)
            (h := childDepth + 3) (i := 3)
            (G := G3) (low := low3) (high := high3)
            grandchildren hactive17_3
          have hroot : d2FlowCandidateQuota d 17 3 .mid <=
              d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 17)
                  (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                  (childDepth + 4) 3 (.node G3 low3 high3 grandchildren)) := by
            rw [hdef, hrole17_3]
            simp
          have hrootTree : d2FlowTreeRootDeficit tree =
              d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 17)
                  (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                  (childDepth + 4) 3 (.node G3 low3 high3 grandchildren)) := by
            rw [htreeEq, hnode, hchildEq, hchild]
          simpa [d, initial, run17, run18, parent, tree] using
            hrootTree ▸ hroot

end Chvatal.D2Reserve
