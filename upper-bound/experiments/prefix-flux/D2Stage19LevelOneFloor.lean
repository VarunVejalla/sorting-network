import D2Stage18LevelTwoLateInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- At depths at least seventeen, each level-two child below the Stage-19
level-one sender receives the Stage-18 level-two middle quota. -/
theorem d2FlowCandidateRun_stage19_levelOne_child_floor
    (childDepth : Nat) (hd : 8 <= childDepth) (j k : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    d2FlowCandidateQuota d 18 2 .mid <=
      d2FlowTreeRootDeficit (d2FlowTreeChild (d2FlowTreeChild run19 j) k) := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild run18 j
  let input := d2FlowTreeChild parent k
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hlate : 16 <= d := by dsimp [d]; omega
  have hfalse1 : d2FlowCandidateActive d 18 1 = false := by
    cases h : d2FlowCandidateActive d 18 1 with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage18_iff (i := 1) hd14).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hactive2 : d2FlowCandidateActive d 18 2 = true := by
    apply (d2FlowCandidateActive_stage18_iff (i := 2) hd14).2
    have hnotSmall : ¬ d <= 15 := by omega
    simp [hnotSmall]
  have hrole2 : d2FlowCandidateRole d 18 2 = .mid :=
    d2FlowCandidateRole_stage18_mid2 hlate
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have hproj :
      d2FlowTreeChild (d2FlowTreeChild run19 j) k =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 18)
          (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
          (childDepth + 8) 1 parent) k := by
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_child_child_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 7) (i := 0) run18 j k
  have hin := d2FlowCandidateRun_stage18_levelTwo_late_inputs
    (childDepth + 2) (by omega) j k
  have hin' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 2 input := by
    simpa [d, initial, run18, parent, input] using hin
  cases hp : parent with
  | node G1 low1 high1 children1 =>
      have hstep := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 18)
        (role := d2FlowCandidateRole d 18)
        (quota := d2FlowCandidateQuota d 18)
        (h := childDepth + 7) (i := 1) (G := G1)
        (low := low1) (high := high1) children1 hfalse1 k
      have hchildStage :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 8) 1 (.node G1 low1 high1 children1)) k =
          d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (childDepth + 7) 2 (children1 k) := by
        simpa using hstep
      have hlocal : d2FlowCandidateQuota d 18 2 .mid <=
          d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 7) 2 input) := by
        cases hi : input with
        | node G2 low2 high2 children2 =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 18)
              (role := d2FlowCandidateRole d 18)
              (quota := d2FlowCandidateQuota d 18)
              (h := childDepth + 6) (i := 2) (G := G2)
              (low := low2) (high := high2) children2 hactive2
            have hdef' : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 7) 2 input) =
                G2 + d2FlowCandidateQuota d 18 2 .mid := by
              simpa [hi, hrole2] using hdef
            rw [← hi, hdef']
            omega
      have hrootEq :
          d2FlowTreeRootDeficit (d2FlowTreeChild (d2FlowTreeChild run19 j) k) =
            d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 7) 2 input) := by
        calc
          _ = d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 8) 1 parent) k) := by
                exact congrArg d2FlowTreeRootDeficit hproj
          _ = d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 7) 2 input) := by
                simpa [parent, input, hp] using
                  congrArg d2FlowTreeRootDeficit hchildStage
      simpa [d, initial, run18, run19] using hrootEq.symm ▸ hlocal

end Chvatal.D2Reserve
