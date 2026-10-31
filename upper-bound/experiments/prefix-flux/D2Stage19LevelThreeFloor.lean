import D2Stage18LevelFourInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Every level-four child below a level-three sender in Run 19 has received
the Stage-18 level-four middle quota. -/
theorem d2FlowCandidateRun_stage19_levelThree_child_floor
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    d2FlowCandidateQuota d 18 4 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run19 j) k) m) l) := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run18 j) k) m
  let input := d2FlowTreeChild parent l
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse3 : d2FlowCandidateActive d 18 3 = false := by
    cases h : d2FlowCandidateActive d 18 3 with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage18_iff hd14).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hactive4 : d2FlowCandidateActive d 18 4 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole4 : d2FlowCandidateRole d 18 4 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 4 (Or.inl rfl)
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have hproj :
      d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run19 j) k) m) l =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 18)
          (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
          (childDepth + 6) 3 parent) l := by
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path4_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 5) (i := 0) run18 j k m l
  have hin := d2FlowCandidateRun_stage18_levelFour_inputs
    (childDepth + 2) (by omega) j k m l
  have hin' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 4 input := by
    simpa [d, initial, run18, parent, input] using hin
  cases hp : parent with
  | node G3 low3 high3 children3 =>
      have hstep := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 18)
        (role := d2FlowCandidateRole d 18)
        (quota := d2FlowCandidateQuota d 18)
        (h := childDepth + 5) (i := 3) (G := G3)
        (low := low3) (high := high3) children3 hfalse3 l
      have hchildStage :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 6) 3 (.node G3 low3 high3 children3)) l =
          d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (childDepth + 5) 4 (children3 l) := by
        simpa using hstep
      have hlocal : d2FlowCandidateQuota d 18 4 .mid <=
          d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 5) 4 input) := by
        cases hi : input with
        | node G4 low4 high4 children4 =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 18)
              (role := d2FlowCandidateRole d 18)
              (quota := d2FlowCandidateQuota d 18)
              (h := childDepth + 4) (i := 4) (G := G4)
              (low := low4) (high := high4) children4 hactive4
            have hdef' : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 5) 4 input) =
                G4 + d2FlowCandidateQuota d 18 4 .mid := by
              simpa [hi, hrole4] using hdef
            rw [← hi, hdef']
            omega
      have hrootEq :
          d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run19 j) k) m) l) =
            d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 5) 4 input) := by
        calc
          _ = d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 6) 3 parent) l) := by
                exact congrArg d2FlowTreeRootDeficit hproj
          _ = d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 5) 4 input) := by
                simpa [parent, input, hp] using
                  congrArg d2FlowTreeRootDeficit hchildStage
      simpa [d, initial, run18, run19] using hrootEq.symm ▸ hlocal

end Chvatal.D2Reserve
