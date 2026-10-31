import D2Stage18LevelSixInputs
import D2Stage18LevelFiveInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun
attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/- Each level-six child of a level-five node in Run 19 has received the
Stage-18 level-six middle quota. -/
theorem d2FlowCandidateRun_stage19_levelFive_child_floor
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run19 j) k) m) l) q) r) := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run18 j) k) m) l) q
  let input := d2FlowTreeChild parent r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse5 : d2FlowCandidateActive d 18 5 = false := by
    cases h : d2FlowCandidateActive d 18 5 with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage18_iff hd14).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hactive6 : d2FlowCandidateActive d 18 6 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole6 : d2FlowCandidateRole d 18 6 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 6 (Or.inr rfl)
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have hproj :
      d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run19 j) k) m) l) q) r =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 18)
          (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
          (childDepth + 4) 5 parent) r := by
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path6_tree_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 3) (i := 0) run18 j k m l q r
  have hparentInput := d2FlowCandidateRun_stage18_levelFive_inputs
    (childDepth + 2) (by omega) j k m l q
  have hparentInput' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 5 parent := by
    simpa [d, initial, run18, parent] using hparentInput
  have hinputContract := d2FlowCandidateRun_stage18_levelSix_inputs
    (childDepth + 2) (by omega) j k m l q r
  have hinputContract' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 6 input := by
    simpa [d, initial, run18, parent, input] using hinputContract
  cases hp : parent with
  | node G5 low5 high5 children5 =>
      have hstep := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 18)
        (role := d2FlowCandidateRole d 18)
        (quota := d2FlowCandidateQuota d 18)
        (h := childDepth + 3) (i := 5) (G := G5)
        (low := low5) (high := high5) children5 hfalse5 r
      have hchildStage :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 4) 5
              (.node G5 low5 high5 children5)) r =
          d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (childDepth + 3) 6 (children5 r) := by
        simpa using hstep
      have hlocal : d2FlowCandidateQuota d 18 6 .mid <=
          d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              (childDepth + 3) 6 input) := by
        cases hi : input with
        | node G6 low6 high6 children6 =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 18)
              (role := d2FlowCandidateRole d 18)
              (quota := d2FlowCandidateQuota d 18)
              (h := childDepth + 2) (i := 6) (G := G6)
              (low := low6) (high := high6) children6 hactive6
            have hdef' : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 3) 6 input) =
                G6 + d2FlowCandidateQuota d 18 6 .mid := by
              simpa [hi, hrole6] using hdef
            rw [← hi, hdef']
            omega
      have hrootEq :
          d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild run19 j) k) m) l) q) r) =
            d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 3) 6 input) := by
        calc
          _ = d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 18)
                  (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                  (childDepth + 4) 5 parent) r) := by
                exact congrArg d2FlowTreeRootDeficit hproj
          _ = d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 18)
                (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
                (childDepth + 3) 6 input) := by
                simpa [parent, input, hp] using
                  congrArg d2FlowTreeRootDeficit hchildStage
      simpa [d, initial, run18, run19] using hrootEq.symm ▸ hlocal

end Chvatal.D2Reserve
