import D2Stage14ActualInputs

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false

/-- Stage 14 is inactive at level five; the actual level-six contracts below
each child therefore give the complete level-five input contract. -/
theorem d2FlowCandidateStage14_actual_levelFive_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k m l q,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 5
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) q) := by
  intro j k m l q
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial 14
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run j) k) m) l) q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
    (d2FlowCandidateQuota d 14)
    (fun x => d2FlowCandidateCapacity d x 14) 5 tree
  have hinactive5 : d2FlowCandidateActive d 14 5 = false := by
    simp [d2FlowCandidateActive]
  have hrecursive : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 6
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateStage14_actual_levelSix_inputs
      childDepth hd j k m l q s
  cases htree : tree with
  | node G low high children =>
      simp only [d, d2FlowStageInvInputs, hinactive5, if_false]
      constructor
      · intro s
        have hs := hrecursive s
        rw [htree] at hs
        simpa only [d2FlowTreeChild] using hs
      · trivial

end Chvatal.D2Reserve
