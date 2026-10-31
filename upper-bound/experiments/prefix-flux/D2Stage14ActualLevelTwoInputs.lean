import D2Stage14ActualLevelTwoBalance
import D2Stage14ActualLevelTwoReserve
import D2Stage14ActualLevelThreeInputs

namespace Chvatal.D2Reserve

set_option maxHeartbeats 30000000
set_option linter.constructorNameAsVariable false

/-- The full Stage-14 recursive input contract holds at every actual
level-two node: Stage 13 supplies balance and quota-backed endpoint reserves,
and level three is inactive. -/
theorem d2FlowCandidateStage14_actual_levelTwo_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k,
      let run : D2FlowTree (childDepth + 7) :=
        d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14
      let path : D2FlowPath 2 := .cons j (.cons k .nil)
      let tree : D2FlowTree (childDepth + 5) :=
        d2FlowTreeAtPath 2 run path
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 2
        tree := by
  intro j k
  let d := childDepth + 7
  let run : D2FlowTree d :=
    d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let path : D2FlowPath 2 := .cons j (.cons k .nil)
  let output : D2FlowTree (childDepth + 5) := d2FlowTreeAtPath 2 run path
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
    (d2FlowCandidateQuota d 14)
    (fun x => d2FlowCandidateCapacity d x 14) 2 output
  have hfront := d2FlowCandidateStage14_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _, _, _⟩
  have hstate := d2FlowCandidateStage14_actual_levelTwo_balance_deficit
    childDepth hd j k
  change (d2FlowTreeRootData output).2.1 +
      (d2FlowTreeRootData output).2.2 = d2FlowTreeRootDeficit output /\
    512 * d2FlowTreeRootDeficit output <=
      d2FlowCandidateCapacity d 2 14 at hstate
  have hreserve := d2FlowCandidateStage14_actual_levelTwo_endpoint_reserves
    childDepth hd j k
  change d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output ⟨0, by omega⟩) /\
    d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output ⟨7, by omega⟩) at hreserve
  rcases d2FlowCandidateStage14_levelTwo_parameters d (by omega) with
    ⟨_, _, hquotaCap, hquotaEven⟩
  have hdD : 14 <= d := by dsimp [d]; omega
  have hrecursive : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 3
        (d2FlowTreeChild output s) := by
    intro s
    have hs := d2FlowCandidateStage14_actual_levelThree_inputs_for_run
      childDepth hd run (by rfl) j k s
    change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
      (d2FlowCandidateQuota d 14)
      (fun x => d2FlowCandidateCapacity d x 14) 3
      (d2FlowTreeChild
        (d2FlowTreeAtPath 2 run (.cons j (.cons k .nil))) s)
    exact d2FlowStageInvInputs_path3_child
      (active := d2FlowCandidateActive d 14)
      (role := d2FlowCandidateRole d 14)
      (quota := d2FlowCandidateQuota d 14)
      (cap := fun x => d2FlowCandidateCapacity d x 14)
      8192 (h := childDepth + 4) run j k s hs
  have hleft : d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output ⟨0, by omega⟩) := hreserve.1
  have hright : d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output ⟨7, by omega⟩) := hreserve.2
  have halloc : d2FlowCandidateQuota d 14 2 .mid <=
      d2FlowTotal (fun s =>
        d2FlowTreeRootDeficit (d2FlowTreeChild output s)) -
        d2FlowTreeRootDeficit output := by
    exact d2FlowCandidateStage14_levelTwo_allocation_of_endpoint
      d (d2FlowTreeRootDeficit output)
      (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild output s))
      ⟨0, by omega⟩ hdD hstate.2 hleft
  exact d2FlowStageInvInputs_mid_of_contract 8192 2 output
    (by simpa [d] using hactive2) (by simpa [d] using hrole2)
    hrecursive hstate.1 hstate.2 hquotaCap halloc hquotaEven hleft hright

end Chvatal.D2Reserve
