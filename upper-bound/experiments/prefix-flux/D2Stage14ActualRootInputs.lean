import D2Stage14ActualLevelTwoRunAdapter
import D2Stage14Contract

namespace Chvatal.D2Reserve

set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-- The actual Stage-14 root satisfies its top-descending input contract.
The level-one nodes are inactive and inherit the already checked level-two
contracts. The root deficit is still zero after the Stage-12 reset; balance
comes from the Stage-13 invariant. -/
theorem d2FlowCandidateStage14_actual_root_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    let run : D2FlowTree (childDepth + 7) :=
      d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 14
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (childDepth + 7) 14)
      (d2FlowCandidateRole (childDepth + 7) 14)
      (d2FlowCandidateQuota (childDepth + 7) 14)
      (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 0 run := by
  let d := childDepth + 7
  let run : D2FlowTree d :=
    d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
    (d2FlowCandidateQuota d 14)
    (fun x => d2FlowCandidateCapacity d x 14) 0 run
  have hfront := d2FlowCandidateStage14_frontiers d (by dsimp [d]; omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, _, _, _, _, _⟩
  have hchildren : ∀ j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 1
        (d2FlowTreeChild run j) := by
    intro j
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 14)
      (role := d2FlowCandidateRole d 14)
      (quota := d2FlowCandidateQuota d 14)
      (cap := fun x => d2FlowCandidateCapacity d x 14)
      8192 1 (d2FlowTreeChild run j) (by simp [d2FlowCandidateActive, d, tfD2])
    intro k
    have hrun : run = d2FlowCandidateRun d
        (d2FlowTreeInitial 8192 d) 14 := by rfl
    have htwo := d2FlowCandidateStage14_actual_levelTwo_inputs_for_run
      childDepth hd run hrun j k
    exact d2FlowStageInvInputs_path2_child
      (active := d2FlowCandidateActive d 14)
      (role := d2FlowCandidateRole d 14)
      (quota := d2FlowCandidateQuota d 14)
      (cap := fun x => d2FlowCandidateCapacity d x 14)
      8192 (h := childDepth + 5)
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14) j k htwo
  have hzero : d2FlowTreeRootDeficit run = 0 := by
    have h12 := d2FlowCandidateStage12_root_zero (childDepth + 1) (by omega)
    have hfront12 := d2FlowCandidateStage12_frontiers d (by dsimp [d]; omega)
    rcases hfront12 with ⟨hactive12, hrole12, _, _, _, _, _, _, _⟩
    have h13reset : d2FlowTreeRootDeficit
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13) = 0 := by
      change d2FlowTreeRootDeficit
        (d2FlowCandidateStage d 12
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12)) = 0
      change d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive d 12)
          (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12) d 0
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12)) = 0
      rw [d2FlowStage_root_deficit_of_topDesc
        (active := d2FlowCandidateActive d 12)
        (role := d2FlowCandidateRole d 12)
        (quota := d2FlowCandidateQuota d 12)
        (i := 0)
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12)
        hactive12 hrole12]
      simpa [d, Nat.add_assoc] using h12
    have h14inactive : d2FlowCandidateActive d 13 0 = false := by
      simp [d2FlowCandidateActive, d, tfD2]
    have h13zero : d2FlowTreeRootDeficit
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13) = 0 := h13reset
    change d2FlowTreeRootDeficit
      (d2FlowCandidateStage d 13
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13)) = 0
    change d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d 13)
        (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13) d 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13)) = 0
    rw [d2FlowStage_root_deficit_of_inactive
      (active := d2FlowCandidateActive d 13)
      (role := d2FlowCandidateRole d 13)
      (quota := d2FlowCandidateQuota d 13)
      (i := 0)
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13)
      h14inactive]
    exact h13zero
  have hinv := d2FlowCandidateStage13_preserves_inv (childDepth + 1) (by omega)
  have hbalance : (d2FlowTreeRootData run).2.1 +
      (d2FlowTreeRootData run).2.2 = d2FlowTreeRootDeficit run := by
    have hbalance' := d2FlowTreeInv_root_balance_of_zero
      (scale := 8192) (tree := run) hinv (by omega) hzero
    exact hbalance'
  exact d2FlowStageInvInputs_topDesc_of_contract 8192 0 run
    hactive0 hrole0 hchildren hbalance hzero

end Chvatal.D2Reserve
