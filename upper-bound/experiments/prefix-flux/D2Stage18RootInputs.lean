import D2Stage18LevelOneInputs
import D2Stage16RootInputs
import D2Stage17LevelOneStartupInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Assemble the Stage-18 root input contract. It is inactive at startup;
after startup its top-descending cut uses the zero root preserved by Stage 16
and the inactive Stage-17 root. -/
theorem d2FlowCandidateRun_stage18_root_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 0 run18 := by
  classical
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run16 : D2FlowTree ((height + 7) + 1) :=
    d2FlowCandidateRun d initial 16
  let run17 : D2FlowTree ((height + 7) + 1) :=
    d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree ((height + 7) + 1) :=
    d2FlowCandidateRun d initial 18
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hchildren : ∀ j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
        (d2FlowCandidateQuota d 18)
        (fun x => d2FlowCandidateCapacity d x 18) 1
        (d2FlowTreeChild run18 j) := by
    intro j
    have hj := d2FlowCandidateRun_stage18_levelOne_inputs childDepth hd j
    simpa [d, initial, run18] using hj
  by_cases hsmall : d <= 15
  · have hfalse : d2FlowCandidateActive d 18 0 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hlevels := (d2FlowCandidateActive_stage18_iff hd14).mp ht
      simp [hsmall] at hlevels
    exact d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (cap := fun x => d2FlowCandidateCapacity d x 18)
      8192 0 run18 hfalse hchildren
  · have hd16 : 16 <= d := by omega
    have hactive18 : d2FlowCandidateActive d 18 0 = true := by
      apply (d2FlowCandidateActive_stage18_iff hd14).2
      simp [hsmall]
    have hrole18 : d2FlowCandidateRole d 18 0 = .topDesc := by
      simpa [hsmall] using d2FlowCandidateRole_stage18_top hd14
    have hactive16 : d2FlowCandidateActive d 16 0 = true := by
      apply (d2FlowCandidateActive_stage16_iff hd14).2
      simp [show d ≠ 14 by omega]
    have hrole16 : d2FlowCandidateRole d 16 0 = .topDesc := by
      simpa [show d ≠ 14 by omega] using d2FlowCandidateRole_stage16_top hd14
    have hinputs16 := d2FlowCandidateRun_stage16_root_inputs childDepth hd
    have hinputs16' : d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
        (d2FlowCandidateQuota d 16)
        (fun x => d2FlowCandidateCapacity d x 16) 0 run16 := by
      simpa [d, initial, run16] using hinputs16
    have hzero16 : d2FlowTreeRootDeficit run16 = 0 := by
      cases htree : run16 with
      | node G low high children =>
          have hx := hinputs16'
          rw [htree] at hx
          simp only [d2FlowStageInvInputs, hactive16, if_true, hrole16] at hx
          simpa [d2FlowTreeRootDeficit] using hx.2.2
    have hrun17 : run17 = d2FlowCandidateStage d 16 run16 := by
      change d2FlowCandidateRun d initial 17 =
        d2FlowCandidateStage d 16 (d2FlowCandidateRun d initial 16)
      rw [d2FlowCandidateRun.eq_def]
    have hzero17 : d2FlowTreeRootDeficit run17 = 0 := by
      cases htree : run16 with
      | node G low high children =>
          have hG : G = 0 := by
            have hx := hinputs16'
            rw [htree] at hx
            simp only [d2FlowStageInvInputs, hactive16, if_true, hrole16] at hx
            exact hx.2.2
          rw [hrun17, htree]
          change d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              d 0 (.node G low high children)) = 0
          rw [hG]
          rw [d2FlowStage_active_node_deficit children hactive16]
          rw [hrole16]
          simp
    have hfalse17 : d2FlowCandidateActive d 17 0 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hlevels := (d2FlowCandidateActive_stage17_iff hd14).mp ht
      rcases hlevels with h | h | h | h <;> omega
    have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
      change d2FlowCandidateRun d initial 18 =
        d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
      rw [d2FlowCandidateRun.eq_def]
    have hzero18 : d2FlowTreeRootDeficit run18 = 0 := by
      rw [hrun18, d2FlowCandidateStage]
      rw [d2FlowStage_root_deficit_of_inactive
        (active := d2FlowCandidateActive d 17)
        (role := d2FlowCandidateRole d 17)
        (quota := d2FlowCandidateQuota d 17) (i := 0) run17 hfalse17]
      simpa [run17] using hzero17
    have hinv18 : d2FlowTreeInv 8192 run18 := by
      simpa [d, initial, run18] using
        d2FlowCandidateStage17_preserves_inv childDepth hd
    have hbalance := d2FlowTreeInv_root_balance_of_zero
      run18 hinv18 (by omega) hzero18
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 0 run18 hactive18 hrole18 hchildren hbalance hzero18

end Chvatal.D2Reserve
