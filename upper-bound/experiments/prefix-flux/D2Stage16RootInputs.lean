import D2Stage16LevelTwoInputs
import D2Stage15PreservesInv
import D2Stage14ActualRootInputs
import D2Stage16Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Assemble the actual Stage-16 root contract from its checked level-two
contracts. -/
theorem d2FlowCandidateRun_stage16_root_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    let d := childDepth + 7
    let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 16
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 0 run := by
  classical
  let d := (childDepth + 6) + 1
  let initial := d2FlowTreeInitial 8192 d
  let run14 : D2FlowTree (childDepth + 7) :=
    d2FlowCandidateRun d initial 14
  let run15 : D2FlowTree (childDepth + 7) :=
    d2FlowCandidateRun d initial 15
  let run16 : D2FlowTree (childDepth + 7) :=
    d2FlowCandidateRun d initial 16
  change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 0 run16
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hchildren : forall j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
        (d2FlowCandidateQuota d 16)
        (fun x => d2FlowCandidateCapacity d x 16) 1
        (d2FlowTreeChild run16 j) := by
    intro j
    have hfalse : d2FlowCandidateActive d 16 1 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hlev := (d2FlowCandidateActive_stage16_iff hd14).mp ht
      by_cases h14 : d = 14 <;> simp [h14] at hlev <;> omega
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (cap := fun x => d2FlowCandidateCapacity d x 16)
      8192 1 (d2FlowTreeChild run16 j) hfalse
    intro k
    have hk := d2FlowCandidateRun_stage16_levelTwo_inputs
      childDepth hd j k
    simpa [d, initial, run16] using hk
  have hroot14 := d2FlowCandidateStage14_actual_root_inputs childDepth hd
  have hfront := d2FlowCandidateStage14_frontiers d hd14
  have ha14 := hfront.1
  have hr14 := hfront.2.1
  have hroot14' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
      (d2FlowCandidateQuota d 14)
      (fun x => d2FlowCandidateCapacity d x 14) 0 run14 := by
      simpa [d, initial, run14] using hroot14
  have hzero14 : d2FlowTreeRootDeficit run14 = 0 := by
    have hroot := hroot14'
    cases htree : (run14 : D2FlowTree ((childDepth + 6) + 1)) with
    | node G low high children =>
        rw [htree] at hroot
        simp only [d2FlowStageInvInputs, ha14, if_true, hr14] at hroot
        simpa [d2FlowTreeRootDeficit] using hroot.2.2
  have hzero15 : d2FlowTreeRootDeficit run15 = 0 := by
    change d2FlowTreeRootDeficit (d2FlowCandidateRun d initial 15) = 0
    rw [d2FlowCandidateRun.eq_def]
    change d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d 14)
        (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14) d 0 run14) = 0
    rw [d2FlowStage_root_deficit_of_topDesc
      (active := d2FlowCandidateActive d 14)
      (role := d2FlowCandidateRole d 14)
      (quota := d2FlowCandidateQuota d 14) (i := 0) run14 ha14 hr14]
    exact hzero14
  have hfalse15 : d2FlowCandidateActive d 15 0 = false := by
    cases hv : d2FlowCandidateActive d 15 0 with
    | false => rfl
    | true =>
        have hlev := d2FlowCandidateActive_stage15_level_bound hv
        rcases hlev with h | h | h | h <;> omega
  have hzero16 : d2FlowTreeRootDeficit run16 = 0 := by
    change d2FlowTreeRootDeficit (d2FlowCandidateRun d initial 16) = 0
    rw [d2FlowCandidateRun.eq_def]
    change d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15) d 0 run15) = 0
    rw [d2FlowStage_root_deficit_of_inactive
      (active := d2FlowCandidateActive d 15)
      (role := d2FlowCandidateRole d 15)
      (quota := d2FlowCandidateQuota d 15) (i := 0) run15 hfalse15]
    exact hzero15
  by_cases h14 : d = 14
  case pos =>
    have hfalse : d2FlowCandidateActive d 16 0 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hlev := (d2FlowCandidateActive_stage16_iff hd14).mp ht
      simp [h14] at hlev
    exact d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (cap := fun x => d2FlowCandidateCapacity d x 16)
      8192 0 run16 hfalse hchildren
  case neg =>
    have hactive : d2FlowCandidateActive d 16 0 = true := by
      apply (d2FlowCandidateActive_stage16_iff hd14).2
      simp [h14]
    have hrole : d2FlowCandidateRole d 16 0 = .topDesc := by
      have h := d2FlowCandidateRole_stage16_top hd14
      simpa [h14] using h
    have hinv16 : d2FlowTreeInv 8192 run16 := by
      simpa [d, initial, run16] using
        d2FlowCandidateStage15_preserves_inv childDepth hd
    have hbalance : (d2FlowTreeRootData run16).2.1 +
        (d2FlowTreeRootData run16).2.2 = d2FlowTreeRootDeficit run16 :=
      d2FlowTreeInv_root_balance_of_zero run16 hinv16 (by omega) hzero16
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 0 run16 hactive hrole hchildren hbalance hzero16

/-- Stage 16 preserves the recursive flow invariant on the actual run. -/
theorem d2FlowCandidateStage16_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 17) := by
  let d := (childDepth + 6) + 1
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 16
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, initial, before] using
      d2FlowCandidateStage15_preserves_inv childDepth hd
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 0 before := by
    simpa [d, initial, before] using
      d2FlowCandidateRun_stage16_root_inputs childDepth hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 16)
    (role := d2FlowCandidateRole d 16)
    (quota := d2FlowCandidateQuota d 16)
    (cap := fun x => d2FlowCandidateCapacity d x 16)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateRun d initial 17)
  rw [d2FlowCandidateRun.eq_def]
  exact hpres

end Chvatal.D2Reserve
