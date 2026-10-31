import D2Stage20LevelTwoInputs
import D2Stage18RootInputs
import D2Stage19PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- The full Stage-20 root input contract. At depth 16 the root is inactive;
from depth 17 onward it is top-descending and its zero deficit is preserved
from Stage 18 through the inactive Stage-19 root. -/
theorem d2FlowCandidateRun_stage20_root_inputs
    (childDepth : Nat) (hd : 6 <= childDepth) :
    let d := childDepth + 10
    let run20 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 20
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun x => d2FlowCandidateCapacity d x 20) 0 run20 := by
  classical
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let run20 := d2FlowCandidateRun d initial 20
  have hd16 : 16 <= d := by dsimp [d]; omega
  have hd14 : 14 <= d := by omega
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have hrun20 : run20 = d2FlowCandidateStage d 19 run19 := by
    change d2FlowCandidateRun d initial 20 =
      d2FlowCandidateStage d 19 (d2FlowCandidateRun d initial 19)
    rw [d2FlowCandidateRun.eq_def]
  have hchildren : ∀ j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
        (d2FlowCandidateQuota d 20)
        (fun x => d2FlowCandidateCapacity d x 20) 1
        (d2FlowTreeChild run20 j) := by
    intro j
    have hfalse1 : d2FlowCandidateActive d 20 1 = false := by
      cases h : d2FlowCandidateActive d 20 1 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := 1) hd16).mp h
          by_cases h16 : d = 16 <;> simp [h16] at hs <;> omega
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20) 8192 1
      (d2FlowTreeChild run20 j) hfalse1
    intro k
    simpa [d, initial, run20] using
      d2FlowCandidateRun_stage20_levelTwo_inputs childDepth hd j k
  by_cases hstartup : d = 16
  · have hfalse0 : d2FlowCandidateActive d 20 0 = false := by
      cases h : d2FlowCandidateActive d 20 0 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := 0) hd16).mp h
          simp [hstartup] at hs
    exact d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20)
      8192 0 run20 hfalse0 hchildren
  · have hactive20 : d2FlowCandidateActive d 20 0 = true := by
      apply (d2FlowCandidateActive_stage20_iff hd16).2
      simp [hstartup]
    have hrole20 : d2FlowCandidateRole d 20 0 = .topDesc := by
      have htop := d2FlowCandidateRole_stage20_top hd16
      simpa [hstartup] using htop
    have hactive18 : d2FlowCandidateActive d 18 0 = true := by
      apply (d2FlowCandidateActive_stage18_iff (i := 0) hd14).2
      have hnotSmall : ¬ d <= 15 := by omega
      simp [hnotSmall]
    have hrole18 : d2FlowCandidateRole d 18 0 = .topDesc := by
      have htop := d2FlowCandidateRole_stage18_top hd14
      have hnotSmall : ¬ d <= 15 := by omega
      simpa [hnotSmall] using htop
    have hinputs18 := d2FlowCandidateRun_stage18_root_inputs
      (childDepth + 3) (by omega)
    have hinputs18' : d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
        (d2FlowCandidateQuota d 18)
        (fun x => d2FlowCandidateCapacity d x 18) 0 run18 := by
      simpa [d, initial, run18] using hinputs18
    have hG18 : ∀ G low high children,
        run18 = .node G low high children → G = 0 := by
      intro G low high children ht
      change D2FlowTree (childDepth + 10) at run18
      have hx := hinputs18'
      rw [ht] at hx
      simp only [d2FlowStageInvInputs, hactive18, if_true, hrole18] at hx
      exact hx.2.2
    have hzero19 : d2FlowTreeRootDeficit run19 = 0 := by
      change D2FlowTree (childDepth + 10) at run18
      cases ht : run18 with
      | node G low high children =>
          have hG := hG18 G low high children ht
          rw [hrun19, ht]
          change d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive d 18)
              (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
              d 0 (.node G low high children)) = 0
          rw [d2FlowStage_active_node_deficit children hactive18, hrole18, hG]
          simp
    have hfalse19 : d2FlowCandidateActive d 19 0 = false := by
      cases h : d2FlowCandidateActive d 19 0 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage19_iff (i := 0) hd14).mp h
          by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
    have hzero20 : d2FlowTreeRootDeficit run20 = 0 := by
      rw [hrun20, d2FlowCandidateStage]
      rw [d2FlowStage_root_deficit_of_inactive
        (active := d2FlowCandidateActive d 19)
        (role := d2FlowCandidateRole d 19)
        (quota := d2FlowCandidateQuota d 19) (i := 0) run19 hfalse19]
      simpa [run19] using hzero19
    have hinv20 : d2FlowTreeInv 8192 run20 := by
      simpa [d, initial, run20] using
        d2FlowCandidateStage19_preserves_inv (childDepth + 1) (by omega)
    have hbalance := d2FlowTreeInv_root_balance_of_zero
      run20 hinv20 (by omega) hzero20
    have hcontract := d2FlowStageInvInputs_topDesc_of_contract
      (scale := 8192) (i := 0) run20 hactive20 hrole20 hchildren
      hbalance hzero20
    simpa [d, initial, run20] using hcontract

end Chvatal.D2Reserve
