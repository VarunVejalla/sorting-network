import D2Stage18LevelThreeInputs
import D2Stage17LevelOneStartupInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- At the two startup depths, the Stage-17 level-one top-descending cut
resets each level-two root to zero. The recursively updated children provide
the Stage-18 level-three contracts. -/
theorem d2FlowCandidateRun_stage18_levelTwo_startup_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (hstartup : childDepth <= 8) (j k : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 2 tree := by
  have hchildDepth : childDepth = 7 \/ childDepth = 8 := by omega
  rcases hchildDepth with h7 | h8
  · subst childDepth
    let d := 14
    let initial := d2FlowTreeInitial 8192 d
    let run17 := d2FlowCandidateRun d initial 17
    let run18 := d2FlowCandidateRun d initial 18
    let parent := d2FlowTreeChild run17 j
    let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
    have hactive18 : d2FlowCandidateActive d 18 2 = true := by
      apply (d2FlowCandidateActive_stage18_iff (d := d) (i := 2) (by omega)).2
      simp
    have hrole18 : d2FlowCandidateRole d 18 2 = .topDesc :=
      d2FlowCandidateRole_stage18_top (d := d) (by omega)
    have hactive17 : d2FlowCandidateActive d 17 1 = true := by
      apply (d2FlowCandidateActive_stage17_iff (d := d) (i := 1) (by omega)).2
      simp
    have hrole17 : d2FlowCandidateRole d 17 1 = .topDesc :=
      d2FlowCandidateRole_stage17_top (d := d) (by omega)
    have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
      change d2FlowCandidateRun d initial 18 =
        d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
      rw [d2FlowCandidateRun.eq_def]
    have htreeEq : tree = d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 17)
          (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
          13 1 parent) k := by
      change d2FlowTreeChild (d2FlowTreeChild run18 j) k = _
      rw [hrun18]
      simp only [d2FlowCandidateStage]
      exact d2FlowStage_child_child_projection
        (active := d2FlowCandidateActive d 17)
        (role := d2FlowCandidateRole d 17)
        (quota := d2FlowCandidateQuota d 17)
        (h := 12) (i := 0) run17 j k
    have hzero : d2FlowTreeRootDeficit tree = 0 := by
      rw [htreeEq]
      cases hp : parent with
      | node G low high children =>
          have hz := d2FlowStage_topDesc_child_deficit
            (active := d2FlowCandidateActive d 17)
            (role := d2FlowCandidateRole d 17)
            (quota := d2FlowCandidateQuota d 17)
            (h := 12) (i := 1) (G := G) (low := low) (high := high)
            children hactive17 hrole17 k
          simpa [hp] using hz
    have hchildren : ∀ q : Fin 8,
        d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
          (d2FlowCandidateQuota d 18)
          (fun x => d2FlowCandidateCapacity d x 18) 3
          (d2FlowTreeChild tree q) := by
      intro q
      exact d2FlowCandidateRun_stage18_levelThree_inputs
        7 (by omega) j k q
    have hinvRun18 : d2FlowTreeInv 8192 run18 := by
      simpa [d, initial, run17, run18] using
        d2FlowCandidateStage17_preserves_inv 7 (by omega)
    have hinvTree : d2FlowTreeInv 8192 tree := by
      simpa [tree] using d2FlowTreeInv_grandchild
        (h := 12) run18 hinvRun18 j k
    have hbalance := d2FlowTreeInv_root_balance_of_zero
      tree hinvTree (by omega) hzero
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 2 tree hactive18 hrole18 hchildren hbalance hzero
  · subst childDepth
    let d := 15
    let initial := d2FlowTreeInitial 8192 d
    let run17 := d2FlowCandidateRun d initial 17
    let run18 := d2FlowCandidateRun d initial 18
    let parent := d2FlowTreeChild run17 j
    let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
    have hactive18 : d2FlowCandidateActive d 18 2 = true := by
      apply (d2FlowCandidateActive_stage18_iff (d := d) (i := 2) (by omega)).2
      simp
    have hrole18 : d2FlowCandidateRole d 18 2 = .topDesc :=
      d2FlowCandidateRole_stage18_top (d := d) (by omega)
    have hactive17 : d2FlowCandidateActive d 17 1 = true := by
      apply (d2FlowCandidateActive_stage17_iff (d := d) (i := 1) (by omega)).2
      simp
    have hrole17 : d2FlowCandidateRole d 17 1 = .topDesc :=
      d2FlowCandidateRole_stage17_top (d := d) (by omega)
    have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
      change d2FlowCandidateRun d initial 18 =
        d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
      rw [d2FlowCandidateRun.eq_def]
    have htreeEq : tree = d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 17)
          (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
          14 1 parent) k := by
      change d2FlowTreeChild (d2FlowTreeChild run18 j) k = _
      rw [hrun18]
      simp only [d2FlowCandidateStage]
      exact d2FlowStage_child_child_projection
        (active := d2FlowCandidateActive d 17)
        (role := d2FlowCandidateRole d 17)
        (quota := d2FlowCandidateQuota d 17)
        (h := 13) (i := 0) run17 j k
    have hzero : d2FlowTreeRootDeficit tree = 0 := by
      rw [htreeEq]
      cases hp : parent with
      | node G low high children =>
          have hz := d2FlowStage_topDesc_child_deficit
            (active := d2FlowCandidateActive d 17)
            (role := d2FlowCandidateRole d 17)
            (quota := d2FlowCandidateQuota d 17)
            (h := 13) (i := 1) (G := G) (low := low) (high := high)
            children hactive17 hrole17 k
          simpa [hp] using hz
    have hchildren : ∀ q : Fin 8,
        d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
          (d2FlowCandidateQuota d 18)
          (fun x => d2FlowCandidateCapacity d x 18) 3
          (d2FlowTreeChild tree q) := by
      intro q
      exact d2FlowCandidateRun_stage18_levelThree_inputs
        8 (by omega) j k q
    have hinvRun18 : d2FlowTreeInv 8192 run18 := by
      simpa [d, initial, run17, run18] using
        d2FlowCandidateStage17_preserves_inv 8 (by omega)
    have hinvTree : d2FlowTreeInv 8192 tree := by
      simpa [tree] using d2FlowTreeInv_grandchild
        (h := 13) run18 hinvRun18 j k
    have hbalance := d2FlowTreeInv_root_balance_of_zero
      tree hinvTree (by omega) hzero
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 2 tree hactive18 hrole18 hchildren hbalance hzero

end Chvatal.D2Reserve
