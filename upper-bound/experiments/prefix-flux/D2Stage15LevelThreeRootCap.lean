import D2Stage15Frontier
import D2Stage14ActualLevelTwoChildAdapter

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-- The Stage-14 level-one node is inactive, so the actual Stage-15
level-three subtree is the level-three child produced by the local Stage-14
level-two cut. -/
theorem d2FlowCandidateRun_stage15_levelThree_path_eq_levelTwo_child
    (childDepth : Nat) (hd : 7 <= childDepth) (j k l : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) l =
    d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (childDepth + 5) 2
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (childDepth + 7)
              (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k)) l := by
  have hrun : d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 15 =
      d2FlowCandidateStage (childDepth + 7) 14
        (d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14) := by rfl
  rw [hrun]
  have hprojection := d2FlowStage_path3_projection
    (active := d2FlowCandidateActive (childDepth + 7) 14)
    (role := d2FlowCandidateRole (childDepth + 7) 14)
    (quota := d2FlowCandidateQuota (childDepth + 7) 14)
    (h := childDepth + 4) (i := 0)
    (d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j k l
  change d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (childDepth + 7) 14)
          (d2FlowCandidateRole (childDepth + 7) 14)
          (d2FlowCandidateQuota (childDepth + 7) 14)
          (childDepth + 7) 0
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14)) j) k) l =
    d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (childDepth + 5) 2
        (d2FlowTreeChild (d2FlowTreeChild
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k)) l
  exact hprojection

/-- The active Stage-14 level-two cut writes a level-three root within the
Stage-15 sender cap. -/
theorem d2FlowCandidateRun_stage15_levelThree_root_cap
    (childDepth : Nat) (hd : 7 <= childDepth) (j k l : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (childDepth + 7)
              (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) l) <=
      d2FlowCandidateCapacity (childDepth + 7) 3 15 := by
  let d := childDepth + 7
  let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let path2 := d2FlowTreeChild (d2FlowTreeChild run j) k
  have hinputs := d2FlowCandidateStage14_actual_levelTwo_child_inputs
    childDepth hd j k
  have hinv := d2FlowCandidateStage13_preserves_inv (childDepth + 1) (by omega)
  have hinv2 := d2FlowTreeInv_grandchild run hinv j k
  have hfront := d2FlowCandidateStage14_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _, _, _⟩
  have hregular2 : d2FlowCandidateRole d 14 2 = .topRise \/
      d2FlowCandidateRole d 14 2 = .mid \/
      d2FlowCandidateRole d 14 2 = .botDesc := by
    exact Or.inr (Or.inl hrole2)
  cases hsource : path2 with
  | node G low high children =>
      have hsourceInv := hinv2
      change d2FlowTreeInv 8192 path2 at hsourceInv
      rw [hsource] at hsourceInv
      have hsourceInputs := hinputs
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14)
        (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun q => d2FlowCandidateCapacity d q 14) 2 path2 at hsourceInputs
      rw [hsource] at hsourceInputs
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (active := d2FlowCandidateActive d 14)
        (role := d2FlowCandidateRole d 14)
        (quota := d2FlowCandidateQuota d 14)
        (cap := fun q => d2FlowCandidateCapacity d q 14)
        (stageDepth := childDepth + 4) (i := 2)
        (.node G low high children) hactive2 hregular2 hsourceInv hsourceInputs
      have hcapShift := d2FlowCandidateCapacity_succ_level_next_stage d 2 14
        (by omega)
      have hlocal := hchildCap l
      rw [← hsource] at hlocal
      rw [← d2FlowCandidateRun_stage15_levelThree_path_eq_levelTwo_child
          childDepth hd j k l] at hlocal
      rw [← hcapShift] at hlocal
      simpa [d] using hlocal

end Chvatal.D2Reserve
