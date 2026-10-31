import D2Stage14ActualLevelFourInputs
import D2Stage15LevelFourInvariant
import D2Stage15Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv

set_option maxHeartbeats 2000000

/-- The actual Stage-15 level-five child roots obey their sender cap. The
Stage-14 level-four ordinary cut provides the child bound, and its recursive
input contract is inherited from the Stage-13 invariant. -/
theorem d2FlowCandidateRun_stage15_levelFive_root_cap
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (childDepth + 7)
                  (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) l) q) <=
      d2FlowCandidateCapacity (childDepth + 7) 5 15 := by
  let d := childDepth + 7
  let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let path4 := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l
  have hprojection := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (h := childDepth + 2) (i := 0) run j k m l q
  have hinv4 := d2FlowCandidateRun_stage14_levelFour_invariant
    childDepth hd j k m l
  have hinputs := d2FlowCandidateStage14_actual_levelFour_inputs childDepth hd j k m l
  have hfront := d2FlowCandidateStage14_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive4, hrole4, _, _, _⟩
  have hregular4 : d2FlowCandidateRole d 14 4 = .topRise ∨
      d2FlowCandidateRole d 14 4 = .mid ∨
      d2FlowCandidateRole d 14 4 = .botDesc := Or.inr (Or.inl hrole4)
  cases hsource : path4 with
  | node G low high children =>
      have hsourceInv := hinv4
      change d2FlowTreeInv 8192 path4 at hsourceInv
      rw [hsource] at hsourceInv
      have hsourceInputs := hinputs
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 4 path4 at hsourceInputs
      rw [hsource] at hsourceInputs
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (active := d2FlowCandidateActive d 14)
        (role := d2FlowCandidateRole d 14)
        (quota := d2FlowCandidateQuota d 14)
        (cap := fun x => d2FlowCandidateCapacity d x 14)
        (stageDepth := childDepth + 2) (i := 4)
        (.node G low high children) hactive4 hregular4 hsourceInv hsourceInputs
      have hcapShift := d2FlowCandidateCapacity_succ_level_next_stage d 4 14
        (by omega)
      have hlocal := hchildCap q
      rw [← hsource] at hlocal
      rw [← hprojection] at hlocal
      rw [← hcapShift] at hlocal
      simpa [d, run] using hlocal

end Chvatal.D2Reserve
