import D2Stage15LevelFiveContract
import D2Stage14PreservesInv
import D2Stage16Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 5000000

/-- The Stage-15 level-five middle cut exports exactly the normalized deficit
gate needed by its level-six children at Stage 16. This is the local bridge
from one checked stage to the next; it does not yet assemble the other
Stage-16 contract fields. -/
theorem d2FlowCandidateRun_stage16_levelSix_root_cap
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 16) j) k) m) l) q) r) <=
      d2FlowCandidateCapacity (childDepth + 7) 6 16 := by
  let d := childDepth + 7
  let run15 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let path2 := d2FlowTreeChild (d2FlowTreeChild run15 j) k
  let path4 := d2FlowTreeChild (d2FlowTreeChild path2 m) l
  let path5 := d2FlowTreeChild path4 q
  have hinv0 : d2FlowTreeInv 8192 run15 := by
    simpa [d, run15] using d2FlowCandidateStage14_preserves_inv childDepth hd
  have hinv2 := d2FlowTreeInv_grandchild
    (h := childDepth + 5) run15 hinv0 j k
  have hinv4 := d2FlowTreeInv_grandchild
    (h := childDepth + 3) path2 hinv2 m l
  have hinvPath4 : d2FlowTreeInv 8192 path4 := hinv4
  have hinv5 : d2FlowTreeInv 8192 path5 := by
    cases hsource4 : path4 with
    | node G low high children =>
        have hx := hinvPath4
        rw [hsource4] at hx
        simp only [d2FlowTreeInv] at hx
        change d2FlowTreeInv 8192 (d2FlowTreeChild path4 q)
        rw [hsource4]
        simp only [d2FlowTreeChild]
        exact hx.2.2.2 q
  have hinputs := d2FlowCandidateRun_stage15_levelFive_inputs
    childDepth hd j k m l q
  have hinputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun x => d2FlowCandidateCapacity d x 15) 5 path5 := hinputs
  have hactive : d2FlowCandidateActive d 15 5 = true := by
    have h := d2FlowCandidateActive_stage15_at (d := d) (by dsimp [d]; omega)
    exact h.2.2.1
  have hrole : d2FlowCandidateRole d 15 5 = .mid := by
    exact d2FlowCandidateRole_stage15_internal_mid (by dsimp [d]; omega)
      5 (Or.inr rfl)
  have hregular : d2FlowCandidateRole d 15 5 = .topRise \/
      d2FlowCandidateRole d 15 5 = .mid \/
      d2FlowCandidateRole d 15 5 = .botDesc := Or.inr (Or.inl hrole)
  have hprojection := d2FlowStage_path6_projection
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (h := childDepth + 1) (i := 0) run15 j k m l q r
  have hprojection' := hprojection
  simp only [Nat.zero_add] at hprojection'
  have hcapShift := d2FlowCandidateCapacity_succ_level_next_stage d 5 15
    (by dsimp [d]; omega)
  cases hsource : path5 with
  | node G low high children =>
      have hsourceInv : d2FlowTreeInv 8192 (.node G low high children) := by
        rw [← hsource]
        exact hinv5
      have hsourceInputs : d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
          (d2FlowCandidateQuota d 15)
          (fun x => d2FlowCandidateCapacity d x 15) 5
          (.node G low high children) := by
        rw [← hsource]
        exact hinputs'
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (active := d2FlowCandidateActive d 15)
        (role := d2FlowCandidateRole d 15)
        (quota := d2FlowCandidateQuota d 15)
        (cap := fun x => d2FlowCandidateCapacity d x 15)
        (stageDepth := childDepth + 1) (i := 5)
        (.node G low high children) hactive hregular hsourceInv hsourceInputs
      have hlocal := hchildCap r
      rw [← hsource] at hlocal
      rw [← hprojection'] at hlocal
      rw [← hcapShift] at hlocal
      rw [d2FlowCandidateRun]
      change 512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateStage d 15 run15) j) k) m) l) q) r) <=
        d2FlowCandidateCapacity d 6 16
      simpa only [d2FlowCandidateStage] using hlocal

end Chvatal.D2Reserve
