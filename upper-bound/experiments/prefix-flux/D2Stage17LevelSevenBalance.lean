import D2Stage16RootInputs
import D2Stage17Frontier
import D2Stage15LevelSevenBalance
import D2Stage16Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Every actual Stage-17 level-seven root is balanced: it is written by the
Stage-16 level-six ordinary cut. -/
theorem d2FlowCandidateRun_stage17_levelSeven_balanced
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run17 := d2FlowCandidateRun d initial 17
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run17 j) k) m) l) q) r) s
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run16 := d2FlowCandidateRun d initial 16
  let run17 := d2FlowCandidateRun d initial 17
  let pathParent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run16 j) k) m) l) q) r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 16 6 = true := by
    apply (d2FlowCandidateActive_stage16_iff hd14).2
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole : d2FlowCandidateRole d 16 6 = .botDesc :=
    d2FlowCandidateRole_stage16_bottom hd14
  have hlocal :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
            (childDepth + 1) 6 pathParent) s)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
            (childDepth + 1) 6 pathParent) s)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
          (childDepth + 1) 6 pathParent) s) := by
    cases pathParent with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive
          (Or.inr (Or.inr hrole)) s
  have hrun : d2FlowCandidateRun d initial 17 =
      d2FlowCandidateStage d 16 run16 := by
    rw [d2FlowCandidateRun.eq_def]
  dsimp only [d, initial]
  rw [hrun]
  simp only [d2FlowCandidateStage]
  rw [d2FlowStage_path7_child_projection]
  simpa [pathParent] using hlocal

end Chvatal.D2Reserve
