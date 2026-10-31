import D2Stage14Arithmetic
import D2Stage15Frontier

namespace Chvatal.D2Reserve

set_option maxHeartbeats 20000000

/-- Pushing a stage through seven consecutive child projections leaves the
last child equal to the child produced by the stage at its level-six
ancestor. This is the data-level form of the existing path-six deficit
projection. -/
theorem d2FlowStage_path7_child_projection
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 7)) (j k m l q r s : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 7) i tree) j) k) m) l) q) r) s =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 6)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild tree j) k) m) l) q) r)) s := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Every actual stage-15 level-seven root is balanced: it is the child
written by the stage-14 level-six bot-descending sender. This supplies the
balance field needed when level seven is the stage-15 bot-rise sender. -/
theorem d2FlowCandidateRun_stage15_levelSeven_balanced
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run15 j) k) m) l) q) r) s
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run14 := d2FlowCandidateRun d initial 14
  let run15 := d2FlowCandidateRun d initial 15
  let pathParent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run14 j) k) m) l) q) r
  have hfront := d2FlowCandidateStage14_frontiers d (by dsimp [d]; omega)
  have hactive : d2FlowCandidateActive d 14 6 = true := by
    have ha : d2FlowCandidateActive d 14 6 = true := hfront.2.2.2.2.2.2.1
    exact ha
  have hrole : d2FlowCandidateRole d 14 6 = .botDesc :=
    hfront.2.2.2.2.2.2.2.1
  have hlocal :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 14)
            (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
            (childDepth + 1) 6 pathParent) s)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 14)
            (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
            (childDepth + 1) 6 pathParent) s)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 14)
            (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
            (childDepth + 1) 6 pathParent) s) := by
    cases pathParent with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive
          (Or.inr (Or.inr hrole)) s
  have hrun : d2FlowCandidateRun d initial 15 =
      d2FlowCandidateStage d 14 run14 := by
    rfl
  dsimp only [d, initial]
  rw [hrun]
  simp only [d2FlowCandidateStage]
  rw [d2FlowStage_path7_child_projection]
  simpa [pathParent] using hlocal

/-- The complete stage-input contract at every actual level-seven sender on
stage 15. Its only local field is endpoint balance because this sender is
bot-rise; all of its descendants are inactive at that stage. -/
theorem d2FlowStageInvInputs_botRise_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .botRise)
    (hchildren : forall u : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree u))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
      have hb : low + high = G := by
        simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
      simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
      exact ⟨hchildren, hb, trivial⟩

end Chvatal.D2Reserve

