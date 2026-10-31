import D2Stage15LevelFiveAllocation
import D2Stage15LevelSevenInputs
import D2Stage15Frontier
import D2Stage14ActualLevelFourInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

theorem d2FlowStage_path5_child_projection
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 5)) (j k m l q : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 5) i tree) j) k) m) l) q =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 4)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild tree j) k) m) l)) q := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- The level-five Stage-15 node is exactly the child output of its
level-four Stage-14 mid sender, hence has the balance field required by the
Stage-15 input contract. -/
theorem d2FlowCandidateRun_stage15_levelFive_balanced
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run15 j) k) m) l) q
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run14 := d2FlowCandidateRun d initial 14
  let run15 := d2FlowCandidateRun d initial 15
  let path4 := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run14 j) k) m) l
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run15 j) k) m) l) q
  have hfront := d2FlowCandidateStage14_frontiers d (by dsimp [d]; omega)
  rcases hfront with ⟨_, _, _, _, hactive, hrole, _, _, _⟩
  have hlocal : (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (childDepth + 3) 4 path4) q)).2.1 +
      (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (childDepth + 3) 4 path4) q)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 14)
            (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
            (childDepth + 3) 4 path4) q) := by
    cases path4 with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive
          (Or.inr (Or.inl hrole)) q
  have hprojection := d2FlowCandidateRun_stage15_levelFour_tree_eq_local
    (childDepth + 2) (by omega) j k m l
  have htree : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 14)
        (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
        (childDepth + 3) 4 path4) q := by
    exact congrArg (fun node : D2FlowTree (childDepth + 3) =>
      d2FlowTreeChild node q) hprojection
  change (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree
  rw [htree]
  exact hlocal

end Chvatal.D2Reserve
