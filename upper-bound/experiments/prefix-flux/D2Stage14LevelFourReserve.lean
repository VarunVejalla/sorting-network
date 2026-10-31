import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 1000000

/-- Actual Stage-14 level-four endpoint reserves follow from the visible
Stage-13 bottom-descending update at each level-five child. -/
theorem d2FlowCandidateStage14_actual_levelFour_endpoint_reserves
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k m l,
      let output := d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l
      d2FlowCandidateCapacity (childDepth + 7) 4 14 <=
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨0, by omega⟩) /\
        d2FlowCandidateCapacity (childDepth + 7) 4 14 <=
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨7, by omega⟩) := by
  intro j k m l
  dsimp only
  let d := childDepth + 7
  let run13 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run13 j) k) m) l
  have hfront := d2FlowCandidateStage13_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hinactive4 : d2FlowCandidateActive d 13 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hquotaReserve :=
    d2FlowCandidateStage14_levelFour_halfQuota_covers_capacity d (by omega)
  have hparentOutput (q : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateStage d 13 run13) j) k) m) l) q) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (childDepth + 3) 4 parent) q) := by
    have hproj := d2FlowStage_path5_projection
      (active := d2FlowCandidateActive d 13)
      (role := d2FlowCandidateRole d 13)
      (quota := d2FlowCandidateQuota d 13)
      (h := childDepth + 2) (i := 0) run13 j k m l q
    simpa [run13, d, parent, d2FlowCandidateRun, d2FlowCandidateStage] using hproj
  have hchildOutput (q : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (childDepth + 3) 4 parent) q) >=
      d2FlowCandidateQuota d 13 5 .botDesc := by
    cases hparent : parent with
    | node G low high children =>
      have hinactive := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 13)
        (role := d2FlowCandidateRole d 13)
        (quota := d2FlowCandidateQuota d 13)
        (h := childDepth + 2) (i := 4) (G := G) (low := low)
        (high := high) children hinactive4 q
      cases hnode : children q with
      | node Gq lowq highq grandchildren =>
        have hdef := d2FlowStage_active_node_deficit
          (active := d2FlowCandidateActive d 13)
          (role := d2FlowCandidateRole d 13)
          (quota := d2FlowCandidateQuota d 13)
          (h := childDepth + 1) (i := 5) (G := Gq)
          (low := lowq) (high := highq) grandchildren hactive5
        have hrole : d2FlowCandidateRole d 13 5 = .botDesc := hrole5
        rw [hrole] at hdef
        rw [d2FlowStage_inactive_child children hinactive4 q, hnode]
        simp at hdef
        rw [hdef]
        omega
  have hreserve (q : Fin 8) :
      d2FlowCandidateCapacity d 4 14 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
              (childDepth + 3) 4 parent) q) := by
    have hout := hchildOutput q
    calc
      d2FlowCandidateCapacity d 4 14 <=
          128 * (d2FlowCandidateQuota d 13 5 .botDesc / 2) := hquotaReserve
      _ <= 128 * d2FlowCandidateQuota d 13 5 .botDesc :=
        Nat.mul_le_mul_left 128 (Nat.div_le_self _ _)
      _ <= _ := Nat.mul_le_mul_left 128 hout
  have htarget (q : Fin 8) :
      d2FlowCandidateCapacity d 4 14 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateStage d 13 run13) j) k) m) l) q) := by
    rw [hparentOutput q]
    exact hreserve q
  constructor
  · exact htarget ⟨0, by omega⟩
  · exact htarget ⟨7, by omega⟩

end Chvatal.D2Reserve
