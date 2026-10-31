import D2Stage14ActualLevelTwoBalance

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false

/-- Each Stage-14 level-two endpoint reserve is supplied by the Stage-13
level-three mid quota added to that child root. -/
theorem d2FlowCandidateStage14_actual_levelTwo_endpoint_reserves
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k,
      let output := d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k
      d2FlowCandidateCapacity (childDepth + 7) 2 14 <=
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨0, by omega⟩) /\
        d2FlowCandidateCapacity (childDepth + 7) 2 14 <=
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨7, by omega⟩) := by
  intro j k
  dsimp only
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 13
  let source := d2FlowTreeChild (d2FlowTreeChild before j) k
  have hfront := d2FlowCandidateStage13_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hinactive2 : d2FlowCandidateActive d 13 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hquotaReserve :=
    d2FlowCandidateStage14_levelTwo_reserve_from_stage13_levelThree_quota
      d (by omega)
  have htarget (q : Fin 8) :
      d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun d initial 14) j) k) q) =
      d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
              (childDepth + 5) 2 source) q) := by
    have hprojection := d2FlowStage_path3_projection
      (active := d2FlowCandidateActive d 13)
      (role := d2FlowCandidateRole d 13)
      (quota := d2FlowCandidateQuota d 13)
      (h := childDepth + 4) (i := 0) before j k q
    have hrun : d2FlowCandidateRun d initial 14 =
        d2FlowCandidateStage d 13 before := rfl
    have hroot := congrArg d2FlowTreeRootDeficit hprojection
    rw [hrun]
    exact hroot
  have hchildQuota (q : Fin 8) :
      d2FlowCandidateQuota d 13 3 .mid <=
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun d initial 14) j) k) q) := by
    rw [htarget q]
    cases hsource : source with
    | node G low high children =>
        rw [d2FlowStage_inactive_child children hinactive2 q]
        cases hchild : children q with
        | node Gq lowq highq grandchildren =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 13)
              (role := d2FlowCandidateRole d 13)
              (quota := d2FlowCandidateQuota d 13)
              (h := childDepth + 3) (i := 3)
              (G := Gq) (low := lowq) (high := highq)
              grandchildren hactive3
            rw [hrole3] at hdef
            simp at hdef
            rw [hdef]
            omega
  have hreserve (q : Fin 8) :
      d2FlowCandidateCapacity d 2 14 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun d initial 14) j) k) q) := by
    calc
      d2FlowCandidateCapacity d 2 14 <=
          128 * d2FlowCandidateQuota d 13 3 .mid := hquotaReserve
      _ <= _ := Nat.mul_le_mul_left 128 (hchildQuota q)
  change d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun d initial 14) j) k) ⟨0, by omega⟩) /\
    d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun d initial 14) j) k) ⟨7, by omega⟩)
  exact ⟨hreserve ⟨0, by omega⟩, hreserve ⟨7, by omega⟩⟩

end Chvatal.D2Reserve
