import D2Stage18LevelFiveInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

theorem d2FlowCandidateStage18_levelFour_quota_arithmetic
    {d : Nat} (hd : 14 <= d) :
    256 * d2FlowCandidateQuota d 18 4 .mid <=
      d2FlowCandidateCapacity d 4 18 /\
    128 * d2FlowCandidateQuota d 17 5 .mid =
      15 * d2FlowCandidateCapacity d 4 18 /\
    d2FlowCandidateQuota d 18 4 .mid <=
      8 * d2FlowCandidateQuota d 17 5 .mid /\
    d2FlowCandidateCapacity d 4 18 <=
      128 * d2FlowCandidateQuota d 17 5 .mid /\
    d2FlowCandidateQuota d 18 4 .mid % 2 = 0 := by
  have he18 : d2FlowCandidateCapacityExponent d 4 18 = 3 * d - 15 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have he17 : d2FlowCandidateCapacityExponent d 5 17 = 3 * d - 10 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hq18 : d2FlowCandidateQuota d 18 4 .mid =
      15 * 2 ^ (3 * d - 27) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 4 18 - 12) = _
    rw [he18]
    congr 1 <;> omega
  have hq17 : d2FlowCandidateQuota d 17 5 .mid =
      15 * 2 ^ (3 * d - 22) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 5 17 - 12) = _
    rw [he17]
    congr 1 <;> omega
  have hcap : d2FlowCandidateCapacity d 4 18 = 2 ^ (3 * d - 15) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 4 18 = _
    rw [he18]
  have hquotaCap : 256 * d2FlowCandidateQuota d 18 4 .mid <=
      d2FlowCandidateCapacity d 4 18 := by
    rw [hq18, hcap]
    have hexp : 8 + (3 * d - 27) = 3 * d - 19 := by omega
    have hcapExp : 3 * d - 15 = 4 + (3 * d - 19) := by omega
    rw [show 256 = 2 ^ 8 by norm_num]
    rw [show 2 ^ 8 * (15 * 2 ^ (3 * d - 27)) =
      15 * (2 ^ 8 * 2 ^ (3 * d - 27)) by ring]
    rw [← pow_add, hexp, hcapExp, pow_add]
    omega
  have hratio : 128 * d2FlowCandidateQuota d 17 5 .mid =
      15 * d2FlowCandidateCapacity d 4 18 := by
    rw [hq17, hcap]
    have hexp : 7 + (3 * d - 22) = 3 * d - 15 := by omega
    rw [show 128 = 2 ^ 7 by norm_num]
    rw [show 2 ^ 7 * (15 * 2 ^ (3 * d - 22)) =
      15 * (2 ^ 7 * 2 ^ (3 * d - 22)) by ring]
    rw [← pow_add, hexp]
  have hcover : d2FlowCandidateQuota d 18 4 .mid <=
      8 * d2FlowCandidateQuota d 17 5 .mid := by
    rw [hq18, hq17]
    have hexp : 3 * d - 22 = 5 + (3 * d - 27) := by omega
    rw [hexp, pow_add]
    omega
  have hreserve : d2FlowCandidateCapacity d 4 18 <=
      128 * d2FlowCandidateQuota d 17 5 .mid := by
    rw [hratio]
    omega
  have heven : d2FlowCandidateQuota d 18 4 .mid % 2 = 0 := by
    rw [hq18]
    have hexp : 3 * d - 27 = (3 * d - 28) + 1 := by omega
    rw [hexp, pow_succ]
    omega
  exact ⟨hquotaCap, hratio, hcover, hreserve, heven⟩

/-- Every level-five child root below a Stage-18 level-four sender has
received the Stage-17 level-five middle quota. -/
theorem d2FlowCandidateRun_stage18_levelFour_child_quota_floor
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    d2FlowCandidateQuota d 17 5 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) := by
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun (height + 8) (d2FlowTreeInitial 8192 (height + 8)) 18
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run17 j) k) m) l
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse4 : d2FlowCandidateActive d 17 4 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage17_iff
      (d := d) (i := 4) hd14).mp ht
    rcases hlevels with h | h | h | h <;> omega
  have hactive5 : d2FlowCandidateActive d 17 5 = true :=
    (d2FlowCandidateActive_stage17_iff hd14).2
      (Or.inr (Or.inr (Or.inl rfl)))
  have hrole5 : d2FlowCandidateRole d 17 5 = .mid :=
    d2FlowCandidateRole_stage17_mid5 hd14
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  have hproject :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 4) 4 parent) q) := by
    rw [hrun18]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path5_projection
      (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (h := height + 3) (i := 0) run17 j k m l q
  cases hp : parent with
  | node G4 low4 high4 children4 =>
      have hstep := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 17)
        (role := d2FlowCandidateRole d 17)
        (quota := d2FlowCandidateQuota d 17)
        (h := height + 3) (i := 4) (G := G4)
        (low := low4) (high := high4) children4 hfalse4 q
      have hchildStage :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 17)
              (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
              (height + 4) 4 (.node G4 low4 high4 children4)) q =
          d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 3) 5 (children4 q) := by
        simpa using hstep
      cases hc : children4 q with
      | node G5 low5 high5 grandchildren =>
          have hdef := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 17)
            (role := d2FlowCandidateRole d 17)
            (quota := d2FlowCandidateQuota d 17)
            (h := height + 2) (i := 5) (G := G5)
            (low := low5) (high := high5) grandchildren hactive5
          have hdef' : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 17)
                (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                (height + 3) 5 (.node G5 low5 high5 grandchildren)) =
              G5 + d2FlowCandidateQuota d 17 5 .mid := by
            simpa [hrole5] using hdef
          have hlocal : d2FlowCandidateQuota d 17 5 .mid <=
              d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 17)
                  (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                  (height + 3) 5 (children4 q)) := by
            rw [hc, hdef']
            omega
          have hrootEq :
              d2FlowTreeRootDeficit
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild
                          (d2FlowTreeChild run18 j) k) m) l) q) =
                d2FlowTreeRootDeficit
                  (d2FlowStage (d2FlowCandidateActive d 17)
                    (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                    (height + 3) 5 (children4 q)) := by
            calc
              _ = d2FlowTreeRootDeficit
                  (d2FlowTreeChild
                    (d2FlowStage (d2FlowCandidateActive d 17)
                      (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                      (height + 4) 4 parent) q) := by
                    exact hproject
              _ = d2FlowTreeRootDeficit
                  (d2FlowStage (d2FlowCandidateActive d 17)
                    (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                    (height + 3) 5 (children4 q)) := by
                    simpa [parent, hp] using
                      congrArg d2FlowTreeRootDeficit hchildStage
          simpa [d, initial, run17, run18] using hrootEq.symm ▸ hlocal

end Chvatal.D2Reserve
