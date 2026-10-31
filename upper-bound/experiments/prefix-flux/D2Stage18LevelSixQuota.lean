import D2Stage18LevelSevenInputs
import D2Stage17LevelSevenBalance
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Stage-17's level-seven bottom-descending quota gives a large reserve for
the Stage-18 level-six middle sender. The exact scale is a factor 15/128 of
the latter's capacity. -/
theorem d2FlowCandidateStage18_levelSix_quota_arithmetic
    {d : Nat} (hd : 14 <= d) :
    256 * d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowCandidateCapacity d 6 18 /\
    128 * d2FlowCandidateQuota d 17 7 .botDesc =
      15 * d2FlowCandidateCapacity d 6 18 /\
    d2FlowCandidateQuota d 18 6 .mid <=
      8 * d2FlowCandidateQuota d 17 7 .botDesc /\
    d2FlowCandidateCapacity d 6 18 <=
      128 * d2FlowCandidateQuota d 17 7 .botDesc /\
    d2FlowCandidateQuota d 18 6 .mid % 2 = 0 := by
  have he18 : d2FlowCandidateCapacityExponent d 6 18 = 3 * d - 9 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have he17 : d2FlowCandidateCapacityExponent d 7 17 = 3 * d - 4 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hq18 : d2FlowCandidateQuota d 18 6 .mid =
      15 * 2 ^ (3 * d - 21) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 6 18 - 12) = _
    rw [he18]
    congr 1 <;> omega
  have hq17 : d2FlowCandidateQuota d 17 7 .botDesc =
      15 * 2 ^ (3 * d - 16) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 7 17 - 12) = _
    rw [he17]
    congr 1 <;> omega
  have hcap : d2FlowCandidateCapacity d 6 18 = 2 ^ (3 * d - 9) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 6 18 = _
    rw [he18]
  have hquotaCap : 256 * d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowCandidateCapacity d 6 18 := by
    rw [hq18, hcap]
    have hexp : 8 + (3 * d - 21) = 3 * d - 13 := by omega
    have hcapExp : 3 * d - 9 = 4 + (3 * d - 13) := by omega
    rw [show 256 = 2 ^ 8 by norm_num]
    rw [show 2 ^ 8 * (15 * 2 ^ (3 * d - 21)) =
      15 * (2 ^ 8 * 2 ^ (3 * d - 21)) by ring]
    rw [← pow_add, hexp, hcapExp, pow_add]
    omega
  have hratio : 128 * d2FlowCandidateQuota d 17 7 .botDesc =
      15 * d2FlowCandidateCapacity d 6 18 := by
    rw [hq17, hcap]
    have hexp : 7 + (3 * d - 16) = 3 * d - 9 := by omega
    rw [show 128 = 2 ^ 7 by norm_num]
    rw [show 2 ^ 7 * (15 * 2 ^ (3 * d - 16)) =
      15 * (2 ^ 7 * 2 ^ (3 * d - 16)) by ring]
    rw [← pow_add, hexp]
  have hcover : d2FlowCandidateQuota d 18 6 .mid <=
      8 * d2FlowCandidateQuota d 17 7 .botDesc := by
    rw [hq18, hq17]
    have hexp : 3 * d - 16 = 5 + (3 * d - 21) := by omega
    rw [hexp, pow_add]
    omega
  have hreserve : d2FlowCandidateCapacity d 6 18 <=
      128 * d2FlowCandidateQuota d 17 7 .botDesc := by
    rw [hratio]
    omega
  have heven : d2FlowCandidateQuota d 18 6 .mid % 2 = 0 := by
    rw [hq18]
    have hexp : 3 * d - 21 = (3 * d - 22) + 1 := by omega
    rw [hexp, pow_succ]
    omega
  exact ⟨hquotaCap, hratio, hcover, hreserve, heven⟩

/-- Each level-seven child below a Stage-18 level-six sender has received the
Stage-17 level-seven bottom-descending quota. -/
theorem d2FlowCandidateRun_stage18_levelSix_child_quota_floor
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    d2FlowCandidateQuota d 17 7 .botDesc <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run18 j) k) m) l) q) r) s) := by
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
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run17 j) k) m) l) q) r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse6 : d2FlowCandidateActive d 17 6 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage17_iff
      (d := d) (i := 6) hd14).mp ht
    rcases hlevels with h | h | h | h <;> omega
  have hactive7 : d2FlowCandidateActive d 17 7 = true :=
    (d2FlowCandidateActive_stage17_iff hd14).2
      (Or.inr (Or.inr (Or.inr rfl)))
  have hrole7 : d2FlowCandidateRole d 17 7 = .botDesc :=
    d2FlowCandidateRole_stage17_bottom hd14
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  have hproject :
      d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run18 j) k) m) l) q) r) s =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 17)
          (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
          (height + 2) 6 parent) s := by
    rw [hrun18]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path7_child_projection
      (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (h := height + 1) (i := 0) run17 j k m l q r s
  cases hp : parent with
  | node G6 low6 high6 children6 =>
      have hstep := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 17)
        (role := d2FlowCandidateRole d 17)
        (quota := d2FlowCandidateQuota d 17)
        (h := height + 1) (i := 6) (G := G6)
        (low := low6) (high := high6) children6 hfalse6 s
      have hchildStage :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 17)
              (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
              (height + 2) 6 (.node G6 low6 high6 children6)) s =
          d2FlowStage (d2FlowCandidateActive d 17)
            (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
            (height + 1) 7 (children6 s) := by
        simpa using hstep
      cases hc : children6 s with
      | node G7 low7 high7 grandchildren =>
          have hdef := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 17)
            (role := d2FlowCandidateRole d 17)
            (quota := d2FlowCandidateQuota d 17)
            (h := height) (i := 7) (G := G7)
            (low := low7) (high := high7) grandchildren hactive7
          have hdef' : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 17)
                (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                (height + 1) 7 (.node G7 low7 high7 grandchildren)) =
              G7 + d2FlowCandidateQuota d 17 7 .botDesc := by
            simpa [hrole7] using hdef
          have hlocal : d2FlowCandidateQuota d 17 7 .botDesc <=
              d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 17)
                  (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                  (height + 1) 7 (children6 s)) := by
            rw [hc, hdef']
            omega
          have hrootEq :
              d2FlowTreeRootDeficit
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild
                          (d2FlowTreeChild
                            (d2FlowTreeChild
                              (d2FlowTreeChild run18 j) k) m) l) q) r) s) =
                d2FlowTreeRootDeficit
                  (d2FlowStage (d2FlowCandidateActive d 17)
                    (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                    (height + 1) 7 (children6 s)) := by
            calc
              _ = d2FlowTreeRootDeficit
                  (d2FlowTreeChild
                    (d2FlowStage (d2FlowCandidateActive d 17)
                      (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                      (height + 2) 6 parent) s) := by
                    simpa [d, initial, run17, run18] using
                      congrArg d2FlowTreeRootDeficit hproject
              _ = d2FlowTreeRootDeficit
                  (d2FlowStage (d2FlowCandidateActive d 17)
                    (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
                    (height + 1) 7 (children6 s)) := by
                    simpa [parent, hp] using
                      congrArg d2FlowTreeRootDeficit hchildStage
          simpa [d, initial, run17, run18] using hrootEq.symm ▸ hlocal

end Chvatal.D2Reserve
