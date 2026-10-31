import D2Stage15Frontier
import D2Stage16Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

/-- Every actual Stage-16 level-six node is balanced: Stage 15's active
level-five middle sender writes it as one of its ordinary cut children. -/
theorem d2FlowCandidateRun_stage16_levelSix_balanced
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r : Fin 8) :
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 16) j) k) m) l) q) r)).2.1 +
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 16) j) k) m) l) q) r)).2.2 =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 16) j) k) m) l) q) r) := by
  let d := childDepth + 7
  let run15 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let path2 := d2FlowTreeChild (d2FlowTreeChild run15 j) k
  let path4 := d2FlowTreeChild (d2FlowTreeChild path2 m) l
  let path5 := d2FlowTreeChild path4 q
  have hactive : d2FlowCandidateActive d 15 5 = true := by
    have h := d2FlowCandidateActive_stage15_at (d := d) (by dsimp [d]; omega)
    exact h.2.2.1
  have hrole : d2FlowCandidateRole d 15 5 = .mid :=
    d2FlowCandidateRole_stage15_internal_mid (by dsimp [d]; omega)
      5 (Or.inr rfl)
  have hregular : d2FlowCandidateRole d 15 5 = .topRise \/
      d2FlowCandidateRole d 15 5 = .mid \/
      d2FlowCandidateRole d 15 5 = .botDesc := Or.inr (Or.inl hrole)
  have hprojection := d2FlowStage_path6_tree_projection
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (h := childDepth + 1) (i := 0) run15 j k m l q r
  have hprojection' := hprojection
  simp only [Nat.zero_add] at hprojection'
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 15)
                  (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
                  d 0 run15) j) k) m) l) q) r =
    d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (childDepth + 1 + 1) 5 path5) r at hprojection'
  have hrun16 : d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) 16 =
      d2FlowCandidateStage d 15 run15 := by
    rw [d2FlowCandidateRun]
  cases hsource : path5 with
  | node G low high children =>
      have hlocal := d2FlowStage_regular_child_balanced
        (active := d2FlowCandidateActive d 15)
        (role := d2FlowCandidateRole d 15)
        (quota := d2FlowCandidateQuota d 15)
        (h := childDepth + 1) (i := 5) (G := G)
        (low := low) (high := high) children hactive hregular r
      have hprojectionNode := hprojection'
      rw [hsource] at hprojectionNode
      rw [show d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 16 =
          d2FlowCandidateStage d 15 run15 by simpa [d] using hrun16]
      simp only [d2FlowCandidateStage]
      rw [hprojectionNode]
      simpa using hlocal

/-- The Stage-16 level-six bottom-descending quota satisfies the sender cap
and parity requirements at every actual depth. -/
theorem d2FlowCandidateStage16_levelSix_quota_gates
    {d : Nat} (hd : 14 <= d) :
    256 * d2FlowCandidateQuota d 16 6 .botDesc <=
        d2FlowCandidateCapacity d 6 16 /\
      d2FlowCandidateQuota d 16 6 .botDesc % 2 = 0 := by
  classical
  have hactive : d2FlowCandidateActive d 16 6 = true := by
    rw [d2FlowCandidateActive_stage16_iff hd]
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole : d2FlowCandidateRole d 16 6 = .botDesc :=
    d2FlowCandidateRole_stage16_bottom hd
  have hactiveRaw : active d (tfD2 d) 6 16 := by
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 6) (t := 16) (by omega)
    rw [hactive] at hm
    exact of_decide_eq_true hm.symm
  have hroleSchedule : d2ScheduleRole d 6 16 = .botDesc := by
    have hm := d2FlowCandidateRole_matches_schedule
      (d := d) (i := 6) (t := 16) (by omega)
    exact hm.symm.trans hrole
  have hregular : d2ScheduleRole d 6 16 = .topRise \/
      d2ScheduleRole d 6 16 = .mid \/
      d2ScheduleRole d 6 16 = .botDesc := Or.inr (Or.inr hroleSchedule)
  have hcap := d2FlowCandidateQuota_le_capacity_div_256
    (by omega) hactiveRaw hregular
  have heven := d2FlowCandidateQuota_even
    (by omega) hactiveRaw (by omega) hregular
  exact ⟨by simpa [hroleSchedule] using hcap,
    by simpa [hroleSchedule, d2FlowCandidateRole] using heven⟩

end Chvatal.D2Reserve
