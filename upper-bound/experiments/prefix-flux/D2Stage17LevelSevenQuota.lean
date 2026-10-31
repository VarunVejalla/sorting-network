import D2Stage17Frontier

namespace Chvatal.D2Reserve

/-- Stage 17 level seven satisfies the schedule-only quota cap and parity
needed by its bottom-descending sender contract. -/
theorem d2FlowCandidateStage17_levelSeven_quota_gates
    {d : Nat} (hd : 14 <= d) :
    256 * d2FlowCandidateQuota d 17 7 .botDesc <=
        d2FlowCandidateCapacity d 7 17 /\
      d2FlowCandidateQuota d 17 7 .botDesc % 2 = 0 := by
  classical
  have hactiveBool : d2FlowCandidateActive d 17 7 = true :=
    (d2FlowCandidateActive_stage17_iff hd).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := 7) (t := 17) (by omega)
  rw [hactiveBool] at hmatch
  have hactive : active d (tfD2 d) 7 17 := of_decide_eq_true hmatch.symm
  have hroleCandidate : d2FlowCandidateRole d 17 7 = .botDesc :=
    d2FlowCandidateRole_stage17_bottom hd
  have hrole : d2ScheduleRole d 7 17 = .botDesc := by
    simpa [d2FlowCandidateRole] using hroleCandidate
  have hcap := d2FlowCandidateQuota_le_capacity_div_256
    (by omega) hactive (Or.inr (Or.inr hrole))
  have heven := d2FlowCandidateQuota_even
    (by omega) hactive (by omega) (Or.inr (Or.inr hrole))
  exact And.intro (by simpa [hrole] using hcap)
    (by simpa [hroleCandidate] using heven)

end Chvatal.D2Reserve
