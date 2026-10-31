import D2TopDescHistory

namespace Chvatal.D2Reserve

/-- At every active positive stage, level zero is on the top frontier and
that frontier is moving away from it. Hence an active root is
top-descending, never an ordinary sender. -/
theorem d2FlowCandidate_root_active_is_topDesc
    {d t : Nat} (hd : 7 ≤ d) (ht : 2 ≤ t)
    (ha : active d (tfD2 d) 0 t) :
    d2ScheduleRole d 0 t = .topDesc := by
  have hactive :
      2 ≤ t ∧ t ≤ tfD2 d ∧ 0 % 2 = t % 2 ∧
        3 * d ≥ 2 * t + 11 ∧ 0 < t + 8 := by
    simpa [active, show t ≠ 1 by omega] using ha
  have hpar : t % 2 = 0 := by omega
  have hAlpha : alpha d t = 0 := by
    unfold alpha
    simp only [show t ≠ 0 by omega, show t ≠ 1 by omega]
    unfold ceilParity alphaStar
    simp only [if_pos (by omega : 2 * t + 11 ≤ 3 * d)]
    simp [hpar]
  have hnext : 0 < alpha d (t + 1) := by
    unfold alpha
    simp only [show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega]
    have hodd : (t + 1) % 2 = 1 := by omega
    unfold ceilParity
    change (if alphaStar d (t + 1) % 2 = (t + 1) % 2 then
      alphaStar d (t + 1) else alphaStar d (t + 1) + 1) > 0
    rw [hodd]
    by_cases hparity : alphaStar d (t + 1) % 2 = 1
    · simp [hparity]
      omega
    · simp [hparity]
  unfold d2ScheduleRole
  simp [hAlpha, hnext]

/-- The moving-root case of the affine sender profile: at every active root
snapshot after the two-stage startup, the actual candidate run has zero root
deficit, using the already-proved top-descending reset history. -/
theorem d2FlowCandidate_active_root_zero_of_prior_core
    {d t : Nat} (hd : 7 ≤ d) (ht : 4 ≤ t)
    (ha : active d (tfD2 d) 0 t)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t - 2) k)
      (fun k => d2FlowCandidateRole d (t - 2) k)
      (fun k => d2FlowCandidateCapacity d k (t - 2)) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2))) :
    d2FlowTreeRootDeficit
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) = 0 := by
  have hrole := d2FlowCandidate_root_active_is_topDesc hd (by omega) ha
  have hdeq : d - 1 + 1 = d := by omega
  have ha' : active (d - 1 + 1) (tfD2 (d - 1 + 1)) 0 t := by
    simpa [hdeq] using ha
  have hcoreRewritten := hcore
  rw [← hdeq] at hcoreRewritten
  have hcore' : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (d - 1 + 1) (t - 2) k)
      (fun k => d2FlowCandidateRole (d - 1 + 1) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (d - 1 + 1) k (t - 2)) 0
      (d2FlowCandidateRun (d - 1 + 1)
        (d2FlowTreeInitial 8192 (d - 1 + 1)) (t - 2)) := hcoreRewritten
  have hrole' : d2ScheduleRole (d - 1 + 1) 0 t = .topDesc := by
    simpa [hdeq] using hrole
  have hzero := d2FlowCandidateRun_active_topDesc_root_zero_of_prior_core
    (h := d - 1) (i := 0) (t := t) (by omega) ht ha' hrole' hcore' .nil
  rw [hdeq] at hzero
  simpa [hdeq] using hzero

end Chvatal.D2Reserve
