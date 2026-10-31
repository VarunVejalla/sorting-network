import D2FlowLocality

namespace Chvatal.D2Reserve

private theorem ceilParity_add_six_same (m t : Nat) :
    ceilParity m (t + 6) = ceilParity m t := by
  unfold ceilParity
  simp [Nat.add_mod]

private theorem ceilParity_add_two_same (m t : Nat) :
    ceilParity (m + 2) (t + 6) = ceilParity m t + 2 := by
  unfold ceilParity
  by_cases h : m % 2 = t % 2 <;> simp [h, Nat.add_mod]

private theorem omega_add_six_local {t : Nat} (ht : 2 ≤ t) :
    omega (t + 6) = omega t + 2 := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht60 : t + 6 ≠ 0 := by omega
  have ht61 : t + 6 ≠ 1 := by omega
  have hdiv : (t + 10) / 3 = (t + 4) / 3 + 2 := by omega
  simp only [omega, if_neg ht0, if_neg ht1, if_neg ht60, if_neg ht61, hdiv]
  exact ceilParity_add_two_same _ _

theorem alpha_add_depth_four_stage_six {d t : Nat} (ht : 2 ≤ t) :
    alpha (d + 4) (t + 6) = alpha d t := by
  have hstar : alphaStar (d + 4) (t + 6) = alphaStar d t := by
    unfold alphaStar
    have hcond : 2 * (t + 6) + 11 ≤ 3 * (d + 4) ↔
        2 * t + 11 ≤ 3 * d := by omega
    by_cases hz : 2 * t + 11 ≤ 3 * d
    · simp [hcond, hz]
    · simp only [hcond, hz, if_false]
      have hnum : 2 * (t + 6) + 11 - 3 * (d + 4) + 2 =
          2 * t + 11 - 3 * d + 2 := by omega
      rw [hnum]
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht60 : t + 6 ≠ 0 := by omega
  have ht61 : t + 6 ≠ 1 := by omega
  simp only [alpha, if_neg ht0, if_neg ht1, if_neg ht60, if_neg ht61, hstar]
  exact ceilParity_add_six_same _ _

theorem tfD2_add_four {d : Nat} (hd : 5 ≤ d) :
    tfD2 (d + 4) = tfD2 d + 12 := by
  unfold tfD2
  omega

theorem d2FlowCandidateCapacityExponent_add_depth_four_stage_six
    (d i t : Nat) :
    d2FlowCandidateCapacityExponent (d + 4) i (t + 6) =
      d2FlowCandidateCapacityExponent d i t := by
  simp [d2FlowCandidateCapacityExponent]
  omega

theorem d2FlowCandidateActive_add_depth_four_stage_six
    {d i t : Nat} (hd : 5 ≤ d) (ht : 2 ≤ t)
    (horizon : t ≤ tfD2 d) (hi : i < omega t) :
    d2FlowCandidateActive (d + 4) (t + 6) i =
      d2FlowCandidateActive d t i := by
  classical
  rw [d2FlowCandidateActive_matches_schedule (d := d + 4) (t := t + 6)
      (by omega),
    d2FlowCandidateActive_matches_schedule (d := d) (t := t) (by omega)]
  have hiff : active (d + 4) (tfD2 (d + 4)) i (t + 6) ↔
      active d (tfD2 d) i t := by
    rw [active_iff_frontiers (d := d + 4) (tf := tfD2 (d + 4))
        (i := i) (t := t + 6) (by omega),
      active_iff_frontiers (d := d) (tf := tfD2 d) (i := i) (t := t) ht]
    rw [tfD2_add_four hd, alpha_add_depth_four_stage_six ht,
      omega_add_six_local ht]
    have hpar : (t + 6) % 2 = t % 2 := by omega
    rw [hpar]
    constructor
    · rintro ⟨htf, hα, hω, hpar⟩
      exact ⟨by omega, hα, Nat.le_of_lt hi, by omega⟩
    · rintro ⟨htf, hα, hω, hpar⟩
      exact ⟨by omega, hα, by omega, by omega⟩
  by_cases hold : active d (tfD2 d) i t
  · have hnew := hiff.mpr hold
    simp [hold, hnew]
  · have hnew : ¬ active (d + 4) (tfD2 (d + 4)) i (t + 6) := by
      intro hn
      exact hold (hiff.mp hn)
    simp [hold, hnew]

theorem d2FlowCandidateRole_add_depth_four_stage_six
    {d i t : Nat} (ht : 2 ≤ t) (hi : i < omega t) :
    d2FlowCandidateRole (d + 4) (t + 6) i =
      d2FlowCandidateRole d t i := by
  rw [d2FlowCandidateRole_matches_schedule (by omega),
    d2FlowCandidateRole_matches_schedule (by omega)]
  have hnext : alpha (d + 4) (t + 6 + 1) = alpha d (t + 1) := by
    have h := alpha_add_depth_four_stage_six (d := d) (t := t + 1) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have homega := omega_add_six_local ht
  simp [d2ScheduleRole, alpha_add_depth_four_stage_six (d := d) (t := t) ht,
    hnext, homega,
    (show i ≠ omega t by omega),
    (show i ≠ omega t + 2 by omega)]

theorem d2FlowCandidateQuota_add_depth_four_stage_six
    (d i t : Nat) (r : D2Role) :
    d2FlowCandidateQuota (d + 4) (t + 6) i r =
      d2FlowCandidateQuota d t i r := by
  simp [d2FlowCandidateQuota,
    d2FlowCandidateCapacityExponent_add_depth_four_stage_six]

/-- The one-step profile update itself respects the depth/time shift. Equal
radius-two input profiles produce equal radius-one output profiles whenever
the root and its children stay above the old bottom frontier. -/
theorem d2FlowCandidateRootProfile_eq_of_depth_shift
    {d t i h₁ h₂ : Nat} (hd : 5 ≤ d) (ht : 2 ≤ t)
    (horizon : t ≤ tfD2 d)
    (hbelow : ∀ k, k ≤ 1 → i + k < omega t)
    (treeNew : D2FlowTree (h₁ + 2))
    (treeOld : D2FlowTree (h₂ + 2))
    (hprofile : d2FlowStageRootSecondProfile treeNew =
      d2FlowStageRootSecondProfile treeOld) :
    d2FlowStageRootProfile
        (d2FlowStage (d2FlowCandidateActive (d + 4) (t + 6))
          (d2FlowCandidateRole (d + 4) (t + 6))
          (d2FlowCandidateQuota (d + 4) (t + 6)) (h₁ + 2) i treeNew) =
      d2FlowStageRootProfile
        (d2FlowStage (d2FlowCandidateActive d t)
          (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
          (h₂ + 2) i treeOld) := by
  have ha0 := d2FlowCandidateActive_add_depth_four_stage_six hd ht horizon
    (hbelow 0 (by omega))
  have hr0 := d2FlowCandidateRole_add_depth_four_stage_six
    (d := d) (i := i) (t := t) ht
    (hbelow 0 (by omega))
  have hq0 : ∀ r,
      d2FlowCandidateQuota (d + 4) (t + 6) i r =
        d2FlowCandidateQuota d t i r := by
    intro r
    exact d2FlowCandidateQuota_add_depth_four_stage_six d i t r
  have hq0role :
      d2FlowCandidateQuota (d + 4) (t + 6) i
          (d2FlowCandidateRole (d + 4) (t + 6) i) =
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) := by
    rw [hr0]
    exact hq0 (d2FlowCandidateRole d t i)
  have ha1 := d2FlowCandidateActive_add_depth_four_stage_six hd ht horizon
    (hbelow 1 (by omega))
  have hr1 := d2FlowCandidateRole_add_depth_four_stage_six
    (d := d) (i := i + 1) (t := t) ht
    (hbelow 1 (by omega))
  have hq1 : ∀ r,
      d2FlowCandidateQuota (d + 4) (t + 6) (i + 1) r =
        d2FlowCandidateQuota d t (i + 1) r := by
    intro r
    exact d2FlowCandidateQuota_add_depth_four_stage_six d (i + 1) t r
  have hq1role :
      d2FlowCandidateQuota (d + 4) (t + 6) (i + 1)
          (d2FlowCandidateRole (d + 4) (t + 6) (i + 1)) =
        d2FlowCandidateQuota d t (i + 1)
          (d2FlowCandidateRole d t (i + 1)) := by
    rw [hr1]
    exact hq1 (d2FlowCandidateRole d t (i + 1))
  exact d2FlowStage_rootProfile_eq_of_rootSecondProfile_eq
    (active₁ := d2FlowCandidateActive (d + 4) (t + 6))
    (active₂ := d2FlowCandidateActive d t)
    (role₁ := d2FlowCandidateRole (d + 4) (t + 6))
    (role₂ := d2FlowCandidateRole d t)
    (quota₁ := d2FlowCandidateQuota (d + 4) (t + 6))
    (quota₂ := d2FlowCandidateQuota d t)
    treeNew treeOld hprofile ha0 hr0 hq0role ha1 hr1 hq1role

/-- In a subtree wholly above the old bottom frontier, increasing the input
depth by four and advancing six stages leaves its recursive tree operator
unchanged. The moving bottom strip is the sole excluded region. -/
theorem d2FlowCandidateStage_eq_of_bulk_depth_shift
    {d t i h : Nat} (hd : 5 ≤ d) (ht : 2 ≤ t)
    (horizon : t ≤ tfD2 d)
    (hbelow : ∀ k, k ≤ h → i + k < omega t)
    (tree : D2FlowTree h) :
    d2FlowStage (d2FlowCandidateActive (d + 4) (t + 6))
        (d2FlowCandidateRole (d + 4) (t + 6))
        (d2FlowCandidateQuota (d + 4) (t + 6)) h i tree =
      d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t) h i tree := by
  apply d2FlowStage_eq_of_callbacks_agree
  · intro k hk
    exact d2FlowCandidateActive_add_depth_four_stage_six hd ht horizon
      (hbelow k hk)
  · intro k hk
    exact d2FlowCandidateRole_add_depth_four_stage_six ht (hbelow k hk)
  · intro k hk r
    exact d2FlowCandidateQuota_add_depth_four_stage_six d (i + k) t r

end Chvatal.D2Reserve
