import D2FlowLocality
import D2SchedulePeriodSix

namespace Chvatal.D2Reserve

/-! The bulk six-stage shift conjugates the actual recursive tree operator
when the whole subtree stays away from both moving frontiers. This is the
operator-level step needed before comparing reachable run states. -/

theorem d2FlowCandidateStage_eq_of_bulk_shift
    {d t i h : Nat}
    (ht : 2 ≤ t) (horizon : t + 6 ≤ tfD2 d)
    (hpositive : 3 * d < 2 * t + 11)
    (hupper : ∀ k, k ≤ h → 3 * (i + k) < t + 2)
    (hbelow : ∀ k, k ≤ h → i + k < omega t)
    (hnotEdge : ∀ k, k ≤ h → i + k + 2 ≠ omega t)
    (tree : D2FlowTree h) :
    d2FlowStage (d2FlowCandidateActive d (t + 6))
        (d2FlowCandidateRole d (t + 6))
        (d2FlowCandidateQuota d (t + 6)) h (i + 4) tree =
      d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t) h i tree := by
  classical
  apply d2FlowStage_eq_of_callbacks_agree
  · intro k hk
    rw [d2FlowCandidateActive_matches_schedule (t := t + 6) (by omega),
      d2FlowCandidateActive_matches_schedule (t := t) (by omega)]
    have hiff := active_add_six_four_iff (d := d) (tf := tfD2 d)
      (i := i + k) (t := t) ht horizon
    have hiff' : active d (tfD2 d) (i + k + 4) (t + 6) ↔
        active d (tfD2 d) (i + k) t := by
      constructor
      · intro hnew
        exact (hiff.mp hnew).1
      · intro hold
        exact hiff.mpr ⟨hold, hupper k hk⟩
    have hpos : i + 4 + k = i + k + 4 := by omega
    rw [hpos]
    by_cases hold : active d (tfD2 d) (i + k) t
    · have hnew := hiff'.2 hold
      simp [hold, hnew]
    · have hnew : ¬ active d (tfD2 d) (i + k + 4) (t + 6) := by
        intro hn
        exact hold (hiff'.1 hn)
      simp [hold, hnew]
  · intro k hk
    rw [d2FlowCandidateRole_matches_schedule (by omega),
      d2FlowCandidateRole_matches_schedule (by omega)]
    have hrole := d2ScheduleRole_add_six_four_of_away_from_bottom
      (d := d) (i := i + k) (t := t) ht hpositive
      (hbelow k hk) (hnotEdge k hk)
    have hpos : i + 4 + k = i + k + 4 := by omega
    simpa [hpos] using hrole
  · intro k hk r
    have hquota := d2FlowCandidateQuota_add_six_four d (i + k) t r
    have hpos : i + 4 + k = i + k + 4 := by omega
    simpa [hpos] using hquota

end Chvatal.D2Reserve
