import D2Stage16Frontier
import D2ScheduleReserve

namespace Chvatal.D2Reserve

theorem d2FlowCandidateStage17_alpha {d : Nat} (hd : 14 <= d) :
    alpha d 17 = 1 := d2FlowCandidateStage16_alpha_next hd

theorem d2FlowCandidateStage17_alpha_next {d : Nat} (hd : 14 <= d) :
    alpha d 18 = (if d <= 15 then 2 else 0) := by
  by_cases h14 : d = 14
  case pos => subst d; norm_num [alpha, alphaStar, ceilParity]
  case neg =>
    by_cases h15 : d = 15
    case pos => subst d; norm_num [alpha, alphaStar, ceilParity]
    case neg =>
      have hz : 47 <= 3 * d := by omega
      simp [alpha, alphaStar, ceilParity, hz]
      omega

theorem d2FlowCandidateStage17_omega : omega 17 = 7 := by
  norm_num [omega, ceilParity]

theorem d2FlowCandidateStage17_omega_next : omega 18 = 8 := by
  norm_num [omega, ceilParity]

end Chvatal.D2Reserve
namespace Chvatal.D2Reserve

theorem d2FlowCandidateActive_stage17_iff {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 17 i = true <->
      i = 1 \/ i = 3 \/ i = 5 \/ i = 7 := by
  classical
  constructor
  case mp =>
    intro ha
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 17) (by omega)
    rw [ha] at hm
    have hp : active d (tfD2 d) i 17 := of_decide_eq_true hm.symm
    have ht1 : (17 : Nat) ≠ 1 := by omega
    unfold active at hp
    simp only [if_neg ht1] at hp
    have hlo : 3 * i + 3 * d >= 45 := hp.2.2.2.1
    have hup : 3 * i < 25 := hp.2.2.2.2
    omega
  case mpr =>
    intro hi
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 17) (by omega)
    rw [hm]
    apply decide_eq_true
    have ht1 : (17 : Nat) ≠ 1 := by omega
    unfold active
    simp only [if_neg ht1]
    have htf : 17 <= tfD2 d := by unfold tfD2; omega
    have hpar : i % 2 = 17 % 2 := by rcases hi with h | h | h | h <;> omega
    have hlo : 3 * i + 3 * d >= 45 := by rcases hi with h | h | h | h <;> omega
    have hup : 3 * i < 25 := by rcases hi with h | h | h | h <;> omega
    exact And.intro (by omega) (And.intro htf (And.intro hpar (And.intro hlo hup)))

end Chvatal.D2Reserve

namespace Chvatal.D2Reserve

theorem d2FlowCandidateRole_stage17_top {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 17 1 = (if d <= 15 then .topDesc else .topRise) := by
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 1) (t := 17) (by omega)]
  by_cases h : d <= 15
  case pos => simp [d2ScheduleRole, d2FlowCandidateStage17_alpha hd,
    d2FlowCandidateStage17_alpha_next hd, h]
  case neg => simp [d2ScheduleRole, d2FlowCandidateStage17_alpha hd,
    d2FlowCandidateStage17_alpha_next hd, h]

theorem d2FlowCandidateRole_stage17_mid3 {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 17 3 = .mid := by
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 3) (t := 17) (by omega)]
  simp [d2ScheduleRole, d2FlowCandidateStage17_alpha hd,
    d2FlowCandidateStage17_omega]

theorem d2FlowCandidateRole_stage17_mid5 {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 17 5 = .mid := by
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 5) (t := 17) (by omega)]
  simp [d2ScheduleRole, d2FlowCandidateStage17_alpha hd,
    d2FlowCandidateStage17_omega]

theorem d2FlowCandidateRole_stage17_bottom {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 17 7 = .botDesc := by
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 7) (t := 17) (by omega)]
  simp [d2ScheduleRole, d2FlowCandidateStage17_alpha hd,
    d2FlowCandidateStage17_omega, d2FlowCandidateStage17_omega_next]

end Chvatal.D2Reserve
