import FrontierScheduleGate

namespace Tapered945

open Chvatal

/-- Except for the special first-level bootstrap and the final meeting, the
candidate's parity band has distinct upper and lower frontiers. -/
theorem candidate_frontiers_separated (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d) :
    candidateAlpha d t + 2 ≤ candidateOmega t := by
  have htime : t + 24 ≤ 3 * d := by
    unfold candidateTerminalCutoff candidateTf at ht
    omega
  have hbase : candidateAlphaBase d t + 2 ≤ candidateOmegaBase t := by
    unfold candidateAlphaBase candidateOmegaBase
    have hmod : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases hmod with h | h | h <;> omega
  unfold candidateAlpha candidateOmega Chvatal.ceilParity
  split_ifs <;> omega

theorem candidate_frontiers_stage_one (d : Nat) (hd : 14 ≤ d) :
    candidateAlpha d 1 = 1 ∧ candidateOmega 1 = 1 := by
  have hbase : (2 * 1 + 23) / 3 - d = 0 := by omega
  simp [candidateAlpha, candidateAlphaBase, candidateOmega, candidateOmegaBase,
    hbase, Chvatal.ceilParity]

/-- Each lower contraction is preceded by two lower expansions. The finite
bootstrap starts at phase one, so its first contraction also has this form. -/
theorem candidate_lower_phase_direction (t : Nat) :
    (t % 3 = 0 → candidateOmega (t + 1) + 1 = candidateOmega t) ∧
    (t % 3 ≠ 0 → candidateOmega (t + 1) = candidateOmega t + 1) := by
  unfold candidateOmega candidateOmegaBase Chvatal.ceilParity
  constructor <;> intro h <;> split_ifs <;> omega

def candidateNativeCapacity (d l : Nat) : Rat := (64 : Rat) ^ (d - l)

theorem candidate_native_child (d l : Nat) (hl : l < d) :
    candidateNativeCapacity d (l + 1) = candidateNativeCapacity d l / 64 := by
  have he : d - l = (d - (l + 1)) + 1 := by omega
  unfold candidateNativeCapacity
  rw [he, pow_succ]
  ring

theorem candidate_native_binary (d l : Nat) (hl : l ≤ d) :
    candidateNativeCapacity d l = (2 : Rat) ^ (6 * d - 6 * l) := by
  unfold candidateNativeCapacity
  rw [show (64 : Rat) = 2 ^ 6 by norm_num, ← pow_mul]
  congr 1
  omega

theorem candidate_reference_capacity_previous_children (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (l : Nat)
    (hl : candidateAlpha d (t + 1) ≤ l) :
    candidateReferenceCapacity d (l + 1) t =
      1024 * candidateReferenceCapacity d l (t + 1) := by
  have hlo := candidate_alpha_exponent_bound d hd (t + 1) (by omega)
  have he : candidateCapacityExponent d (l + 1) t =
      candidateCapacityExponent d l (t + 1) + 10 := by
    unfold candidateCapacityExponent at *
    omega
  unfold candidateReferenceCapacity
  rw [he, pow_add]
  norm_num
  ring

/-- The shape selects port rules; top and bottom targets are unchanged when
their direction flips. The singleton bootstrap and terminal meeting use a
native count target. -/
def candidateFlowMode (d t : Nat) (b : KBag 64 d) : ScheduledFlowShape :=
  if t = 1 then .bootstrap
  else if candidateAlpha d t = candidateOmega t then .meeting
  else if b.l = candidateAlpha d t then
    if candidateAlpha d (t + 1) = candidateAlpha d t + 1 then .topAdvance
    else .topRetreat
  else if b.l = candidateOmega t then
    if candidateOmega (t + 1) = candidateOmega t + 1 then .bottomExpansion
    else .bottomContraction
  else .interior

def candidateFlowTarget (d t : Nat) (b : KBag 64 d) : Rat :=
  scheduledFlowTarget (candidateFlowMode d t b) (candidateNativeCapacity d b.l)
    (candidateReferenceCapacity d b.l t) (bagAddressDebt b)

theorem candidate_flow_target_formula (d t : Nat) (b : KBag 64 d) :
    candidateFlowTarget d t b =
      if t = 1 ∨ candidateAlpha d t = candidateOmega t then candidateNativeCapacity d b.l
      else if b.l = candidateAlpha d t then
        frontierTopMass (candidateReferenceCapacity d b.l t) (bagAddressDebt b)
      else if b.l = candidateOmega t then
        frontierBottomMass (candidateNativeCapacity d b.l)
          (candidateReferenceCapacity d b.l t) (bagAddressDebt b)
      else (1 - 1 / cap) * candidateReferenceCapacity d b.l t := by
  unfold candidateFlowTarget candidateFlowMode
  split_ifs <;> simp_all [scheduledFlowTarget]

theorem candidate_flow_mode_top (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (hb : b.l = candidateAlpha d t) :
    candidateFlowMode d t b =
      if candidateAlpha d (t + 1) = candidateAlpha d t + 1 then .topAdvance
      else .topRetreat := by
  have hsep := candidate_frontiers_separated d hd t ht0 ht
  simp [candidateFlowMode, show t ≠ 1 by omega, show candidateAlpha d t ≠
    candidateOmega t by omega, hb]

theorem candidate_flow_mode_bottom (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (hb : b.l = candidateOmega t) :
    candidateFlowMode d t b =
      if candidateOmega (t + 1) = candidateOmega t + 1 then .bottomExpansion
      else .bottomContraction := by
  have hsep := candidate_frontiers_separated d hd t ht0 ht
  simp [candidateFlowMode, show t ≠ 1 by omega, show candidateAlpha d t ≠
    candidateOmega t by omega, hb, show candidateOmega t ≠ candidateAlpha d t by omega]

theorem candidate_flow_mode_interior (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (ha : candidateAlpha d t < b.l) (ho : b.l < candidateOmega t) :
    candidateFlowMode d t b = .interior := by
  simp [candidateFlowMode, show t ≠ 1 by omega,
    show candidateAlpha d t ≠ candidateOmega t by omega,
    show b.l ≠ candidateAlpha d t by omega, show b.l ≠ candidateOmega t by omega]

theorem candidate_flow_mode_top_advance (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (hb : b.l = candidateAlpha d t)
    (hmove : candidateAlpha d (t + 1) = candidateAlpha d t + 1) :
    candidateFlowMode d t b = .topAdvance := by
  have htwo : 2 ≤ t := by
    by_contra h
    have ht1 : t = 1 := by omega
    subst t
    have h1 := candidate_frontiers_stage_one d hd
    have h2 := candidate_frontiers_stage_two d hd
    change candidateAlpha d 2 = candidateAlpha d 1 + 1 at hmove
    rw [h1.1, h2.1] at hmove
    norm_num at hmove
  rw [candidate_flow_mode_top d hd t htwo ht b hb, if_pos hmove]

theorem candidate_flow_mode_bottom_contraction (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d)
    (b : KBag 64 d) (hb : b.l = candidateOmega t)
    (hmove : candidateOmega t = candidateOmega (t + 1) + 1) :
    candidateFlowMode d t b = .bottomContraction := by
  have htwo : 2 ≤ t := by
    by_contra h
    have ht1 : t = 1 := by omega
    subst t
    norm_num [candidateOmega, candidateOmegaBase, Chvatal.ceilParity] at hmove
  rw [candidate_flow_mode_bottom d hd t htwo ht b hb, if_neg (by omega)]

end Tapered945
