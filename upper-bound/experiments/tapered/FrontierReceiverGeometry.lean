import FrontierBandGeometry

namespace Tapered945

open Chvatal

/-- Once the two newly entering frontier families are excluded, a receiver
lies between an active parent and active children of the preceding stage. -/
theorem candidate_inner_receiver_levels (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (hnotTop : q.l + 1 ≠ candidateAlpha d t)
    (hnotBottom : q.l ≠ candidateOmega t + 1) :
    candidateAlpha d t + 1 ≤ q.l ∧ q.l + 1 ≤ candidateOmega t := by
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have ha := candidate_alpha_frontier_moves_one d hd t htTf
  have ho := candidate_omega_frontier_moves_one t
  have hap := candidate_alpha_parity d t
  have hop := candidate_omega_parity t
  have hqlo := hq.1.1
  have hqhi := hq.1.2
  have hqp := hq.2
  constructor <;> omega

theorem candidate_inner_receiver_sources (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (hnotTop : q.l + 1 ≠ candidateAlpha d t)
    (hnotBottom : q.l ≠ candidateOmega t + 1) (hqd : q.l < d) :
    2 ≤ t ∧ candidateScheduledActive d t (q.parent (by norm_num)) ∧
    ∀ j : Fin 64, candidateScheduledActive d t (q.child j.val j.isLt hqd) := by
  have hlevels := candidate_inner_receiver_levels d hd t ht q hq hnotTop hnotBottom
  have htwo : 2 ≤ t := by
    by_contra hn
    have ht1 : t = 1 := by omega
    subst t
    have h1 := candidate_frontiers_stage_one d hd
    omega
  have hp := hq.2
  refine ⟨htwo, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · change candidateAlpha d t ≤ q.l - 1; omega
  · change q.l - 1 ≤ candidateOmega t; omega
  · change (q.l - 1) % 2 = t % 2; omega
  · intro j
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change candidateAlpha d t ≤ q.l + 1; omega
    · change q.l + 1 ≤ candidateOmega t; omega
    · change (q.l + 1) % 2 = t % 2; omega

theorem candidate_inner_parent_mode (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hlo : candidateAlpha d t + 1 ≤ q.l) (hhi : q.l + 1 ≤ candidateOmega t) :
    candidateFlowMode d t (q.parent (by norm_num)) = .topAdvance ∨
      candidateFlowMode d t (q.parent (by norm_num)) = .interior ∨
      candidateFlowMode d t (q.parent (by norm_num)) = .topRetreat := by
  by_cases htop : (q.parent (by norm_num)).l = candidateAlpha d t
  · rw [candidate_flow_mode_top d hd t ht0 ht _ htop]
    split_ifs <;> simp
  · have hl : candidateAlpha d t < (q.parent (by norm_num)).l := by
      change q.l - 1 ≠ candidateAlpha d t at htop
      change candidateAlpha d t < q.l - 1
      omega
    have hh : (q.parent (by norm_num)).l < candidateOmega t := by
      change q.l - 1 < candidateOmega t
      omega
    exact Or.inr (Or.inl (candidate_flow_mode_interior d hd t ht0 ht _ hl hh))

theorem candidate_inner_children_mode (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hlo : candidateAlpha d t + 1 ≤ q.l) (hhi : q.l + 1 ≤ candidateOmega t)
    (hnotCohort : ¬ (q.l + 1 = candidateOmega t ∧
      candidateOmega t = candidateOmega (t + 1) + 1)) (hqd : q.l < d) :
    ∀ j : Fin 64, candidateFlowMode d t (q.child j.val j.isLt hqd) = .interior ∨
      candidateFlowMode d t (q.child j.val j.isLt hqd) = .bottomExpansion := by
  intro j
  by_cases hb : q.l + 1 = candidateOmega t
  · have hmove : candidateOmega (t + 1) = candidateOmega t + 1 := by
      have hm := candidate_omega_frontier_moves_one t
      omega
    right
    rw [candidate_flow_mode_bottom d hd t ht0 ht _ hb, if_pos hmove]
  · left
    apply candidate_flow_mode_interior d hd t ht0 ht
    · change candidateAlpha d t < q.l + 1; omega
    · change q.l + 1 < candidateOmega t; omega

theorem candidate_inner_parent_top_iff (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 2 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hlo : candidateAlpha d t + 1 ≤ q.l) (hhi : q.l + 1 ≤ candidateOmega t) :
    candidateFlowMode d t (q.parent (by norm_num)) = .topAdvance ↔
      q.l = candidateAlpha d (t + 1) := by
  have ha := candidate_alpha_frontier_moves_one d hd t (by
    unfold candidateTerminalCutoff at ht; omega)
  by_cases hp : (q.parent (by norm_num)).l = candidateAlpha d t
  · rw [candidate_flow_mode_top d hd t ht0 ht _ hp]
    change q.l - 1 = candidateAlpha d t at hp
    split_ifs <;> simp_all <;> omega
  · have hl : candidateAlpha d t < (q.parent (by norm_num)).l := by
      change q.l - 1 ≠ candidateAlpha d t at hp
      change candidateAlpha d t < q.l - 1
      omega
    have hh : (q.parent (by norm_num)).l < candidateOmega t := by
      change q.l - 1 < candidateOmega t; omega
    rw [candidate_flow_mode_interior d hd t ht0 ht _ hl hh]
    change q.l - 1 ≠ candidateAlpha d t at hp
    constructor
    · intro he; cases he
    · intro he; exfalso; omega

theorem candidate_entering_lower_target (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hlevel : q.l = candidateOmega t + 1)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1) :
    candidateFlowTarget d (t + 1) q =
      frontierBottomMass (candidateNativeCapacity d q.l)
        (candidateReferenceCapacity d q.l (t + 1)) (bagAddressDebt q) := by
  have hgap : candidateAlpha d (t + 1) < q.l := by
    by_cases ht1 : t = 1
    · subst t
      have ha := (candidate_frontiers_stage_two d hd).1
      have ho := (candidate_frontiers_stage_one d hd).2
      change candidateAlpha d 2 < q.l
      omega
    · have hs := candidate_frontiers_separated d hd t (by omega) ht
      have hm := candidate_alpha_frontier_moves_one d hd t (by
        unfold candidateTerminalCutoff at ht; omega)
      omega
  rw [candidate_flow_target_formula, if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem candidate_entering_upper_target (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) (q : KBag 64 d)
    (hlevel : q.l + 1 = candidateAlpha d t)
    (hmove : candidateAlpha d t = candidateAlpha d (t + 1) + 1) :
    candidateFlowTarget d (t + 1) q =
      frontierTopMass (candidateReferenceCapacity d q.l (t + 1)) (bagAddressDebt q) := by
  have hgap : q.l < candidateOmega (t + 1) := by
    by_cases ht1 : t = 1
    · subst t
      have ha := (candidate_frontiers_stage_one d hd).1
      have ho := (candidate_frontiers_stage_two d hd).2
      change q.l < candidateOmega 2
      omega
    · have hs := candidate_frontiers_separated d hd t (by omega) ht
      have hm := candidate_omega_frontier_moves_one t
      omega
  rw [candidate_flow_target_formula, if_neg (by omega), if_pos (by omega)]

end Tapered945
