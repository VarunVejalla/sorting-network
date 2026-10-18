import FrontierRoutedReceivers
import FrontierReceiverGeometry

namespace Tapered945

open Chvatal

/-- The extra persistent information needed for contraction. At phase two,
the bottom source was freshly emitted by the preceding expansion. At phase
zero, its children retain the exact conserved cohort from that source. -/
structure CandidateFlowInvariant (d t : Nat) (P : RaggedWirePartition d) : Prop
    extends CandidateActualCounts d t P where
  fresh : t % 3 = 2 → ∀ b : KBag 64 d, b.l = candidateOmega t →
    |((P.sets b).card : Rat) - frontierBottomMass (candidateNativeCapacity d b.l)
      (candidateReferenceCapacity d b.l t) (bagAddressDebt b)| ≤ evenFlowBlockError
  history : t % 3 = 0 → ∀ (b : KBag 64 d) (hbd : b.l < d),
    b.l + 1 = candidateOmega t → Nonempty (BottomCohortHistory P b hbd
      (candidateNativeCapacity d b.l) (candidateReferenceCapacity d b.l (t - 1))
      (bagAddressDebt b))

section

variable {d t : Nat} (hd : 14 ≤ d) (ht0 : 1 ≤ t)
  (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
  (H : CandidateActualCounts d t P)

local notation "F" => candidateEvenFlowSplits hd t ht0 ht P H
local notation "Pnext" => candidateActualEvenStep hd t ht0 ht P H

/-- The shape table itself discharges the receiving port bounds throughout
the old band, except where the lower frontier sends whole registers. -/
theorem candidate_noncohort_receiver_error (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (hnotTop : q.l + 1 ≠ candidateAlpha d t)
    (hnotBottom : q.l ≠ candidateOmega t + 1)
    (hnotCohort : ¬ (q.l + 1 = candidateOmega t ∧
      candidateOmega t = candidateOmega (t + 1) + 1)) :
    |(((Pnext).sets q).card : Rat) - candidateFlowTarget d (t + 1) q| ≤ 69 := by
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have hlevels := candidate_inner_receiver_levels d hd t ht q hq hnotTop hnotBottom
  have how := candidate_omega_le_depth_minus_five d hd t (by omega)
  have hqd : q.l < d := by omega
  obtain ⟨htwo, hparentActive, hchildrenActive⟩ :=
    candidate_inner_receiver_sources d hd t ht0 ht q hq hnotTop hnotBottom hqd
  let b := q.parent (by norm_num : 1 ≤ 64)
  let j : Fin 64 := ⟨q.x % 64, Nat.mod_lt _ (by norm_num)⟩
  have hbd : b.l < d := by change q.l - 1 < d; omega
  have hdepth : b.l + 2 < d := by change q.l - 1 + 2 < d; omega
  have hchild : b.child j.val j.isLt hbd = q :=
    KBag.parent_child q (by omega) (by norm_num) hbd
  have hpm := candidate_inner_parent_mode d hd t htwo ht q hlevels.1 hlevels.2
  change (candidateFlowMode d t b = .topAdvance ∨ candidateFlowMode d t b = .interior ∨
    candidateFlowMode d t b = .topRetreat) at hpm
  have hcm := candidate_inner_children_mode d hd t htwo ht q hlevels.1 hlevels.2
    hnotCohort hqd
  have herr := candidate_regular_receiver_error hd ht0 ht P H b hparentActive j hdepth
    hpm (by
      intro k
      simpa only [hchild] using And.intro (hchildrenActive k) (hcm k))
  have hcapacity : candidateReferenceCapacity d q.l (t + 1) =
      4 * candidateReferenceCapacity d b.l t := by
    have hcap := candidate_reference_capacity_next_stage d hd t htTf b.l hparentActive.1.1
    have hl : q.l = b.l + 1 := by change q.l = q.l - 1 + 1; omega
    simpa only [← hl] using hcap
  have hdebt : bagAddressDebt q = debtStep (addressQ j.val) (bagAddressDebt b) := by
    simpa only [hchild] using bagAddressDebt_child b j.val j.isLt hbd
  have hnotBottomNext : q.l ≠ candidateOmega (t + 1) := by
    have hm := candidate_omega_frontier_moves_one t
    omega
  have hnotMeeting : candidateAlpha d (t + 1) ≠ candidateOmega (t + 1) := by
    have hlo := hq.1.1
    have hhi := hq.1.2
    omega
  have htopIff := candidate_inner_parent_top_iff d hd t htwo ht q hlevels.1 hlevels.2
  change (candidateFlowMode d t b = .topAdvance ↔ q.l = candidateAlpha d (t + 1)) at htopIff
  rw [candidate_flow_target_formula, if_neg (by omega),
    if_neg hnotBottomNext, hcapacity]
  simpa only [hchild, ← hdebt, htopIff] using herr

/-- The actual lower frontier and terminal meeting use the history generated
by the preceding expansion. Every source port comes from the same chosen
table as the regular receivers. -/
theorem candidate_cohort_receiver_error (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (hbottom : q.l + 1 = candidateOmega t)
    (hcontract : candidateOmega t = candidateOmega (t + 1) + 1)
    (hqd : q.l < d)
    (hHistory : Nonempty (BottomCohortHistory P q hqd
      (candidateNativeCapacity d q.l) (candidateReferenceCapacity d q.l (t - 1))
      (bagAddressDebt q))) :
    |(((Pnext).sets q).card : Rat) - candidateFlowTarget d (t + 1) q| ≤ 69 := by
  have htwo : 2 ≤ t := by
    by_contra hn
    have ht1 : t = 1 := by omega
    subst t
    norm_num [candidateOmega, candidateOmegaBase, Chvatal.ceilParity] at hcontract
  have hsep := candidate_frontiers_separated d hd t htwo ht
  have hnotTop : q.l + 1 ≠ candidateAlpha d t := by omega
  have hnotBottom : q.l ≠ candidateOmega t + 1 := by omega
  have hlevels := candidate_inner_receiver_levels d hd t ht q hq hnotTop hnotBottom
  obtain ⟨_, hpActive, hcActive⟩ :=
    candidate_inner_receiver_sources d hd t ht0 ht q hq hnotTop hnotBottom hqd
  let b := q.parent (by norm_num : 1 ≤ 64)
  let j : Fin 64 := ⟨q.x % 64, Nat.mod_lt _ (by norm_num)⟩
  let B := candidateNativeCapacity d q.l
  let C := candidateReferenceCapacity d b.l t
  let e := bagAddressDebt b
  have hbd : b.l < d := by change q.l - 1 < d; omega
  have hchild : b.child j.val j.isLt hbd = q :=
    KBag.parent_child q (by omega) (by norm_num) hbd
  have hdebt : bagAddressDebt q = debtStep (addressQ (q.x % 64)) e := by
    simpa only [hchild] using bagAddressDebt_child b j.val j.isLt hbd
  have hcapPrev : candidateReferenceCapacity d q.l (t - 1) = 1024 * C := by
    have htime : t - 1 + 1 = t := by omega
    have hqlevel : b.l + 1 = q.l := by change q.l - 1 + 1 = q.l; omega
    have hh := candidate_reference_capacity_previous_children d hd (t - 1) (by
      unfold candidateTerminalCutoff at ht; omega) b.l (by
        simpa only [htime] using hpActive.1.1)
    simpa only [htime, hqlevel] using hh
  obtain ⟨hist⟩ := hHistory
  have hist' : BottomCohortHistory P q hqd B (1024 * C)
      (debtStep (addressQ (q.x % 64)) e) := by
    simpa only [hcapPrev, hdebt] using hist
  have hwhole : ∀ k : Fin 64,
      (F (q.child k.val k.isLt hqd)).up = (P.sets (q.child k.val k.isLt hqd)).card := by
    intro k
    exact candidate_source_whole_up hd ht0 ht P H _ (hcActive k)
      (candidate_flow_mode_bottom_contraction d hd t ht0 ht _ hbottom hcontract)
  have hpm := candidate_inner_parent_mode d hd t htwo ht q hlevels.1 hlevels.2
  have hdown := candidate_source_block_error hd ht0 ht P H b hpActive j
  have htopIff := candidate_inner_parent_top_iff d hd t htwo ht q hlevels.1 hlevels.2
  have hnextLower : q.l = candidateOmega (t + 1) := by omega
  by_cases htop : candidateFlowMode d t b = .topAdvance
  · have hmeet : candidateAlpha d (t + 1) = candidateOmega (t + 1) := by
      have hh := htopIff.mp htop
      omega
    rw [candidate_flow_target_formula, if_pos (Or.inr hmeet)]
    apply routeEvenFlows_terminal_meeting P F q (by omega) hqd B C e hist'
    · simpa only [htop, scheduledDownTarget] using hdown
    · exact hwhole
  · have hntop : q.l ≠ candidateAlpha d (t + 1) := by
      intro hh
      exact htop (htopIff.mpr hh)
    have hnmeet : candidateAlpha d (t + 1) ≠ candidateOmega (t + 1) := by omega
    have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
    have hnextCapacity : candidateReferenceCapacity d q.l (t + 1) = 4 * C := by
      have hh := candidate_reference_capacity_next_stage d hd t htTf b.l hpActive.1.1
      have hl : q.l = b.l + 1 := by change q.l = q.l - 1 + 1; omega
      simpa only [← hl] using hh
    rw [candidate_flow_target_formula, if_neg (by omega), if_neg hntop,
      if_pos hnextLower, hnextCapacity, hdebt]
    apply routeEvenFlows_bottom_contraction P F q (by omega) hqd B C e hist'
    · rcases hpm with hm | hm | hm
      · exact False.elim (htop hm)
      · change candidateFlowMode d t b = .interior at hm
        rw [hm, scheduledDownTarget] at hdown
        exact hdown
      · change candidateFlowMode d t b = .topRetreat at hm
        rw [hm, scheduledDownTarget] at hdown
        exact hdown
    · exact hwhole

theorem candidate_entering_lower_receiver_error (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (hlevel : q.l = candidateOmega t + 1) :
    |(((Pnext).sets q).card : Rat) - frontierBottomMass (candidateNativeCapacity d q.l)
      (candidateReferenceCapacity d q.l (t + 1)) (bagAddressDebt q)| ≤ evenFlowBlockError := by
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have how := candidate_omega_le_depth_minus_five d hd t (by omega)
  have horder := candidate_frontiers_order d hd t (by omega)
  let b := q.parent (by norm_num : 1 ≤ 64)
  let j : Fin 64 := ⟨q.x % 64, Nat.mod_lt _ (by norm_num)⟩
  have hbLevel : b.l = candidateOmega t := by change q.l - 1 = candidateOmega t; omega
  have hb : candidateScheduledActive d t b := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hbLevel]; exact horder
    · rw [hbLevel]
    · rw [hbLevel]; exact candidate_omega_parity t
  have hbd : b.l < d := by omega
  have hdepth : b.l + 2 < d := by omega
  have hchild : b.child j.val j.isLt hbd = q :=
    KBag.parent_child q (by omega) (by norm_num) hbd
  have hmove : candidateOmega (t + 1) = candidateOmega t + 1 := by
    have hm := candidate_omega_frontier_moves_one t
    have hqhi := hq.1.2
    omega
  have herr := candidate_expansion_child_error hd ht0 ht P H b hb hbLevel hmove j hdepth
  have hl : b.l + 1 = q.l := by change q.l - 1 + 1 = q.l; omega
  simpa only [hchild, hl] using herr

/-- All actual next counts satisfy their own shape targets. Frontier errors
are proved from the chosen source table and cohort history, rather than
assumed as extra discrepancy hypotheses. -/
theorem candidate_next_actual_counts (I : CandidateFlowInvariant d t P) :
    CandidateActualCounts d (t + 1) Pnext := by
  refine ⟨candidateActualEvenStep_even hd t ht0 ht P H,
    candidateActualEvenStep_inactive hd ht0 ht P H, ?_⟩
  intro q hq
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have ha := candidate_alpha_frontier_moves_one d hd t htTf
  have ho := candidate_omega_frontier_moves_one t
  have hqlo := hq.1.1
  have hqhi := hq.1.2
  have how := candidate_omega_le_depth_minus_five d hd (t + 1) (by omega)
  have hqd : q.l < d := by omega
  by_cases hnewTop : q.l + 1 = candidateAlpha d t
  · have hmove : candidateAlpha d t = candidateAlpha d (t + 1) + 1 := by omega
    rw [candidate_entering_upper_target d hd t ht0 ht q hnewTop hmove]
    exact candidate_top_retreat_receiver_error hd ht0 ht P H q hq hnewTop hmove hqd
  · by_cases hnewBottom : q.l = candidateOmega t + 1
    · have hmove : candidateOmega (t + 1) = candidateOmega t + 1 := by omega
      rw [candidate_entering_lower_target d hd t ht0 ht q hnewBottom hmove]
      exact (candidate_entering_lower_receiver_error hd ht0 ht P H q hq hnewBottom).trans
        evenFlowBlockError_le
    · by_cases hcohort : q.l + 1 = candidateOmega t ∧
          candidateOmega t = candidateOmega (t + 1) + 1
      · have hphase : t % 3 = 0 := by
          by_contra hn
          have hm := (candidate_lower_phase_direction t).2 hn
          omega
        exact candidate_cohort_receiver_error hd ht0 ht P H q hq hcohort.1 hcohort.2 hqd
          (I.history hphase q hqd hcohort.1)
      · exact candidate_noncohort_receiver_error hd ht0 ht P H q hq hnewTop hnewBottom hcohort

/-- The invariant propagates through every phase, including both directions
of each frontier and the terminal meeting. Phase-two freshness generates the
phase-zero cohort history needed by the next contraction. -/
theorem candidate_flow_invariant_step (I : CandidateFlowInvariant d t P) :
    CandidateFlowInvariant d (t + 1) Pnext := by
  refine ⟨candidate_next_actual_counts hd ht0 ht P H I, ?_, ?_⟩
  · intro hphase q hqLevel
    have hprevPhase : t % 3 ≠ 0 := by omega
    have hmove := (candidate_lower_phase_direction t).2 hprevPhase
    have hnewLevel : q.l = candidateOmega t + 1 := by omega
    have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
    have horder := candidate_frontiers_order d hd (t + 1) (by omega)
    have hq : candidateScheduledActive d (t + 1) q := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hqLevel]; exact horder
      · rw [hqLevel]
      · rw [hqLevel]; exact candidate_omega_parity (t + 1)
    exact candidate_entering_lower_receiver_error hd ht0 ht P H q hq hnewLevel
  · intro hphase b hbd hlevel
    have hprevPhase : t % 3 = 2 := by omega
    have hmove := (candidate_lower_phase_direction t).2 (by omega : t % 3 ≠ 0)
    have hbLevel : b.l = candidateOmega t := by omega
    have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
    have horder := candidate_frontiers_order d hd t (by omega)
    have hb : candidateScheduledActive d t b := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hbLevel]; exact horder
      · rw [hbLevel]
      · rw [hbLevel]; exact candidate_omega_parity t
    have how := candidate_omega_le_depth_minus_five d hd t (by omega)
    have hdepth : b.l + 2 < d := by omega
    have hist := candidate_expansion_cohort_history hd ht0 ht P H b hb hbLevel hmove
      hdepth (I.fresh hprevPhase b hbLevel) (by omega)
    exact ⟨by simpa only [Nat.add_sub_cancel] using hist⟩
end

end Tapered945
