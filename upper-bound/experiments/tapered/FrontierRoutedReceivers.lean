import FrontierFlowSupport
import FrontierRootRoute

namespace Tapered945

open Chvatal

theorem EvenFlowSplit.block_zero_of_count {count : Nat} (F : EvenFlowSplit count)
    (hn : count = 0) (j : Fin 64) : F.blocks j = 0 :=
  F.block_zero_of_whole (by have := F.up_le; omega) j

section

variable {d t : Nat} (hd : 14 ≤ d) (ht0 : 1 ≤ t)
  (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
  (H : CandidateActualCounts d t P)

local notation "F" => candidateEvenFlowSplits hd t ht0 ht P H
local notation "Pnext" => candidateActualEvenStep hd t ht0 ht P H

theorem candidate_child_routed_count (b : KBag 64 d) (j : Fin 64)
    (hdepth : b.l + 2 < d) :
    ((Pnext).sets (b.child j.val j.isLt (by omega))).card = (F b).blocks j +
      ∑ k : Fin 64,
        (F ((b.child j.val j.isLt (by omega)).child k.val k.isLt (by
          change b.l + 1 < d; omega))).up := by
  rw [candidateActualEvenStep, routeEvenFlows_card _ _ _ (by
    change 1 ≤ b.l + 1; omega) (by change b.l + 1 < d; omega)]
  have hidx : (b.child j.val j.isLt (by omega)).x % 64 = j.val := by
    simp [KBag.child, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  have hp : (b.child j.val j.isLt (by omega)).parent (by norm_num) = b :=
    KBag.child_parent b j.val j.isLt (by omega) (by norm_num)
  rw [hp]
  have hj : (⟨(b.child j.val j.isLt (by omega)).x % 64,
      Nat.mod_lt _ (by norm_num)⟩ : Fin 64) = j := Fin.ext hidx
  rw [hj]

/-- A newly expanded bottom child has no incoming up-ports from below the
old active band. Its actual register is exactly the chosen parent block. -/
theorem candidate_expansion_child_exact (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hbottom : b.l = candidateOmega t)
    (j : Fin 64) (hdepth : b.l + 2 < d) :
    ((Pnext).sets (b.child j.val j.isLt (by omega))).card = (F b).blocks j := by
  rw [candidate_child_routed_count hd ht0 ht P H b j hdepth]
  have hzero : ∀ k : Fin 64,
      (F ((b.child j.val j.isLt (by omega)).child k.val k.isLt (by
        change b.l + 1 < d; omega))).up = 0 := by
    intro k
    apply candidateEvenFlowSplits_inactive_up hd t ht0 ht P H
    intro hactive
    have ho := hactive.1.2
    change b.l + 1 + 1 ≤ candidateOmega t at ho
    omega
  simp only [hzero, Finset.sum_const_zero, Nat.add_zero]

theorem candidate_expansion_child_error (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hbottom : b.l = candidateOmega t)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1)
    (j : Fin 64) (hdepth : b.l + 2 < d) :
    |(((Pnext).sets (b.child j.val j.isLt (by omega))).card : Rat) -
      frontierBottomMass (candidateNativeCapacity d (b.l + 1))
        (candidateReferenceCapacity d (b.l + 1) (t + 1))
        (bagAddressDebt (b.child j.val j.isLt (by omega)))| ≤ evenFlowBlockError := by
  rw [candidate_expansion_child_exact hd ht0 ht P H b hb hbottom j hdepth]
  have herr := candidate_source_block_error hd ht0 ht P H b hb j
  have hmode : candidateFlowMode d t b = .bootstrap ∨
      candidateFlowMode d t b = .bottomExpansion := by
    by_cases h1 : t = 1
    · exact Or.inl (by simp [candidateFlowMode, h1])
    · right
      rw [candidate_flow_mode_bottom d hd t (by omega) ht b hbottom, if_pos hmove]
  have hTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  rw [candidate_native_child d b.l (by omega),
    candidate_reference_capacity_next_stage d hd t hTf b.l hb.1.1,
    bagAddressDebt_child]
  rcases hmode with hm | hm <;>
    simpa only [hm, scheduledDownTarget] using herr

/-- The contracted receiver's correlation is generated from actual expansion
children in this very route. No independent child error bound is summed. -/
noncomputable def candidate_expansion_cohort_history (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hbottom : b.l = candidateOmega t)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1)
    (hdepth : b.l + 2 < d)
    (hfresh : |((P.sets b).card : Rat) -
      frontierBottomMass (candidateNativeCapacity d b.l)
        (candidateReferenceCapacity d b.l t) (bagAddressDebt b)| ≤ evenFlowBlockError)
    (hnotBoot : 2 ≤ t) :
    BottomCohortHistory Pnext b (by omega) (candidateNativeCapacity d b.l)
      (candidateReferenceCapacity d b.l t) (bagAddressDebt b) := by
  apply bottomCohortHistoryOfExpansion P Pnext b (by omega) _ _ _ (F b) hfresh
  · have hu := candidate_source_up_error hd ht0 ht P H b hb
    rw [candidate_flow_mode_bottom d hd t hnotBoot ht b hbottom, if_pos hmove,
      scheduledUpTarget] at hu
    exact hu
  · intro j
    exact candidate_expansion_child_exact hd ht0 ht P H b hb hbottom j hdepth

theorem candidate_retreat_routed_count (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (htop : q.l + 1 = candidateAlpha d t) (hqd : q.l < d) :
    ((Pnext).sets q).card = ∑ j : Fin 64, (F (q.child j.val j.isLt hqd)).up := by
  have hparentInactive (hp : 1 ≤ q.l) :
      ¬ candidateScheduledActive d t (q.parent (by norm_num)) := by
    intro h
    have hlo := h.1.1
    change candidateAlpha d t ≤ q.l - 1 at hlo
    omega
  by_cases hzero : q.l = 0
  · have hroot : q = KBag.root 64 d := by
      have hx := q.hx
      simp only [hzero, pow_zero] at hx
      apply KBag.ext <;> simp [KBag.root] <;> omega
    subst q
    rw [candidateActualEvenStep, routeEvenFlows, RaggedWirePartition.route,
      routeRaggedWires_root_card (by omega : 1 ≤ d)]
    have hinactive : ¬ candidateScheduledActive d t (KBag.root 64 d) := by
      intro h
      have hlo := h.1.1
      change candidateAlpha d t ≤ 0 at hlo
      change 0 + 1 = candidateAlpha d t at htop
      omega
    simp only [EvenFlowSplit.wireSplit_up,
      candidateEvenFlowSplits_inactive_up hd t ht0 ht P H _ hinactive, Nat.zero_add]
  · rw [candidateActualEvenStep, routeEvenFlows_card _ _ q (by omega) hqd]
    have hz := (F (q.parent (by norm_num))).block_zero_of_count
      (H.inactive _ (hparentInactive (by omega)))
        ⟨q.x % 64, Nat.mod_lt _ (by norm_num)⟩
    rw [hz, Nat.zero_add]

theorem candidate_top_retreat_receiver_error (q : KBag 64 d)
    (hq : candidateScheduledActive d (t + 1) q)
    (htop : q.l + 1 = candidateAlpha d t)
    (hmove : candidateAlpha d t = candidateAlpha d (t + 1) + 1)
    (hqd : q.l < d) :
    |(((Pnext).sets q).card : Rat) -
      frontierTopMass (candidateReferenceCapacity d q.l (t + 1)) (bagAddressDebt q)| ≤ 69 := by
  let C := candidateReferenceCapacity d q.l (t + 1)
  let e := bagAddressDebt q
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have how := candidate_frontiers_order d hd t (by omega)
  have hparq := hq.2
  have hscale := candidate_reference_capacity_previous_children d hd t htTf q.l hq.1.1
  have hups : ∀ j : Fin 64,
      |((F (q.child j.val j.isLt hqd)).up : Rat) -
        frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e)| ≤ 1 := by
    intro j
    have hj : candidateScheduledActive d t (q.child j.val j.isLt hqd) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change candidateAlpha d t ≤ q.l + 1; omega
      · change q.l + 1 ≤ candidateOmega t; omega
      · change (q.l + 1) % 2 = t % 2; omega
    have hu := candidate_source_up_error hd ht0 ht P H _ hj
    have hm : candidateFlowMode d t (q.child j.val j.isLt hqd) = .bootstrap ∨
        candidateFlowMode d t (q.child j.val j.isLt hqd) = .topRetreat := by
      by_cases ht1 : t = 1
      · left; simp [candidateFlowMode, ht1]
      · right
        rw [candidate_flow_mode_top d hd t (by omega) ht _ htop,
          if_neg (by omega)]
    rcases hm with hm | hm
    all_goals
      rw [hm, scheduledUpTarget, bagAddressDebt_child] at hu
      change |((F (q.child j.val j.isLt hqd)).up : Rat) -
        frontierTopRetreatUp (candidateReferenceCapacity d (q.l + 1) t)
          (debtStep (addressQ j.val) e)| ≤ 1 at hu
      simpa only [hscale] using hu
  have hactual : (((Pnext).sets q).card : Rat) =
      ∑ j : Fin 64, ((F (q.child j.val j.isLt hqd)).up : Rat) := by
    exact_mod_cast candidate_retreat_routed_count hd ht0 ht P H q hq htop hqd
  exact (top_retreat_receiver_discrepancy _ _ C e hups hactual).trans (by norm_num)

/-- Ordinary and upper-advance receivers share the same physical count
equation. The upper parent keeps its own down target; all incoming child
up-ports have the ordinary interior target. -/
theorem candidate_regular_receiver_error (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (j : Fin 64) (hdepth : b.l + 2 < d)
    (hparent : candidateFlowMode d t b = .topAdvance ∨
      candidateFlowMode d t b = .interior ∨ candidateFlowMode d t b = .topRetreat)
    (hchildren : ∀ k : Fin 64,
      let q := (b.child j.val j.isLt (by omega)).child k.val k.isLt (by
        change b.l + 1 < d; omega)
      candidateScheduledActive d t q ∧
        (candidateFlowMode d t q = .interior ∨ candidateFlowMode d t q = .bottomExpansion)) :
    |(((Pnext).sets (b.child j.val j.isLt (by omega))).card : Rat) -
      (if candidateFlowMode d t b = .topAdvance then
        frontierTopMass (4 * candidateReferenceCapacity d b.l t)
          (debtStep (addressQ j.val) (bagAddressDebt b))
      else (1 - 1 / cap) * (4 * candidateReferenceCapacity d b.l t))| ≤ 69 := by
  let C := candidateReferenceCapacity d b.l t
  let e := bagAddressDebt b
  let ups : Fin 64 → Nat := fun k =>
    (F ((b.child j.val j.isLt (by omega)).child k.val k.isLt (by
      change b.l + 1 < d; omega))).up
  have hTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have hscale := (candidate_active_capacity_ratios hd t (by omega) b hb.1 hTf).1
  have hup : ∀ k : Fin 64, |(ups k : Rat) - frontierInteriorUp (4096 * C)
      (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))| ≤ 1 := by
    intro k
    obtain ⟨hk, hmode⟩ := hchildren k
    have hu := candidate_source_up_error hd ht0 ht P H _ hk
    have hscale' : candidateReferenceCapacity d (b.l + 1 + 1) t = 4096 * C := by
      simpa [C, show b.l + 1 + 1 = b.l + 2 by omega] using hscale
    rcases hmode with hm | hm
    all_goals
      rw [hm, scheduledUpTarget, bagAddressDebt_child, bagAddressDebt_child] at hu
      change |(ups k : Rat) -
        frontierInteriorUp (candidateReferenceCapacity d (b.l + 1 + 1) t)
          (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))| ≤ 1 at hu
      simpa only [hscale'] using hu
  have hactual : (((Pnext).sets (b.child j.val j.isLt (by omega))).card : Rat) =
      ((F b).blocks j : Rat) + ∑ k, (ups k : Rat) := by
    exact_mod_cast candidate_child_routed_count hd ht0 ht P H b j hdepth
  have hdown := candidate_source_block_error hd ht0 ht P H b hb j
  have hcost : evenFlowBlockError + 64 * 1 ≤ (69 : Rat) := by norm_num [evenFlowBlockError]
  rcases hparent with hm | hm | hm
  · rw [if_pos hm]
    have hd' : |((F b).blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        evenFlowBlockError := by simpa only [hm, scheduledDownTarget] using hdown
    exact (receiver_count_discrepancy _ _ ups _ _ _ evenFlowBlockError 1 hd' hup
      (frontier_top_advance_receive C e j).symm hactual).trans hcost
  · rw [if_neg (by simp [hm])]
    have hd' : |((F b).blocks j : Rat) - frontierOrdinaryDown C e j| ≤
        evenFlowBlockError := by simpa only [hm, scheduledDownTarget] using hdown
    exact (receiver_count_discrepancy _ _ ups _ _ _ evenFlowBlockError 1 hd' hup
      (frontier_ordinary_interior_receive C e j).symm hactual).trans hcost
  · rw [if_neg (by simp [hm])]
    have hd' : |((F b).blocks j : Rat) - frontierOrdinaryDown C e j| ≤
        evenFlowBlockError := by simpa only [hm, scheduledDownTarget] using hdown
    exact (receiver_count_discrepancy _ _ ups _ _ _ evenFlowBlockError 1 hd' hup
      (frontier_ordinary_interior_receive C e j).symm hactual).trans hcost

end

end Tapered945
