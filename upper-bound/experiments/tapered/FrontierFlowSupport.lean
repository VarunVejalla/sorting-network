import FrontierFlowTable

namespace Tapered945

open Chvatal

section

variable {d t : Nat} (hd : 14 ≤ d) (ht0 : 1 ≤ t)
  (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
  (H : CandidateActualCounts d t P)

local notation "F" => candidateEvenFlowSplits hd t ht0 ht P H

/-- Every nonempty port of the chosen source table lands in the next active
parity band. Exact zero ports at the moving frontiers are used here. -/
theorem candidate_positive_port_destination_active (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (p : Option (Fin 64))
    (hpos : 0 < (raggedWirePort ((F b).wireSplit (P.sets b)) p).card) :
    candidateScheduledActive d (t + 1) (raggedTreeDestination b p) := by
  have htTf : t < candidateTf d := by unfold candidateTerminalCutoff at ht; omega
  have ha := candidate_alpha_frontier_moves_one d hd t htTf
  have ho := candidate_omega_frontier_moves_one t
  have hap := candidate_alpha_parity d t
  have hop := candidate_omega_parity t
  have hlo := hb.1.1
  have hhi := hb.1.2
  have hpar := hb.2
  cases p with
  | none =>
    have hupPos : 0 < (F b).up := by simpa [raggedWirePort_card] using hpos
    have hnotop : ¬ (b.l = candidateAlpha d t ∧
        candidateAlpha d (t + 1) = candidateAlpha d t + 1) := by
      rintro ⟨hl, hm⟩
      have hzero := candidate_source_advance_up hd ht0 ht P H b hb
        (candidate_flow_mode_top_advance d hd t ht0 ht b hl hm)
      omega
    have hbl : 1 ≤ b.l := by omega
    change (candidateAlpha d (t + 1) ≤ b.l - 1 ∧
      b.l - 1 ≤ candidateOmega (t + 1)) ∧ (b.l - 1) % 2 = (t + 1) % 2
    constructor
    · constructor <;> omega
    · omega
  | some j =>
    have hdepth : b.l < d := by
      have how := candidate_omega_le_depth_minus_five d hd t (by omega)
      omega
    have hblockPos : 0 < (F b).blocks j := by
      simpa [raggedWirePort_card] using hpos
    have hnobottom : ¬ (b.l = candidateOmega t ∧
        candidateOmega t = candidateOmega (t + 1) + 1) := by
      rintro ⟨hl, hm⟩
      have hwhole := candidate_source_whole_up hd ht0 ht P H b hb
        (candidate_flow_mode_bottom_contraction d hd t ht0 ht b hl hm)
      have hzero := (F b).block_zero_of_whole hwhole j
      omega
    rw [raggedTreeDestination_down b j hdepth]
    change (candidateAlpha d (t + 1) ≤ b.l + 1 ∧
      b.l + 1 ≤ candidateOmega (t + 1)) ∧ (b.l + 1) % 2 = (t + 1) % 2
    constructor
    · constructor <;> omega
    · omega

/-- The real wire route preserves support on the moving active band. This
uses the physical register partition and the chosen shape-specific table. -/
theorem candidateActualEvenStep_inactive (b : KBag 64 d)
    (hb : ¬ candidateScheduledActive d (t + 1) b) :
    ((candidateActualEvenStep hd t ht0 ht P H).sets b).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  change w ∈ routeRaggedWires P.sets
    (fun q => (F q).wireSplit (P.sets q)) raggedTreeDestination b at hw
  obtain ⟨q, p, hdest, hport⟩ := (mem_routeRaggedWires _ _ _ _ _).mp hw
  have hq : candidateScheduledActive d t q := by
    by_contra hnot
    have hzero := H.inactive q hnot
    have hmem := raggedWirePort_subset ((F q).wireSplit (P.sets q)) p hport
    have hnonzero : 0 < (P.sets q).card := Finset.card_pos.mpr ⟨w, hmem⟩
    omega
  have hpos : 0 < (raggedWirePort ((F q).wireSplit (P.sets q)) p).card :=
    Finset.card_pos.mpr ⟨w, hport⟩
  have hnext := candidate_positive_port_destination_active hd ht0 ht P H q hq p hpos
  rw [hdest] at hnext
  exact hb hnext

end

end Tapered945
