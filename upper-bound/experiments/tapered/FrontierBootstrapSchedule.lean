import FrontierFlowSupport
import FrontierRootRoute

namespace Tapered945

open Chvatal

theorem even_64_power (k : Nat) (hk : 1 ≤ k) : Even (64 ^ k) := by
  refine ⟨32 * 64 ^ (k - 1), ?_⟩
  calc
    64 ^ k = 64 ^ (k - 1) * 64 := by rw [← pow_succ, Nat.sub_add_cancel hk]
    _ = 32 * 64 ^ (k - 1) + 32 * 64 ^ (k - 1) := by ring

/-- The initial root sends exactly one native interval to each child. All
other source registers are empty. -/
noncomputable def candidateInitialFlows (d : Nat) (hd : 14 ≤ d) (b : KBag 64 d) :
    EvenFlowSplit ((RaggedWirePartition.initial d).sets b).card where
  up := 0
  blocks := fun _ => if b = KBag.root 64 d then 64 ^ (d - 1) else 0
  up_even := ⟨0, rfl⟩
  blocks_even := by
    intro j
    split_ifs
    · exact even_64_power _ (by omega)
    · exact ⟨0, rfl⟩
  up_le := Nat.zero_le _
  total := by
    classical
    by_cases hb : b = KBag.root 64 d
    · have hs : 64 * 64 ^ (d - 1) = 64 ^ d := by
        rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
      simpa [RaggedWirePartition.initial, hb, mul_comm] using hs
    · simp [RaggedWirePartition.initial, hb]

noncomputable def candidateFirstPartition (d : Nat) (hd : 14 ≤ d) :
    RaggedWirePartition d := routeEvenFlows (RaggedWirePartition.initial d)
      (candidateInitialFlows d hd)

theorem candidateFirstPartition_support (d : Nat) (hd : 14 ≤ d) (b : KBag 64 d)
    (hn : 0 < ((candidateFirstPartition d hd).sets b).card) : b.l = 1 := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hn
  change w ∈ routeRaggedWires (RaggedWirePartition.initial d).sets
    (fun q => (candidateInitialFlows d hd q).wireSplit _) raggedTreeDestination b at hw
  obtain ⟨q, p, hdest, hp⟩ := (mem_routeRaggedWires _ _ _ _ _).mp hw
  have hq : q = KBag.root 64 d := by
    by_contra hnot
    have hm := raggedWirePort_subset
      ((candidateInitialFlows d hd q).wireSplit _) p hp
    simpa [RaggedWirePartition.initial, hnot] using hm
  subst q
  cases p with
  | none =>
    have hc : 0 < (raggedWirePort
        ((candidateInitialFlows d hd (KBag.root 64 d)).wireSplit _) none).card :=
      Finset.card_pos.mpr ⟨w, hp⟩
    simpa [raggedWirePort_card, candidateInitialFlows] using hc
  | some j =>
    rw [raggedTreeDestination_down _ j (by change 0 < d; omega)] at hdest
    have hl := congrArg KBag.l hdest
    simpa [KBag.child, KBag.root] using hl.symm

theorem candidateFirstPartition_level_one_card (d : Nat) (hd : 14 ≤ d)
    (b : KBag 64 d) (hb : b.l = 1) :
    ((candidateFirstPartition d hd).sets b).card = 64 ^ (d - 1) := by
  have hparent : b.parent (by norm_num) = KBag.root 64 d := by
    have hx : b.x < 64 := by simpa [hb] using b.hx
    apply KBag.ext <;> simp [KBag.parent, KBag.root, hb, Nat.div_eq_of_lt hx]
  rw [candidateFirstPartition, routeEvenFlows_card _ _ b (by omega) (by omega)]
  simp [candidateInitialFlows, hparent]

/-- Kernel-checked initialization of the actual register-count invariant.
The following singleton bootstrap uses the static-debt split, so this
initialization carries no later debt reset. -/
theorem candidate_first_partition_counts (d : Nat) (hd : 14 ≤ d) :
    CandidateActualCounts d 1 (candidateFirstPartition d hd) := by
  have hfront := candidate_frontiers_stage_one d hd
  refine ⟨routeEvenFlows_card_even _ _ , ?_, ?_⟩
  · intro b hb
    by_contra hn
    have hl := candidateFirstPartition_support d hd b (Nat.pos_of_ne_zero hn)
    apply hb
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro b hb
    have hl : b.l = 1 := by
      have hlo := hb.1.1
      have hhi := hb.1.2
      omega
    rw [candidateFirstPartition_level_one_card d hd b hl]
    simp [candidateFlowTarget, candidateFlowMode, scheduledFlowTarget,
      candidateNativeCapacity, hl]

end Tapered945
