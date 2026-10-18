import FrontierEvenFlow
import RaggedExecution
import FrontierBandGeometry

namespace Tapered945

/-! UB-24 retirement gate. Exact native purity of isolated components forces
exact component cardinalities. Coordinatewise flow rounding alone leaves a
choice of incompatible component sizes, even at a real candidate top scale.
This is an obstruction to a universal contract implication, not a proof that
the particular selected UB-23 trace is unsortable. -/

/-- A complete partition of wires mapped injectively into a complete disjoint
native partition can be pure only at the exact native component sizes. -/
theorem pure_partition_exact_card
    {Wire Key Bag : Type*} [Fintype Wire] [Fintype Key]
    [DecidableEq Wire] [DecidableEq Key] [DecidableEq Bag]
    (owned : Bag → Finset Wire) (native : Bag → Finset Key)
    (keys : Wire → Key) (hinj : Function.Injective keys)
    (hsurj : Function.Surjective keys)
    (hcover : ∀ w, ∃ b, w ∈ owned b)
    (hdisj : ∀ b c, b ≠ c → Disjoint (native b) (native c))
    (hpure : ∀ b, (owned b).image keys ⊆ native b) (b : Bag) :
    (owned b).card = (native b).card := by
  have heq : (owned b).image keys = native b := by
    apply Finset.Subset.antisymm (hpure b)
    intro k hk
    obtain ⟨w, rfl⟩ := hsurj k
    obtain ⟨c, hc⟩ := hcover w
    have hkc := hpure c (Finset.mem_image_of_mem keys hc)
    have hcb : c = b := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj c b hne) hkc hk
    exact Finset.mem_image_of_mem keys (hcb ▸ hc)
  rw [← heq, Finset.card_image_of_injective _ hinj]

private def retirementExampleBlock (shift : Bool) (j : Fin 64) : Nat :=
  if j.val = 0 ∨ j.val = 63 then 2 ^ 34 - 8668228
  else 2 ^ 34 + 279620 +
    if (if shift then 2 ≤ j.val ∧ j.val ≤ 9 else 1 ≤ j.val ∧ j.val ≤ 8) then 2 else 0

private def retirementExampleSplit (shift : Bool) : EvenFlowSplit (2 ^ 40) where
  up := 0
  blocks := retirementExampleBlock shift
  up_even := ⟨0, rfl⟩
  blocks_even := by
    intro j
    unfold retirementExampleBlock
    split_ifs <;> norm_num
  up_le := Nat.zero_le _
  total := by
    cases shift <;>
      norm_num [retirementExampleBlock, Fin.sum_univ_succ]

/-- Two different even, conserved top-advance allocations satisfy every
field of the current local contract, including its rounding bounds. -/
def retirementExampleFlow (shift : Bool) :
    ScheduledEvenFlow .topAdvance 0 (2 ^ 40) 0 (2 ^ 40) where
  split := retirementExampleSplit shift
  up_error := by norm_num [retirementExampleSplit, scheduledUpTarget]
  block_error := by
    intro j
    dsimp [retirementExampleSplit, scheduledDownTarget]
    unfold retirementExampleBlock frontierTopAdvanceDown addressQ
    split_ifs <;> norm_num [qEnd, qMid, boundaryDebtCoeff, evenFlowBlockError]
  advance_up := by intro _; rfl
  whole_up := by simp

theorem retirement_example_distinct :
    (retirementExampleFlow false).split.blocks ⟨1, by omega⟩ =
      (retirementExampleFlow true).split.blocks ⟨1, by omega⟩ + 2 := by
  norm_num [retirementExampleFlow, retirementExampleSplit, retirementExampleBlock]

/-- The example scale is an actual top-advance scale in the candidate, not
an artificial small-capacity instance. This does not identify the selected
trace's actual count or its chosen rounding. -/
theorem retirement_example_candidate_scale :
    candidateFlowMode 16 12 (Chvatal.KBag.root 64 16) = .topAdvance ∧
      candidateReferenceCapacity 16 0 12 = (2 : Rat) ^ 40 := by
  norm_num [candidateFlowMode, candidateAlpha, candidateAlphaBase,
    candidateOmega, candidateOmegaBase, Chvatal.ceilParity, Chvatal.KBag.root,
    candidateReferenceCapacity, candidateCapacityExponent]

/-- For any fixed descendant storage, these two admissible top-advance
choices cannot both fill the same retiring native component exactly. -/
theorem local_rounding_does_not_force_retirement_balance (storage native : Nat) :
    ¬ (storage + (retirementExampleFlow false).split.blocks ⟨1, by omega⟩ = native ∧
      storage + (retirementExampleFlow true).split.blocks ⟨1, by omega⟩ = native) := by
  have h := retirement_example_distinct
  omega

end Tapered945
