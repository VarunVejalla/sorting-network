import FrontierEvenFlow
import RaggedTreeRoute

namespace Tapered945

open Chvatal

/-- Install even port data on the source's actual wire register. -/
def EvenFlowSplit.wireSplit {n : Nat} (s : Finset (Fin n))
    (F : EvenFlowSplit s.card) : RaggedWireSplit s :=
  raggedWireSplitOfInteger s F.up F.blocks F.up_even F.up_le F.total

@[simp] theorem EvenFlowSplit.wireSplit_up {n : Nat} (s : Finset (Fin n))
    (F : EvenFlowSplit s.card) : (F.wireSplit s).up = F.up := rfl

@[simp] theorem EvenFlowSplit.wireSplit_width {n : Nat} (s : Finset (Fin n))
    (F : EvenFlowSplit s.card) (j : Fin 64) :
    (F.wireSplit s).widths j.val = F.blocks j := by
  simp [EvenFlowSplit.wireSplit, raggedWireSplitOfInteger]

/-- A single address-indexed port choice defines a global wire transition.
Coverage and disjointness come from `RaggedWirePartition.route`. -/
noncomputable def routeEvenFlows {d : Nat} (P : RaggedWirePartition d)
    (F : ∀ b, EvenFlowSplit (P.sets b).card) : RaggedWirePartition d :=
  P.route (fun b => (F b).wireSplit (P.sets b)) raggedTreeDestination

theorem routeEvenFlows_card_even {d : Nat} (P : RaggedWirePartition d)
    (F : ∀ b, EvenFlowSplit (P.sets b).card) (b : KBag 64 d) :
    Even ((routeEvenFlows P F).sets b).card := by
  classical
  rw [routeEvenFlows, RaggedWirePartition.route_card_eq_port_sum]
  apply Finset.even_sum
  intro x hx
  rw [raggedWirePort_card]
  cases hp : x.2 with
  | none => exact (F x.1).up_even
  | some j => simpa using (F x.1).blocks_even j

/-- The actual even-port route satisfies the tree recurrence at every
non-root, nonterminal receiver, including both frontiers. -/
theorem routeEvenFlows_card {d : Nat} (P : RaggedWirePartition d)
    (F : ∀ b, EvenFlowSplit (P.sets b).card)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hbd : b.l < d) :
    ((routeEvenFlows P F).sets b).card =
      (F (b.parent (by norm_num))).blocks ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ +
        ∑ j : Fin 64, (F (b.child j.val j.isLt hbd)).up := by
  change (routeRaggedWires _ _ _ b).card = _
  rw [routeRaggedWires_card_eq_tree_recurrence P _ b hb hbd]
  simp only [EvenFlowSplit.wireSplit_up]
  rw [EvenFlowSplit.wireSplit_width _ _ ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩]

theorem frontier_bottom_contract_decompose (B C e : Rat) (j : Fin 64) :
    frontierOrdinaryDown C e j +
      frontierBottomMass B (1024 * C) (debtStep (addressQ j.val) e) -
      frontierInteriorUp (1024 * C) (debtStep (addressQ j.val) e) =
        frontierBottomMass B (4 * C) (debtStep (addressQ j.val) e) := by
  have hr := addressDownCoeff_centered j.val
  unfold frontierOrdinaryDown frontierBottomMass frontierInteriorUp
    boundaryDebtCoeff debtStep upFlow cap rBar at *
  linear_combination C * hr

/-- The history needed by a whole-cohort contraction. Its exact sum records
one previous expansion, not 64 independent error estimates. -/
structure BottomCohortHistory {d : Nat} (P : RaggedWirePartition d)
    (b : KBag 64 d) (hbd : b.l < d) (B sourceCapacity e : Rat) where
  sourceCount : Nat
  sourceUp : Nat
  sourceUp_le : sourceUp ≤ sourceCount
  total : (∑ j : Fin 64, (P.sets (b.child j.val j.isLt hbd)).card) =
    sourceCount - sourceUp
  source_error : |(sourceCount : Rat) - frontierBottomMass B sourceCapacity e| ≤
    evenFlowBlockError
  up_error : |(sourceUp : Rat) - frontierInteriorUp sourceCapacity e| ≤ 1

/-- A preceding expansion creates exactly the history used at contraction,
provided its fresh source and actual child-register equations are supplied. -/
def bottomCohortHistoryOfExpansion {d : Nat}
    (P Pnext : RaggedWirePartition d) (b : KBag 64 d) (hbd : b.l < d)
    (B C e : Rat) (F : EvenFlowSplit (P.sets b).card)
    (hfresh : |((P.sets b).card : Rat) - frontierBottomMass B C e| ≤
      evenFlowBlockError)
    (hup : |(F.up : Rat) - frontierInteriorUp C e| ≤ 1)
    (hchild : ∀ j : Fin 64,
      (Pnext.sets (b.child j.val j.isLt hbd)).card = F.blocks j) :
    BottomCohortHistory Pnext b hbd B C e where
  sourceCount := (P.sets b).card
  sourceUp := F.up
  sourceUp_le := F.up_le
  total := by simp only [hchild]; exact F.total
  source_error := hfresh
  up_error := hup

/-- Cohort cancellation bounds the physical receiver by the preceding
source error plus one up-rounding error plus its incoming down-block error. -/
theorem conserved_cohort_receiver_discrepancy
    (actual down source up : Nat) (children : Fin 64 → Nat)
    (downTarget sourceTarget upTarget target : Rat)
    (hcohort : (∑ j, children j) = source - up) (hupLe : up ≤ source)
    (hactual : actual = down + ∑ j, children j)
    (hmass : downTarget + sourceTarget - upTarget = target)
    (hdown : |(down : Rat) - downTarget| ≤ evenFlowBlockError)
    (hsource : |(source : Rat) - sourceTarget| ≤ evenFlowBlockError)
    (hup : |(up : Rat) - upTarget| ≤ 1) :
    |(actual : Rat) - target| ≤ 115 / 16 := by
  have heq : (actual : Rat) - target =
      ((down : Rat) - downTarget) + ((source : Rat) - sourceTarget) -
        ((up : Rat) - upTarget) := by
    rw [hactual, hcohort, Nat.cast_add, Nat.cast_sub hupLe]
    linarith [hmass]
  rw [heq]
  have hsum := abs_add_le ((down : Rat) - downTarget) ((source : Rat) - sourceTarget)
  have hdiff : |((down : Rat) - downTarget) + ((source : Rat) - sourceTarget) -
      ((up : Rat) - upTarget)| ≤
        |((down : Rat) - downTarget) + ((source : Rat) - sourceTarget)| +
        |(up : Rat) - upTarget| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (((down : Rat) - downTarget) + ((source : Rat) - sourceTarget))
        (-((up : Rat) - upTarget))
  have hbound : evenFlowBlockError + evenFlowBlockError + 1 = (115 / 16 : Rat) := by
    norm_num [evenFlowBlockError]
  linarith only [hsum, hdiff, hdown, hsource, hup, hbound]

/-- Physical lower contraction, using one actual source split table and the
exact cohort history. The next count is measured at its bottom target. -/
theorem routeEvenFlows_bottom_contraction {d : Nat}
    (P : RaggedWirePartition d) (F : ∀ b, EvenFlowSplit (P.sets b).card)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hbd : b.l < d)
    (B C e : Rat)
    (H : BottomCohortHistory P b hbd B (1024 * C)
      (debtStep (addressQ (b.x % 64)) e))
    (hdown : |((F (b.parent (by norm_num))).blocks
      ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ : Rat) -
      frontierOrdinaryDown C e ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩| ≤
        evenFlowBlockError)
    (hwhole : ∀ j : Fin 64,
      (F (b.child j.val j.isLt hbd)).up = (P.sets (b.child j.val j.isLt hbd)).card) :
    |(((routeEvenFlows P F).sets b).card : Rat) -
      frontierBottomMass B (4 * C)
        (debtStep (addressQ (b.x % 64)) e)| ≤ 69 := by
  have hactual := routeEvenFlows_card P F b hb hbd
  simp only [hwhole] at hactual
  have h := conserved_cohort_receiver_discrepancy _ _ _ _ _ _ _ _ _
    H.total H.sourceUp_le hactual
    (frontier_bottom_contract_decompose B C e _) hdown H.source_error H.up_error
  exact h.trans (by norm_num)

/-- Physical terminal meeting uses the same conserved cohort, replacing the
ordinary parent port by its top-advance port. -/
theorem routeEvenFlows_terminal_meeting {d : Nat}
    (P : RaggedWirePartition d) (F : ∀ b, EvenFlowSplit (P.sets b).card)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hbd : b.l < d)
    (B C e : Rat)
    (H : BottomCohortHistory P b hbd B (1024 * C)
      (debtStep (addressQ (b.x % 64)) e))
    (hdown : |((F (b.parent (by norm_num))).blocks
      ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ : Rat) -
      frontierTopAdvanceDown C e ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩| ≤
        evenFlowBlockError)
    (hwhole : ∀ j : Fin 64,
      (F (b.child j.val j.isLt hbd)).up = (P.sets (b.child j.val j.isLt hbd)).card) :
    |(((routeEvenFlows P F).sets b).card : Rat) - B| ≤ 69 := by
  have hactual := routeEvenFlows_card P F b hb hbd
  simp only [hwhole] at hactual
  have h := conserved_cohort_receiver_discrepancy _ _ _ _ _ _ _ _ _
    H.total H.sourceUp_le hactual
    (frontier_terminal_meeting_decompose B C e _) hdown H.source_error H.up_error
  exact h.trans (by norm_num)

end Tapered945
