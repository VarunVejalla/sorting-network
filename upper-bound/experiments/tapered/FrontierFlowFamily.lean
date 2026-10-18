import FrontierInteger
import FrontierDebtFlow
import FrontierPositivity
import RaggedIntegerSchedule
import Mathlib.Tactic

namespace Tapered945

/-! The flow family keeps exceptional frontier mass formulas separate from
ordinary occupancy. `FrontierIntegerSchedule` closes global count routing and
address coverage for this family; rank-distribution invariants remain separate
obligations. -/

inductive ScheduledFlowShape where
  | bootstrap
  | interior
  | topAdvance
  | topRetreat
  | bottomExpansion
  | bottomContraction
  | meeting
  deriving DecidableEq

/-- Expected mass depends on the shape. `B` is the bootstrap or bottom
reservoir parameter; `C` is the local reference capacity. -/
def scheduledFlowTarget (shape : ScheduledFlowShape) (B C e : Rat) : Rat :=
  match shape with
  | .bootstrap => B
  | .interior => (1 - 1 / cap) * C
  | .topAdvance => frontierTopMass C e
  | .topRetreat => frontierTopMass C e
  | .bottomExpansion => frontierBottomMass B C e
  | .bottomContraction => frontierBottomMass B C e
  | .meeting => B

/-- A count tagged by its correct schedule shape. This prevents a frontier
count from being silently treated as ordinary occupancy. -/
structure ScheduledFlowCount (shape : ScheduledFlowShape) (B C e : Rat) where
  count : Nat
  error : Rat
  count_eq : (count : Rat) = scheduledFlowTarget shape B C e + error
  error_le : |error| ≤ 69

def scheduled_bootstrap_count (B : Nat) :
    ScheduledFlowCount .bootstrap (B : Rat) 0 0 where
  count := B
  error := 0
  count_eq := by simp [scheduledFlowTarget]
  error_le := by norm_num

def scheduled_interior_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = (1 - 1 / cap) * C + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .interior B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

def scheduled_top_advance_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = frontierTopMass C e + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .topAdvance B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

def scheduled_top_retreat_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = frontierTopMass C e + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .topRetreat B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

def scheduled_bottom_expansion_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = frontierBottomMass B C e + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .bottomExpansion B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

def scheduled_bottom_contraction_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = frontierBottomMass B C e + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .bottomContraction B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

def scheduled_meeting_count {B C e : Rat} (n : Nat) (err : Rat)
    (hn : (n : Rat) = B + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .meeting B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

/-- Auxiliary identity for adding equal-scale top and bottom frontier
registers. The first physical meeting instead combines one top down port with
a whole bottom cohort, with native target `B`. -/
theorem frontier_equal_scale_auxiliary_mass_error
    (top : ScheduledFlowCount .topRetreat 0 C e)
    (bottom : ScheduledFlowCount .bottomContraction C C e) :
    |((top.count + bottom.count : Nat) : Rat) -
      (2 - 1 / cap) * C| ≤ 138 := by
  have htop : (top.count : Rat) = frontierTopMass C e + top.error := by
    simpa [scheduledFlowTarget] using top.count_eq
  have hbottom : (bottom.count : Rat) = frontierBottomMass C C e + bottom.error := by
    simpa [scheduledFlowTarget] using bottom.count_eq
  have hcombined : ((top.count + bottom.count : Nat) : Rat) -
      (2 - 1 / cap) * C = top.error + bottom.error := by
    push_cast
    rw [htop, hbottom]
    nlinarith [frontier_meeting_mass C e]
  rw [hcombined]
  calc
    |top.error + bottom.error| ≤ |top.error| + |bottom.error| := abs_add_le _ _
    _ ≤ 69 + 69 := add_le_add top.error_le bottom.error_le
    _ = 138 := by norm_num

/-- A bottom register at least as large as its local reference scale remains
positive after the common integer-rounding correction. -/
theorem frontier_bottom_mass_rounding_room (B C e : Rat)
    (hC : 2 ^ 34 ≤ C) (hB : C / 65536 ≤ B) (he : e ≤ ePos) :
    70 / 64 ≤ frontierBottomMass B C e := by
  have hCnonneg : 0 ≤ C := by linarith
  have hcoeff : (1 / 2 ^ 25 : Rat) ≤
      1 / 65536 - 1 / cap - boundaryDebtCoeff * e := by
    have hmul := mul_le_mul_of_nonneg_left he
      (by norm_num [boundaryDebtCoeff] : 0 ≤ boundaryDebtCoeff)
    norm_num [cap, boundaryDebtCoeff, ePos] at hmul ⊢
    linarith
  have hbig : (70 / 64 : Rat) ≤ C / 2 ^ 25 := by
    norm_num
    nlinarith
  unfold frontierBottomMass
  have hrewrite : B - C / cap - boundaryDebtCoeff * e * C =
      (B - C / 65536) + C *
        (1 / 65536 - 1 / cap - boundaryDebtCoeff * e) := by ring
  rw [hrewrite]
  have hfirst : 0 ≤ B - C / 65536 := by linarith
  have hsecond := mul_le_mul_of_nonneg_left hcoeff hCnonneg
  nlinarith

/-- Integerize a bottom-frontier expansion using its own reservoir target:
one even interior up-port and 64 next-bottom registers. This is the missing
integer counterpart of `frontier_bottom_expand_split`. -/
theorem bottom_expand_integer_split
    (B C e : Rat) (parent : ScheduledFlowCount .bottomExpansion B C e)
    (hC : 2 ^ 34 ≤ C) (hB : C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ up : Nat, Even up ∧ up ≤ parent.count ∧
      |(up : Rat) - frontierInteriorUp C e| ≤ 1 ∧
      ∃ blocks : Fin 64 → Nat,
        (∑ j, blocks j) = parent.count - up ∧
        ∀ j, |(blocks j : Rat) -
          frontierBottomMass (B / 64) (4 * C)
            (debtStep (addressQ j.val) e)| ≤ 1 + 70 / 64 := by
  let childDebt : Fin 64 → Rat := fun j => debtStep (addressQ j.val) e
  let childTarget : Fin 64 → Rat := fun j =>
    frontierBottomMass (B / 64) (4 * C) (childDebt j)
  have hCpositive : 0 < C := by linarith
  have hUpCoeff : 0 < upFlow - e := by
    unfold upFlow ePos at *
    norm_num at he ⊢
    linarith
  have hUpPositive : 0 < frontierInteriorUp C e := by
    unfold frontierInteriorUp
    exact mul_pos hUpCoeff hCpositive
  have hchildDebt : ∀ j, childDebt j ≤ ePos := by
    intro j
    have hq := addressQ_bounds j.val
    have hs := debtStep_preserves_bounds (addressQ j.val) e
      hq.1 hq.2 he.1 he.2
    simpa [childDebt] using hs.2
  have hchildLarge : ∀ j, (70 / 64 : Rat) ≤ childTarget j := by
    intro j
    have hCchild : (2 : Rat) ^ 34 ≤ 4 * C := by nlinarith
    have hBchild : (4 * C) / 65536 ≤ B / 64 := by nlinarith [hB]
    exact frontier_bottom_mass_rounding_room (B / 64) (4 * C) (childDebt j)
      hCchild hBchild (hchildDebt j)
  have hsumLarge : (70 : Rat) ≤ ∑ j : Fin 64, childTarget j := by
    calc
      (70 : Rat) = ∑ _j : Fin 64, (70 / 64 : Rat) := by norm_num
      _ ≤ ∑ j : Fin 64, childTarget j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hchildLarge j
  have hparentRoom : frontierInteriorUp C e + 1 ≤ (parent.count : Rat) := by
    have hcount : (parent.count : Rat) = frontierBottomMass B C e + parent.error := by
      simpa [scheduledFlowTarget] using parent.count_eq
    rw [hcount]
    rw [← frontier_bottom_expand_split B C e]
    have herrLo := (abs_le.mp parent.error_le).1
    linarith
  obtain ⟨up, hupEven, hupLe, hupNear⟩ :=
    even_up_round_within_parent (frontierInteriorUp C e) parent.count
      hUpPositive hparentRoom
  let delta : Rat := (parent.count : Rat) - (up : Rat) - ∑ j, childTarget j
  have hdeltaEq : delta = parent.error + (frontierInteriorUp C e - up) := by
    dsimp [delta, childTarget, childDebt]
    have hcount : (parent.count : Rat) = frontierBottomMass B C e + parent.error := by
      simpa [scheduledFlowTarget] using parent.count_eq
    rw [hcount, ← frontier_bottom_expand_split B C e]
    ring
  have hdelta : |delta| ≤ 70 := by
    rw [hdeltaEq]
    calc
      |parent.error + (frontierInteriorUp C e - up)| ≤
          |parent.error| + |frontierInteriorUp C e - up| := abs_add_le _ _
      _ ≤ 69 + 1 := add_le_add parent.error_le (by
        simpa [abs_sub_comm] using hupNear)
      _ = 70 := by norm_num
  have hdeltaLo : -70 ≤ delta := (abs_le.mp hdelta).1
  have hshift : ∀ j, 0 ≤ childTarget j + delta / 64 := by
    intro j
    have hsmall := hchildLarge j
    linarith
  have hdeltaDef : delta = (parent.count - up : Nat) - ∑ j, childTarget j := by
    dsimp [delta]
    rw [Nat.cast_sub hupLe]
  have hshift' : ∀ j, 0 ≤ childTarget j +
      ((parent.count - up : Nat) - ∑ i, childTarget i) / 64 := by
    simpa [hdeltaDef] using hshift
  obtain ⟨blocks, htotal, herr⟩ :=
    balanced_rounding_with_total_error childTarget (parent.count - up) hshift'
  refine ⟨up, hupEven, hupLe, hupNear, blocks, htotal, ?_⟩
  intro j
  have hj := herr j
  rw [← hdeltaDef] at hj
  have hbound : |delta| / 64 ≤ (70 : Rat) / 64 := by
    exact div_le_div_of_nonneg_right hdelta (by norm_num)
  exact hj.trans (by linarith)

/-- Bottom expansion variant for an even parent register. The up-port remains
even and every child register is rounded in two-wire units, so the cohort is
ready for a later whole-register contraction. -/
theorem bottom_expand_even_integer_split
    (B C e : Rat) (parent : ScheduledFlowCount .bottomExpansion B C e)
    (hParentEven : Even parent.count)
    (hC : 2 ^ 34 ≤ C) (hB : C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ up : Nat, Even up ∧ up ≤ parent.count ∧
      |(up : Rat) - frontierInteriorUp C e| ≤ 1 ∧
      ∃ blocks : Fin 64 → Nat,
        (∑ j, blocks j) = parent.count - up ∧
        (∀ j, Even (blocks j)) ∧
        ∀ j, |(blocks j : Rat) -
          frontierBottomMass (B / 64) (4 * C)
            (debtStep (addressQ j.val) e)| ≤ 2 + 70 / 64 := by
  obtain ⟨up, hupEven, hupLe, hupNear, _, _, _⟩ :=
    bottom_expand_integer_split B C e parent hC hB he
  let childDebt : Fin 64 → Rat := fun j => debtStep (addressQ j.val) e
  let childTarget : Fin 64 → Rat := fun j =>
    frontierBottomMass (B / 64) (4 * C) (childDebt j)
  have hdeltaEq :
      ((parent.count - up : Nat) : Rat) - ∑ j, childTarget j =
        parent.error + (frontierInteriorUp C e - up) := by
    have hcast : ((parent.count - up : Nat) : Rat) =
        (parent.count : Rat) - up := by
      exact Nat.cast_sub hupLe
    rw [hcast]
    have hcount : (parent.count : Rat) = frontierBottomMass B C e + parent.error := by
      simpa [scheduledFlowTarget] using parent.count_eq
    rw [hcount]
    have hsplit := frontier_bottom_expand_split B C e
    dsimp [childTarget, childDebt]
    linarith
  have hdelta :
      |((parent.count - up : Nat) : Rat) - ∑ j, childTarget j| ≤ 70 := by
    rw [hdeltaEq]
    calc
      |parent.error + (frontierInteriorUp C e - up)| ≤
          |parent.error| + |frontierInteriorUp C e - up| := abs_add_le _ _
      _ ≤ 69 + 1 := add_le_add parent.error_le (by
        simpa [abs_sub_comm] using hupNear)
      _ = 70 := by norm_num
  have htargetRoom : ∀ j, 70 / 64 ≤ childTarget j := by
    intro j
    have hchildDebt : -eAbs ≤ childDebt j ∧ childDebt j ≤ ePos :=
      debtStep_preserves_bounds (addressQ j.val) e
        (addressQ_bounds j.val).1 (addressQ_bounds j.val).2 he.1 he.2
    have hCchild : (2 : Rat) ^ 34 ≤ 4 * C := by nlinarith
    have hBchild : (4 * C) / 65536 ≤ B / 64 := by nlinarith [hB]
    exact frontier_bottom_mass_rounding_room (B / 64) (4 * C)
      (childDebt j) hCchild hBchild hchildDebt.2
  have hshift : ∀ j, 0 ≤ childTarget j +
      (((parent.count - up : Nat) : Rat) - ∑ i, childTarget i) / 64 := by
    intro j
    have hj := htargetRoom j
    have hd := (abs_le.mp hdelta).1
    linarith
  have htotalEven : Even (parent.count - up) := by
    obtain ⟨p, hp⟩ := hParentEven
    obtain ⟨u, hu⟩ := hupEven
    refine ⟨p - u, ?_⟩
    omega
  obtain ⟨blocks, hsum, heven, herr⟩ :=
    balanced_even_rounding_with_total_error childTarget
      (parent.count - up) htotalEven hshift
  refine ⟨up, hupEven, hupLe, hupNear, blocks, hsum, heven, ?_⟩
  intro j
  have h := herr j
  have hbound :
      |((parent.count - up : Nat) : Rat) - ∑ i, childTarget i| / 64 ≤
        (70 : Rat) / 64 := by
    exact div_le_div_of_nonneg_right hdelta (by norm_num)
  dsimp [childTarget, childDebt] at h ⊢
  linarith

/-- Turn an even bottom-expansion split into typed fresh child registers.
Every child has an even count, a shape-correct bottom-expansion target, and
the local `2 + 70/64` error bound; the family still sums exactly to the
parent's count minus its up-port. -/
theorem scheduled_bottom_expansion_fresh_cohort
    (B C e : Rat) (parent : ScheduledFlowCount .bottomExpansion B C e)
    (hParentEven : Even parent.count)
    (hC : 2 ^ 34 ≤ C) (hB : C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ (up : Nat) (blocks : Fin 64 → Nat)
      (children : ∀ j : Fin 64,
        ScheduledFlowCount .bottomExpansion (B / 64) (4 * C)
          (debtStep (addressQ j.val) e)),
      Even up ∧ up ≤ parent.count ∧
      |(up : Rat) - frontierInteriorUp C e| ≤ 1 ∧
      (∑ j, blocks j) = parent.count - up ∧
      (∀ j, Even (blocks j)) ∧
      (∀ j, (children j).count = blocks j) ∧
      (∀ j, |(children j).error| ≤ 2 + 70 / 64) ∧
      (∀ j, |((children j).count : Rat) -
        frontierBottomMass (B / 64) (4 * C)
          (debtStep (addressQ j.val) e)| ≤ 2 + 70 / 64) := by
  obtain ⟨up, hupEven, hupLe, hupNear, blocks, htotal,
      hblocksEven, hblocksError⟩ :=
    bottom_expand_even_integer_split B C e parent hParentEven hC hB he
  let childDebt : Fin 64 → Rat := fun j => debtStep (addressQ j.val) e
  let childTarget : Fin 64 → Rat := fun j =>
    frontierBottomMass (B / 64) (4 * C) (childDebt j)
  let childError : Fin 64 → Rat := fun j => (blocks j : Rat) - childTarget j
  let children : ∀ j : Fin 64,
      ScheduledFlowCount .bottomExpansion (B / 64) (4 * C) (childDebt j) :=
    fun j =>
      { count := blocks j
        error := childError j
        count_eq := by
          dsimp [childError, childTarget, childDebt, scheduledFlowTarget]
          ring
        error_le := by
          have h := hblocksError j
          exact le_trans h (by norm_num :
            (2 + 70 / 64 : Rat) ≤ 69) }
  refine ⟨up, blocks, children, hupEven, hupLe, hupNear, htotal,
    hblocksEven, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    have h := hblocksError j
    simpa [children, childError, childTarget, childDebt] using h
  · intro j
    simpa [children] using hblocksError j

/-- A bottom cohort emitted by an even expansion supplies the whole-register
part of a later meeting receiver. If the parent is a fresh expansion child,
its discrepancy is the local two-wire rounding error, rather than the generic
69-wire allowance. -/
theorem frontier_terminal_meeting_receiver_discrepancy
    (B C e : Rat) (j : Fin 64)
    (parentCount up topDown : Nat) (children : Fin 64 → Nat)
    (parentError upError topError : Rat)
    (hcohort : (∑ k : Fin 64, children k) = parentCount - up)
    (hUpLe : up ≤ parentCount)
    (hparent : (parentCount : Rat) =
      frontierBottomMass B (1024 * C) (debtStep (addressQ j.val) e) + parentError)
    (hup : (up : Rat) =
      frontierInteriorUp (1024 * C) (debtStep (addressQ j.val) e) + upError)
    (htop : (topDown : Rat) = frontierTopAdvanceDown C e j + topError)
    (hparentError : |parentError| ≤ 2 + 70 / 64)
    (hupError : |upError| ≤ 1)
    (htopError : |topError| ≤ 2 + 69 / 64) :
    |((topDown + ∑ k : Fin 64, children k : Nat) : Rat) - B| ≤ 459 / 64 := by
  have hcohortRat :
      (∑ k : Fin 64, (children k : Rat)) =
        (parentCount : Rat) - up := by
    have hcast : ((∑ k : Fin 64, children k : Nat) : Rat) =
        ((parentCount - up : Nat) : Rat) := by
      exact_mod_cast hcohort
    rw [Nat.cast_sum, Nat.cast_sub hUpLe] at hcast
    exact hcast
  have hroute :
      ((topDown + ∑ k : Fin 64, children k : Nat) : Rat) - B =
        topError + parentError - upError := by
    push_cast
    calc
      ((topDown : Rat) + (∑ k : Fin 64, (children k : Rat))) - B =
          ((topDown : Rat) + ((parentCount : Rat) - up)) - B := by
            rw [hcohortRat]
      _ = topError + parentError - upError := by
            rw [htop, hparent, hup]
            linear_combination frontier_terminal_meeting_decompose B C e j
  rw [hroute]
  have hrearrange : topError + parentError - upError =
      (topError + parentError) + (-upError) := by ring
  rw [hrearrange]
  calc
    |(topError + parentError) + (-upError)|
        ≤ |topError + parentError| + |-upError| := abs_add_le _ _
    _ = |topError + parentError| + |upError| := by rw [abs_neg]
    _ ≤ |topError| + |parentError| + |upError| := by
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (2 + 69 / 64) + (2 + 70 / 64) + 1 := by
      exact add_le_add (add_le_add htopError hparentError) hupError
    _ = 459 / 64 := by norm_num

/-- The terminal meeting error is comfortably inside the common 69-wire
discrepancy window. -/
theorem frontier_terminal_meeting_receiver_within_69
    (B C e : Rat) (j : Fin 64)
    (parentCount up topDown : Nat) (children : Fin 64 → Nat)
    (parentError upError topError : Rat)
    (hcohort : (∑ k : Fin 64, children k) = parentCount - up)
    (hUpLe : up ≤ parentCount)
    (hparent : (parentCount : Rat) =
      frontierBottomMass B (1024 * C) (debtStep (addressQ j.val) e) + parentError)
    (hup : (up : Rat) =
      frontierInteriorUp (1024 * C) (debtStep (addressQ j.val) e) + upError)
    (htop : (topDown : Rat) = frontierTopAdvanceDown C e j + topError)
    (hparentError : |parentError| ≤ 2 + 70 / 64)
    (hupError : |upError| ≤ 1)
    (htopError : |topError| ≤ 2 + 69 / 64) :
    |((topDown + ∑ k : Fin 64, children k : Nat) : Rat) - B| ≤ 69 := by
  have h := frontier_terminal_meeting_receiver_discrepancy B C e j
    parentCount up topDown children parentError upError topError
    hcohort hUpLe hparent hup htop hparentError hupError htopError
  have hbound : (459 / 64 : Rat) ≤ 69 := by norm_num
  exact le_trans h hbound

/-- The advance integerizer consumes only a top-advance count. The ordinary
interior constructor cannot be substituted without an explicit conversion. -/
theorem scheduled_top_advance_integer_split
    (B C e : Rat) (parent : ScheduledFlowCount .topAdvance B C e)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e) :
    ∃ blocks : Fin 64 → Nat, (∑ j, blocks j) = parent.count ∧
      ∀ j, |(blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        1 + 69 / 64 := by
  have hcount : (parent.count : Rat) = frontierTopMass C e + parent.error := by
    simpa [scheduledFlowTarget] using parent.count_eq
  exact top_advance_integer_split C e parent.error parent.count hC he
    parent.error_le hcount

/-- Even-total version of the top advance split. It is suitable for an
even-register schedule and retains a sub-69 per-port rounding bound. -/
theorem scheduled_top_advance_even_integer_split
    (B C e : Rat) (parent : ScheduledFlowCount .topAdvance B C e)
    (hParentEven : Even parent.count)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e) :
    ∃ blocks : Fin 64 → Nat,
      (∑ j, blocks j) = parent.count ∧
      (∀ j, Even (blocks j)) ∧
      ∀ j, |(blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        2 + 69 / 64 := by
  have hcount : (parent.count : Rat) = frontierTopMass C e + parent.error := by
    simpa [scheduledFlowTarget] using parent.count_eq
  have hsum := frontier_top_advance_split C e
  have hdelta : (parent.count : Rat) -
      ∑ j : Fin 64, frontierTopAdvanceDown C e j = parent.error := by
    rw [hsum, hcount]
    ring
  have hshift : ∀ j, 0 ≤ frontierTopAdvanceDown C e j +
      ((parent.count : Rat) - ∑ i, frontierTopAdvanceDown C e i) / 64 := by
    intro j
    rw [hdelta]
    have hl := top_advance_block_lower C e j (by norm_num at hC ⊢; linarith) he
    have helo := (abs_le.mp parent.error_le).1
    norm_num at hC
    linarith
  obtain ⟨blocks, htotal, heven, herr⟩ :=
    balanced_even_rounding_with_total_error
      (frontierTopAdvanceDown C e) parent.count hParentEven hshift
  refine ⟨blocks, htotal, heven, ?_⟩
  intro j
  have hj := herr j
  rw [hdelta] at hj
  calc
    |(blocks j : Rat) - frontierTopAdvanceDown C e j|
        ≤ 2 + |parent.error| / 64 := hj
    _ ≤ 2 + 69 / 64 := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right parent.error_le (by norm_num))

/-- One typed realization of the terminal mixed receiver. The lower parent is
assumed to be a fresh child from the preceding expansion; this supplies its
sharper `2 + 70/64` discrepancy. The emitted child cohort retains its exact
sum, so the meeting count does not accumulate 64 independent errors. -/
theorem scheduled_terminal_meeting_receiver
    (B C e : Rat) (j : Fin 64)
    (top : ScheduledFlowCount .topAdvance 0 C e)
    (bottom : ScheduledFlowCount .bottomExpansion B (1024 * C)
      (debtStep (addressQ j.val) e))
    (hTopEven : Even top.count) (hBottomEven : Even bottom.count)
    (hFresh : |bottom.error| ≤ 2 + 70 / 64)
    (hC : 2 ^ 34 ≤ C) (hB : (1024 * C) / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ (topBlocks : Fin 64 → Nat) (bottomUp : Nat)
      (bottomBlocks : Fin 64 → Nat),
      (∑ k, topBlocks k) = top.count ∧
      (∀ k, Even (topBlocks k)) ∧
      (∀ k, |(topBlocks k : Rat) - frontierTopAdvanceDown C e k| ≤
        2 + 69 / 64) ∧
      Even bottomUp ∧ bottomUp ≤ bottom.count ∧
      |(bottomUp : Rat) - frontierInteriorUp (1024 * C)
        (debtStep (addressQ j.val) e)| ≤ 1 ∧
      (∑ k, bottomBlocks k) = bottom.count - bottomUp ∧
      (∀ k, Even (bottomBlocks k)) ∧
      (∀ k, |(bottomBlocks k : Rat) -
        frontierBottomMass (B / 64) (4096 * C)
          (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))| ≤
          2 + 70 / 64) ∧
      ∃ meeting : ScheduledFlowCount .meeting B (4 * C) e,
        meeting.count = topBlocks j + ∑ k, bottomBlocks k := by
  classical
  obtain ⟨topBlocks, htopSum, htopEven, htopError⟩ :=
    scheduled_top_advance_even_integer_split 0 C e top hTopEven hC he.1
  have hChildDebt : -eAbs ≤ debtStep (addressQ j.val) e ∧
      debtStep (addressQ j.val) e ≤ ePos :=
    debtStep_preserves_bounds (addressQ j.val) e
      (addressQ_bounds j.val).1 (addressQ_bounds j.val).2 he.1 he.2
  have hCbottom : (2 : Rat) ^ 34 ≤ 1024 * C := by nlinarith [hC]
  obtain ⟨bottomUp, hbottomUpEven, hbottomUpLe, hbottomUpError,
      bottomBlocks, hbottomTotal, hbottomBlocksEven, hbottomBlockError⟩ :=
    bottom_expand_even_integer_split B (1024 * C)
      (debtStep (addressQ j.val) e) bottom hBottomEven
      hCbottom hB hChildDebt
  let receiverCount : Nat := topBlocks j + ∑ k : Fin 64, bottomBlocks k
  let topError : Rat := (topBlocks j : Rat) - frontierTopAdvanceDown C e j
  let upError : Rat := (bottomUp : Rat) -
    frontierInteriorUp (1024 * C) (debtStep (addressQ j.val) e)
  have htop : (topBlocks j : Rat) = frontierTopAdvanceDown C e j + topError := by
    dsimp [topError]
    ring
  have hup : (bottomUp : Rat) =
      frontierInteriorUp (1024 * C) (debtStep (addressQ j.val) e) + upError := by
    dsimp [upError]
    ring
  have hbottom : (bottom.count : Rat) =
      frontierBottomMass B (1024 * C) (debtStep (addressQ j.val) e) + bottom.error := by
    simpa [scheduledFlowTarget] using bottom.count_eq
  have htopErrorJ : |topError| ≤ 2 + 69 / 64 := by
    dsimp [topError]
    exact htopError j
  have hreceiverError := frontier_terminal_meeting_receiver_within_69
    B C e j bottom.count bottomUp (topBlocks j) bottomBlocks bottom.error
    upError topError hbottomTotal hbottomUpLe hbottom hup htop hFresh
    hbottomUpError htopErrorJ
  have hbottomBlockError' : ∀ k, |(bottomBlocks k : Rat) -
      frontierBottomMass (B / 64) (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))| ≤
        2 + 70 / 64 := by
    intro k
    simpa [show 4 * (1024 * C) = 4096 * C by ring] using
      hbottomBlockError k
  let meetingError : Rat := (receiverCount : Rat) - B
  have hmeeting : (receiverCount : Rat) = B + meetingError := by
    dsimp [meetingError]
    ring
  refine ⟨topBlocks, bottomUp, bottomBlocks, htopSum, htopEven, htopError,
    hbottomUpEven, hbottomUpLe, hbottomUpError, hbottomTotal,
    hbottomBlocksEven, hbottomBlockError', ?_⟩
  exact ⟨scheduled_meeting_count receiverCount meetingError hmeeting hreceiverError,
    rfl⟩

/-- Candidate-specific two-expansion cohort into the terminal meeting. The
first split creates fresh bottom parents at reservoir size `64^7`; splitting
those parents once more and combining their whole registers with a top-advance
port gives every terminal receiver its correctly typed `B=64^7` count. The
top parent flow remains an explicit premise to be supplied by the upper
frontier recurrence. -/
theorem scheduled_candidate_terminal_meeting_family
    (d : Nat) (hd : 14 ≤ d) (e : Rat)
    (rootBottom : ScheduledFlowCount .bottomExpansion (64 ^ 8 : Rat)
      (64 ^ 8 : Rat) e)
    (top : ScheduledFlowCount .topAdvance 0 (2 ^ 40 : Rat) e)
    (hRootEven : Even rootBottom.count) (hTopEven : Even top.count)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∀ j : Fin 64,
      ∃ meeting : ScheduledFlowCount .meeting (64 ^ 7 : Rat)
        (4 * (2 ^ 40 : Rat)) e,
        |meeting.error| ≤ 69 ∧
        ∃ topBlocks : Fin 64 → Nat, ∃ bottomBlocks : Fin 64 → Nat,
          meeting.count = topBlocks j + ∑ k : Fin 64, bottomBlocks k := by
  have hscale := candidate_terminal_cohort_scales d hd
  have hrootC : candidateReferenceCapacity d (d - 8)
      (candidateTerminalCutoff d - 3) = (64 ^ 8 : Rat) := hscale.1
  have hchildC : candidateReferenceCapacity d (d - 7)
      (candidateTerminalCutoff d - 2) = (4 * 64 ^ 8 : Rat) := hscale.2.1
  have htopC : candidateReferenceCapacity d (d - 8)
      (candidateTerminalCutoff d - 1) = (2 ^ 40 : Rat) := hscale.2.2.1
  have hmeetingB : candidateReferenceCapacity d (d - 7)
      (candidateTerminalCutoff d) = (64 ^ 7 : Rat) :=
    (candidate_terminal_cutoff_scale d hd).2.2
  have hrootCapacity : (2 : Rat) ^ 34 ≤ (64 ^ 8 : Rat) := by norm_num
  have hrootReservoir : (64 ^ 8 : Rat) / 256 ≤ (64 ^ 8 : Rat) := by norm_num
  obtain ⟨rootUp, rootBlocks, rootChildren, hrootUpEven, hrootUpLe,
      hrootUpError, hrootTotal, hrootBlocksEven, hrootChildCount,
      hrootChildError, hrootChildMassError⟩ :=
    scheduled_bottom_expansion_fresh_cohort (64 ^ 8 : Rat) (64 ^ 8 : Rat) e
      rootBottom hRootEven hrootCapacity hrootReservoir he
  intro j
  have hreservoir : (1024 * (2 ^ 40 : Rat)) / 256 ≤ (64 ^ 7 : Rat) := by
    norm_num
  have htopCapacity : (2 : Rat) ^ 34 ≤ (2 ^ 40 : Rat) := by norm_num
  have hchildB : ((64 ^ 8 : Rat) / 64) = (64 ^ 7 : Rat) := by norm_num
  have hchildCap : (4 * (64 ^ 8 : Rat)) = 1024 * (2 ^ 40 : Rat) := by
    norm_num
  let bottom : ScheduledFlowCount .bottomExpansion (64 ^ 7 : Rat)
      (1024 * (2 ^ 40 : Rat)) (debtStep (addressQ j.val) e) :=
    { count := (rootChildren j).count
      error := (rootChildren j).error
      count_eq := by
        simpa [scheduledFlowTarget, hchildB, hchildCap] using
          (rootChildren j).count_eq
      error_le := (rootChildren j).error_le }
  have hbottomFresh : |bottom.error| ≤ 2 + 70 / 64 := by
    simpa [bottom] using hrootChildError j
  have hbottomEven : Even bottom.count := by
    simpa [bottom, hrootChildCount j] using hrootBlocksEven j
  obtain ⟨topBlocks, bottomUp, bottomBlocks, htopSum, htopBlocksEven,
      htopBlockError, hbottomUpEven, hbottomUpLe, hbottomUpError,
      hbottomTotal, hbottomBlocksEven, hbottomBlockError, meeting, hmeeting⟩ :=
    scheduled_terminal_meeting_receiver (64 ^ 7 : Rat) (2 ^ 40 : Rat) e j
      top bottom hTopEven hbottomEven hbottomFresh htopCapacity
      hreservoir he
  exact ⟨meeting, meeting.error_le, ⟨topBlocks, bottomBlocks, hmeeting⟩⟩

/-- The retreat integerizer consumes a distinct top-retreat count because it
allocates an up-port as well as ordinary down-ports. -/
theorem scheduled_top_retreat_integer_split
    (B C e : Rat) (parent : ScheduledFlowCount .topRetreat B C e)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ up : Nat, Even up ∧ up ≤ parent.count ∧
      |(up : Rat) - frontierTopRetreatUp C e| ≤ 1 ∧
      ∃ blocks : Fin 64 → Nat,
        (∑ j, blocks j) = parent.count - up ∧
        ∀ j, |(blocks j : Rat) - frontierOrdinaryDown C e j| ≤
          1 + 70 / 64 := by
  have hcount : (parent.count : Rat) = frontierTopMass C e + parent.error := by
    simpa [scheduledFlowTarget] using parent.count_eq
  exact top_retreat_integer_split C e parent.error parent.count hC he
    parent.error_le hcount

/-- Ordinary addresses retain the existing address-dependent integerizer.
The debt equality is explicit, so the shape index cannot be paired with a
different bag's port profile. -/
theorem scheduled_interior_integer_flow {d : Nat}
    (b : Chvatal.KBag 64 d) (B C e : Rat)
    (parent : ScheduledFlowCount .interior B C e)
    (hC : 2 ^ 34 ≤ C) :
    Nonempty (LocalIntegerFlow b C parent.error parent.count) := by
  apply local_integer_flow_nonempty b C parent.error parent.count hC
    parent.error_le
  have hcount : (parent.count : Rat) =
      (1 - 1 / cap) * C + parent.error := by
    simpa [scheduledFlowTarget] using parent.count_eq
  exact hcount

/-- The ordinary shape's port targets agree exactly with the static-debt
formulas once its address debt is identified. -/
theorem scheduled_interior_ports_match {d : Nat}
    (b : Chvatal.KBag 64 d) (C e : Rat) (hdebt : bagAddressDebt b = e) :
    addressUpAt b C = frontierInteriorUp C e ∧
      (∀ j, addressDownAt b C j = frontierOrdinaryDown C e j) := by
  constructor
  · rw [addressUpAt, hdebt]
    unfold frontierInteriorUp
    ring
  · intro j
    rw [addressDownAt, hdebt]
    unfold frontierOrdinaryDown
    ring

/-- An ordinary child receives its one parent down-port and the up-ports of
its 64 grandchildren at exactly the ordinary reference mass. This is the
interior analogue of `frontier_top_advance_receive`. -/
theorem frontier_ordinary_interior_receive (C e : Rat) (j : Fin 64) :
    frontierOrdinaryDown C e j +
      (∑ k : Fin 64, frontierInteriorUp (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      (1 - 1 / cap) * (4 * C) := by
  rw [frontier_interior_up_sum]
  have hr := addressDownCoeff_centered j.val
  unfold frontierOrdinaryDown debtStep upFlow cap rBar at *
  linear_combination C * hr

/-- Receiver discrepancies compose by adding the error on its parent block
to the errors of its 64 incoming up-ports. The exact conservation identity
must be supplied by the relevant shape-specific formula. -/
theorem receiver_count_discrepancy
    (actual : Nat) (downActual : Nat) (upActual : Fin 64 → Nat)
    (downTarget : Rat) (upTarget : Fin 64 → Rat) (target : Rat)
    (downErr upErr : Rat)
    (hdown : |(downActual : Rat) - downTarget| ≤ downErr)
    (hup : ∀ j, |(upActual j : Rat) - upTarget j| ≤ upErr)
    (hreal : target = downTarget + ∑ j, upTarget j)
    (hactual : (actual : Rat) = downActual + ∑ j, (upActual j : Rat)) :
    |(actual : Rat) - target| ≤ downErr + 64 * upErr := by
  have heq : (actual : Rat) - target =
      ((downActual : Rat) - downTarget) +
        ∑ j, ((upActual j : Rat) - upTarget j) := by
    rw [hactual, hreal, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    |((downActual : Rat) - downTarget) +
        ∑ j, ((upActual j : Rat) - upTarget j)|
        ≤ |(downActual : Rat) - downTarget| +
          |∑ j, ((upActual j : Rat) - upTarget j)| := abs_add_le _ _
    _ ≤ downErr + ∑ j, |(upActual j : Rat) - upTarget j| :=
      add_le_add hdown (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ downErr + ∑ _j : Fin 64, upErr := by
      gcongr with j
      exact hup j
    _ = downErr + 64 * upErr := by norm_num

/-- At an upper advance, a correctly routed parent down-block and the 64
child up-ports retain the top target with an error below the ordinary 69-wire
budget, provided each child up-rounds within one wire. -/
theorem top_advance_receiver_discrepancy
    (actual downActual : Nat) (upActual : Fin 64 → Nat)
    (C e : Rat) (j : Fin 64)
    (hdown : |(downActual : Rat) - frontierTopAdvanceDown C e j| ≤
      1 + 69 / 64)
    (hup : ∀ k, |(upActual k : Rat) -
      frontierInteriorUp (4096 * C)
        (debtStep (addressQ k.val)
          (debtStep (addressQ j.val) e))| ≤ 1)
    (hactual : (actual : Rat) = downActual + ∑ k, (upActual k : Rat)) :
    |(actual : Rat) - frontierTopMass (4 * C)
      (debtStep (addressQ j.val) e)| ≤ 1 + 69 / 64 + 64 := by
  have hbound := receiver_count_discrepancy actual downActual upActual
    (frontierTopAdvanceDown C e j)
    (fun k => frontierInteriorUp (4096 * C)
      (debtStep (addressQ k.val) (debtStep (addressQ j.val) e)))
    (frontierTopMass (4 * C) (debtStep (addressQ j.val) e))
    (1 + 69 / 64) 1 hdown hup
    (frontier_top_advance_receive C e j).symm hactual
  nlinarith [hbound]

/-- Ordinary interior receivers satisfy the sharper ordinary target; their
single down-block and 64 unit-rounded up-ports fit below 69 wires too. -/
theorem ordinary_interior_receiver_discrepancy
    (actual downActual : Nat) (upActual : Fin 64 → Nat)
    (C e : Rat) (j : Fin 64)
    (hdown : |(downActual : Rat) - frontierOrdinaryDown C e j| ≤
      1 + 70 / 64)
    (hup : ∀ k, |(upActual k : Rat) -
      frontierInteriorUp (4096 * C)
        (debtStep (addressQ k.val)
          (debtStep (addressQ j.val) e))| ≤ 1)
    (hactual : (actual : Rat) = downActual + ∑ k, (upActual k : Rat)) :
    |(actual : Rat) - (1 - 1 / cap) * (4 * C)| ≤
      1 + 70 / 64 + 64 := by
  have hbound := receiver_count_discrepancy actual downActual upActual
    (frontierOrdinaryDown C e j)
    (fun k => frontierInteriorUp (4096 * C)
      (debtStep (addressQ k.val) (debtStep (addressQ j.val) e)))
    ((1 - 1 / cap) * (4 * C)) (1 + 70 / 64) 1 hdown hup
    (frontier_ordinary_interior_receive C e j).symm hactual
  nlinarith [hbound]

/-- The retreat receiver sums the 64 top-up ports. Its total discrepancy is
at most 64 wires under unit rounding on each port. -/
theorem top_retreat_receiver_discrepancy
    (actual : Nat) (upActual : Fin 64 → Nat) (C e : Rat)
    (hup : ∀ j, |(upActual j : Rat) -
      frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e)| ≤ 1)
    (hactual : (actual : Rat) = ∑ j, (upActual j : Rat)) :
    |(actual : Rat) - frontierTopMass C e| ≤ 64 := by
  have hdebtSum : (∑ j : Fin 64,
      frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e)) =
      frontierTopMass C e := frontier_top_retreat_receive C e
  have herror : |(actual : Rat) -
      ∑ j : Fin 64, frontierTopRetreatUp (1024 * C)
        (debtStep (addressQ j.val) e)| ≤ 64 := by
    rw [hactual]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin 64, ((upActual j : Rat) -
          frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e))|
          ≤ ∑ j : Fin 64, |(upActual j : Rat) -
            frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e)| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 64, (1 : Rat) := by
        gcongr with j
        exact hup j
      _ = 64 := by norm_num
  rwa [hdebtSum] at herror

/-! Exact rational conservation identities for the typed transition modes.
These are the receiver-count formulas used to assemble a schedule; proving
that a routed execution realizes their hypotheses is a later global step. -/

theorem scheduled_frontier_mass_transitions (B C e : Rat) (j : Fin 64) :
    (∑ k : Fin 64, frontierTopAdvanceDown C e k) = frontierTopMass C e ∧
    frontierTopAdvanceDown C e j +
      (∑ k : Fin 64, frontierInteriorUp (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierTopMass (4 * C) (debtStep (addressQ j.val) e) ∧
    frontierTopRetreatUp C e +
      (∑ k : Fin 64, frontierOrdinaryDown C e k) = frontierTopMass C e ∧
    frontierInteriorUp C e +
      (∑ k : Fin 64, frontierBottomMass (B / 64) (4 * C)
        (debtStep (addressQ k.val) e)) = frontierBottomMass B C e ∧
    frontierOrdinaryDown C e j +
      (∑ k : Fin 64, frontierBottomMass (B / 64) (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierBottomMass B (4 * C) (debtStep (addressQ j.val) e) ∧
    (∑ k : Fin 64, frontierTopRetreatUp (1024 * C)
        (debtStep (addressQ k.val) e)) = frontierTopMass C e ∧
    frontierTopMass C e + frontierBottomMass C C e = (2 - 1 / cap) * C := by
  exact ⟨frontier_top_advance_split C e,
    frontier_top_advance_receive C e j,
    frontier_top_retreat_split C e,
    frontier_bottom_expand_split B C e,
    frontier_bottom_contract_receive B C e j,
    frontier_top_retreat_receive C e,
    frontier_meeting_mass C e⟩

end Tapered945
