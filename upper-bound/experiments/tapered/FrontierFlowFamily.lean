import FrontierInteger
import FrontierDebtFlow
import FrontierPositivity
import RaggedIntegerSchedule
import Mathlib.Tactic

namespace Tapered945

/-! The flow family keeps exceptional frontier mass formulas separate from
ordinary occupancy. It is a local interface: global routing, address coverage,
and rank-distribution invariants remain separate obligations. -/

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
  | .meeting => (2 - 1 / cap) * C

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
    (hn : (n : Rat) = (2 - 1 / cap) * C + err) (herr : |err| ≤ 69) :
    ScheduledFlowCount .meeting B C e where
  count := n
  error := err
  count_eq := by simpa [scheduledFlowTarget] using hn
  error_le := herr

/-- Meeting the two frontier registers at equal reservoir scale has the
correct nominal combined mass. Independent ±69 input errors only imply ±138,
so this records the meeting budget without treating it as an ordinary
69-error count. -/
theorem frontier_meeting_count_error
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
