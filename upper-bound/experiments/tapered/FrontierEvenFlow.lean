import FrontierFlowFamily

namespace Tapered945

/-- Integer port data whose every routed contribution has even cardinality.
The count is the actual source-register size, rather than a rational target. -/
structure EvenFlowSplit (count : Nat) where
  up : Nat
  blocks : Fin 64 → Nat
  up_even : Even up
  blocks_even : ∀ j, Even (blocks j)
  up_le : up ≤ count
  total : (∑ j, blocks j) = count - up

def evenFlowBlockError : Rat := 2 + 70 / 64

theorem evenFlowBlockError_le : evenFlowBlockError ≤ 69 := by
  norm_num [evenFlowBlockError]

/-- Round an even source count using an even up-port within one wire of its
target and even down blocks. The common count correction is shared equally
by the 64 blocks. This is the integer construction of UB-23; the rational
mass equation is supplied separately for each frontier shape. -/
theorem even_flow_split_exists (count : Nat) (hEven : Even count)
    (upTarget : Rat) (downTarget : Fin 64 → Rat) (eta : Rat)
    (hup : 0 < upTarget) (hroom : ∀ j, 70 / 64 ≤ downTarget j)
    (hcount : (count : Rat) = upTarget + ∑ j, downTarget j + eta)
    (heta : |eta| ≤ 69) :
    ∃ F : EvenFlowSplit count,
      |(F.up : Rat) - upTarget| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - downTarget j| ≤ evenFlowBlockError := by
  have hsum : (70 : Rat) ≤ ∑ j, downTarget j := by
    calc
      (70 : Rat) = ∑ _j : Fin 64, (70 / 64 : Rat) := by norm_num
      _ ≤ ∑ j, downTarget j := Finset.sum_le_sum fun j _ => hroom j
  have hparentRoom : upTarget + 1 ≤ (count : Rat) := by
    have he := (abs_le.mp heta).1
    linarith
  obtain ⟨up, huEven, huLe, huError⟩ :=
    even_up_round_within_parent upTarget count hup hparentRoom
  have hdeltaEq : ((count - up : Nat) : Rat) - ∑ j, downTarget j =
      eta + (upTarget - up) := by
    rw [Nat.cast_sub huLe, hcount]
    ring
  have hdelta : |((count - up : Nat) : Rat) - ∑ j, downTarget j| ≤ 70 := by
    rw [hdeltaEq]
    calc
      |eta + (upTarget - up)| ≤ |eta| + |upTarget - up| := abs_add_le _ _
      _ ≤ 69 + 1 := add_le_add heta (by simpa [abs_sub_comm] using huError)
      _ = 70 := by norm_num
  have hshift : ∀ j, 0 ≤ downTarget j +
      (((count - up : Nat) : Rat) - ∑ k, downTarget k) / 64 := by
    intro j
    have hj := hroom j
    have hd := (abs_le.mp hdelta).1
    linarith
  have hresEven : Even (count - up) := by
    obtain ⟨p, hp⟩ := hEven
    obtain ⟨u, hu⟩ := huEven
    exact ⟨p - u, by omega⟩
  obtain ⟨blocks, htotal, hblocksEven, hblocksError⟩ :=
    balanced_even_rounding_with_total_error downTarget (count - up) hresEven hshift
  refine ⟨⟨up, blocks, huEven, hblocksEven, huLe, htotal⟩, huError, ?_⟩
  intro j
  have hj := hblocksError j
  have hscaled := div_le_div_of_nonneg_right hdelta (by norm_num : (0 : Rat) ≤ 64)
  dsimp [evenFlowBlockError]
  linarith

theorem frontier_ordinary_split (C e : Rat) :
    frontierInteriorUp C e + (∑ j : Fin 64, frontierOrdinaryDown C e j) =
      (1 - 1 / cap) * C := by
  rw [frontier_ordinary_down_sum]
  unfold frontierInteriorUp upFlow cap
  ring

theorem frontier_ordinary_down_rounding_room (C e : Rat)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∀ j : Fin 64, 70 / 64 ≤ frontierOrdinaryDown C e j := by
  have hC0 : 0 ≤ C := by linarith
  have hshift := candidate_child_shift_nonnegative C (e * C) (-70)
    (fun j : Fin 64 => addressDownCoeff j.val) hC
    (mul_le_mul_of_nonneg_right he.1 hC0)
    (mul_le_mul_of_nonneg_right he.2 hC0) (by norm_num)
    (fun j => addressDownCoeff_cases j.val)
  intro j
  have hj := hshift j
  unfold frontierOrdinaryDown
  nlinarith

theorem scheduled_interior_even_split (B C e : Rat)
    (parent : ScheduledFlowCount .interior B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ F : EvenFlowSplit parent.count,
      |(F.up : Rat) - frontierInteriorUp C e| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - frontierOrdinaryDown C e j| ≤ evenFlowBlockError := by
  have hup : 0 < frontierInteriorUp C e := by
    have heHi := he.2
    unfold frontierInteriorUp upFlow ePos at *
    nlinarith
  apply even_flow_split_exists parent.count hEven _ _ parent.error hup
    (frontier_ordinary_down_rounding_room C e hC he) _ parent.error_le
  rw [frontier_ordinary_split]
  simpa [scheduledFlowTarget] using parent.count_eq

theorem scheduled_top_retreat_even_split (B C e : Rat)
    (parent : ScheduledFlowCount .topRetreat B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ F : EvenFlowSplit parent.count,
      |(F.up : Rat) - frontierTopRetreatUp C e| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - frontierOrdinaryDown C e j| ≤ evenFlowBlockError := by
  have hup : 0 < frontierTopRetreatUp C e :=
    mul_pos (frontier_top_retreat_coeff_positive e he.1) (by linarith)
  apply even_flow_split_exists parent.count hEven _ _ parent.error hup
    (frontier_ordinary_down_rounding_room C e hC he) _ parent.error_le
  rw [frontier_top_retreat_split]
  simpa [scheduledFlowTarget] using parent.count_eq

/-- At the singleton first-level bootstrap, a native register is split
directly into static-debt bottom children and a top-retreat up-port. Unlike
the historical reset, this initializes the same debt at every later time. -/
theorem frontier_static_bootstrap_split (B C e : Rat) :
    frontierTopRetreatUp C e +
      (∑ j : Fin 64, frontierBottomMass (B / 64) (4 * C)
        (debtStep (addressQ j.val) e)) = B := by
  rw [frontier_bottom_mass_sum]
  unfold frontierTopRetreatUp boundaryDebtCoeff cap
  norm_num
  ring

theorem static_bootstrap_even_split (count : Nat) (e : Rat)
    (hEven : Even count) (hC : 2 ^ 34 ≤ (count : Rat))
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ F : EvenFlowSplit count,
      |(F.up : Rat) - frontierTopRetreatUp count e| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - frontierBottomMass
        ((count : Rat) / 64) (4 * count)
          (debtStep (addressQ j.val) e)| ≤ evenFlowBlockError := by
  have hup : 0 < frontierTopRetreatUp count e :=
    mul_pos (frontier_top_retreat_coeff_positive e he.1) (by linarith)
  apply even_flow_split_exists count hEven _ _ 0 hup _ _ (by norm_num)
  · intro j
    have hej := debtStep_preserves_bounds (addressQ j.val) e
      (addressQ_bounds j.val).1 (addressQ_bounds j.val).2 he.1 he.2
    apply frontier_bottom_mass_rounding_room _ _ _ (by nlinarith)
      (by nlinarith) hej.2
  · simpa using (frontier_static_bootstrap_split (count : Rat) count e).symm

/-- Bottom contraction's whole register is a valid even up-port. -/
def wholeUpEvenSplit (count : Nat) (he : Even count) : EvenFlowSplit count where
  up := count
  blocks := fun _ => 0
  up_even := he
  blocks_even := fun _ => ⟨0, rfl⟩
  up_le := le_rfl
  total := by simp

theorem scheduled_top_advance_even_flow (B C e : Rat)
    (parent : ScheduledFlowCount .topAdvance B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e) :
    ∃ F : EvenFlowSplit parent.count, F.up = 0 ∧
      ∀ j, |(F.blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        evenFlowBlockError := by
  obtain ⟨blocks, htotal, heven, herr⟩ :=
    scheduled_top_advance_even_integer_split B C e parent hEven hC he
  refine ⟨⟨0, blocks, ⟨0, rfl⟩, heven, Nat.zero_le _, by simpa using htotal⟩,
    rfl, ?_⟩
  intro j
  exact (herr j).trans (by norm_num [evenFlowBlockError])

theorem scheduled_bottom_expansion_even_flow (B C e : Rat)
    (parent : ScheduledFlowCount .bottomExpansion B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C) (hB : C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ F : EvenFlowSplit parent.count,
      |(F.up : Rat) - frontierInteriorUp C e| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - frontierBottomMass (B / 64) (4 * C)
        (debtStep (addressQ j.val) e)| ≤ evenFlowBlockError := by
  obtain ⟨up, hue, hul, huer, blocks, ht, hbe, hber⟩ :=
    bottom_expand_even_integer_split B C e parent hEven hC hB he
  exact ⟨⟨up, blocks, hue, hbe, hul, ht⟩, huer, hber⟩

theorem scheduled_bootstrap_even_flow (B C e : Rat)
    (parent : ScheduledFlowCount .bootstrap B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C) (hB : C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    ∃ F : EvenFlowSplit parent.count,
      |(F.up : Rat) - frontierTopRetreatUp C e| ≤ 1 ∧
      ∀ j, |(F.blocks j : Rat) - frontierBottomMass (B / 64) (4 * C)
        (debtStep (addressQ j.val) e)| ≤ evenFlowBlockError := by
  have hup : 0 < frontierTopRetreatUp C e :=
    mul_pos (frontier_top_retreat_coeff_positive e he.1) (by linarith)
  apply even_flow_split_exists parent.count hEven _ _ parent.error hup _ _
    parent.error_le
  · intro j
    have hej := debtStep_preserves_bounds (addressQ j.val) e
      (addressQ_bounds j.val).1 (addressQ_bounds j.val).2 he.1 he.2
    apply frontier_bottom_mass_rounding_room _ _ _ (by nlinarith)
      (by nlinarith) hej.2
  · rw [frontier_static_bootstrap_split]
    simpa [scheduledFlowTarget] using parent.count_eq

def scheduledUpTarget (shape : ScheduledFlowShape) (C e : Rat) (count : Nat) : Rat :=
  match shape with
  | .bootstrap | .topRetreat => frontierTopRetreatUp C e
  | .interior | .bottomExpansion => frontierInteriorUp C e
  | .topAdvance => 0
  | .bottomContraction | .meeting => count

def scheduledDownTarget (shape : ScheduledFlowShape) (B C e : Rat)
    (j : Fin 64) : Rat :=
  match shape with
  | .bootstrap | .bottomExpansion =>
    frontierBottomMass (B / 64) (4 * C) (debtStep (addressQ j.val) e)
  | .interior | .topRetreat => frontierOrdinaryDown C e j
  | .topAdvance => frontierTopAdvanceDown C e j
  | .bottomContraction | .meeting => 0

/-- One chosen integer split, tagged with its own up and down target formulas.
The top-advance and whole-up cases also carry the exact vanishing ports that
are needed to preserve the moving active band. -/
structure ScheduledEvenFlow (shape : ScheduledFlowShape) (B C e : Rat)
    (count : Nat) where
  split : EvenFlowSplit count
  up_error : |(split.up : Rat) - scheduledUpTarget shape C e count| ≤ 1
  block_error : ∀ j,
    |(split.blocks j : Rat) - scheduledDownTarget shape B C e j| ≤ evenFlowBlockError
  advance_up : shape = .topAdvance → split.up = 0
  whole_up : shape = .bottomContraction ∨ shape = .meeting → split.up = count

theorem scheduled_even_flow_nonempty (shape : ScheduledFlowShape) (B C e : Rat)
    (parent : ScheduledFlowCount shape B C e)
    (hEven : Even parent.count) (hC : 2 ^ 34 ≤ C)
    (hB : shape = .bottomExpansion ∨ shape = .bootstrap → C / 256 ≤ B)
    (he : -eAbs ≤ e ∧ e ≤ ePos) :
    Nonempty (ScheduledEvenFlow shape B C e parent.count) := by
  cases shape with
  | interior =>
    obtain ⟨F, hu, hb⟩ := scheduled_interior_even_split B C e parent hEven hC he
    exact ⟨⟨F, hu, hb, by simp, by simp⟩⟩
  | topRetreat =>
    obtain ⟨F, hu, hb⟩ := scheduled_top_retreat_even_split B C e parent hEven hC he
    exact ⟨⟨F, hu, hb, by simp, by simp⟩⟩
  | topAdvance =>
    obtain ⟨F, hu, hb⟩ := scheduled_top_advance_even_flow B C e parent hEven hC he.1
    exact ⟨⟨F, by simp [scheduledUpTarget, hu], hb, fun _ => hu, by simp⟩⟩
  | bottomExpansion =>
    obtain ⟨F, hu, hb⟩ := scheduled_bottom_expansion_even_flow B C e parent
      hEven hC (hB (by simp)) he
    exact ⟨⟨F, hu, hb, by simp, by simp⟩⟩
  | bootstrap =>
    obtain ⟨F, hu, hb⟩ := scheduled_bootstrap_even_flow B C e parent
      hEven hC (hB (by simp)) he
    exact ⟨⟨F, hu, hb, by simp, by simp⟩⟩
  | bottomContraction =>
    exact ⟨⟨wholeUpEvenSplit parent.count hEven, by simp [scheduledUpTarget,
      wholeUpEvenSplit], by intro j; norm_num [scheduledDownTarget, wholeUpEvenSplit,
      evenFlowBlockError], by simp, fun _ => rfl⟩⟩
  | meeting =>
    exact ⟨⟨wholeUpEvenSplit parent.count hEven, by simp [scheduledUpTarget,
      wholeUpEvenSplit], by intro j; norm_num [scheduledDownTarget, wholeUpEvenSplit,
      evenFlowBlockError], by simp, fun _ => rfl⟩⟩

end Tapered945
