import FrontierPositivity
import IntegerRounding

namespace Tapered945

/-! Integer realization of a top-advance split. Choice across successive
stages and the receiving discrepancy invariant remain separate obligations. -/

theorem top_advance_block_lower (C e : Rat) (j : Fin 64)
    (hC : 0 ≤ C) (he : -eAbs ≤ e) :
    C / 128 ≤ frontierTopAdvanceDown C e j := by
  have hq := (addressQ_bounds j.val).1
  have hc : (1 / 128 : Rat) ≤
      1 / 64 + boundaryDebtCoeff * (addressQ j.val + e / 64) := by
    unfold boundaryDebtCoeff eAbs qEnd at *
    linarith
  have hm := mul_le_mul_of_nonneg_right hc hC
  unfold frontierTopAdvanceDown
  linarith

theorem top_advance_integer_split (C e eta : Rat) (count : Nat)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e) (heta : |eta| ≤ 69)
    (hcount : (count : Rat) = frontierTopMass C e + eta) :
    ∃ blocks : Fin 64 → Nat, (∑ j, blocks j) = count ∧
      ∀ j, |(blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        1 + 69 / 64 := by
  have hsum := frontier_top_advance_split C e
  have hdelta : (count : Rat) - ∑ j, frontierTopAdvanceDown C e j = eta := by
    rw [hsum, hcount]
    ring
  have hshift : ∀ j, 0 ≤ frontierTopAdvanceDown C e j +
      ((count : Rat) - ∑ i, frontierTopAdvanceDown C e i) / 64 := by
    intro j
    rw [hdelta]
    have hl := top_advance_block_lower C e j (by norm_num at hC ⊢; linarith) he
    have helo := (abs_le.mp heta).1
    norm_num at hC
    linarith
  obtain ⟨blocks, htotal, herr⟩ := balanced_rounding_with_total_error
    (frontierTopAdvanceDown C e) count hshift
  refine ⟨blocks, htotal, ?_⟩
  intro j
  have h := herr j
  rw [hdelta] at h
  linarith

end Tapered945
