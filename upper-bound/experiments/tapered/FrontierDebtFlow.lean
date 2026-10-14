import AddressDebt
import Mathlib.Tactic

namespace Tapered945

/-! Exact real frontier flow with static address debt. These identities close
local mass conservation; they do not establish rank bounds or an integer
global scheduler. Unlike a time-dependent debt reset, this model uses the
same debt at a given address at every stage. -/

def boundaryDebtCoeff : Rat := 16 / 15
def frontierTopMass (C e : Rat) : Rat := C + boundaryDebtCoeff * e * C
def frontierBottomMass (B C e : Rat) : Rat := B - C / cap - boundaryDebtCoeff * e * C
def frontierInteriorUp (C e : Rat) : Rat := (upFlow - e) * C
def frontierOrdinaryDown (C e : Rat) (j : Fin 64) : Rat :=
  (addressDownCoeff j.val + e / 64) * C
def frontierTopAdvanceDown (C e : Rat) (j : Fin 64) : Rat :=
  (1 / 64 + boundaryDebtCoeff * (addressQ j.val + e / 64)) * C
def frontierTopRetreatUp (C e : Rat) : Rat := (1 / 65536 + e / 15) * C

theorem frontier_child_debt_sum (e : Rat) :
    (∑ j : Fin 64, debtStep (addressQ j.val) e) = e / 64 := by
  simp only [debtStep, Finset.sum_add_distrib, ← Finset.sum_div,
    addressQ_sum_zero, zero_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem frontier_top_advance_split (C e : Rat) :
    (∑ j : Fin 64, frontierTopAdvanceDown C e j) = frontierTopMass C e := by
  simp only [frontierTopAdvanceDown, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, addressQ_sum_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold frontierTopMass boundaryDebtCoeff
  ring

theorem frontier_ordinary_down_sum (C e : Rat) :
    (∑ j : Fin 64, frontierOrdinaryDown C e j) =
      (1 - 256 / cap) * C + e * C := by
  simp only [frontierOrdinaryDown, ← Finset.sum_mul, Finset.sum_add_distrib,
    addressDownCoeff_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold rBar cap
  ring

theorem frontier_top_retreat_split (C e : Rat) :
    frontierTopRetreatUp C e + (∑ j : Fin 64, frontierOrdinaryDown C e j) =
      frontierTopMass C e := by
  rw [frontier_ordinary_down_sum]
  unfold frontierTopRetreatUp frontierTopMass boundaryDebtCoeff cap
  ring

theorem frontier_interior_up_sum (C e : Rat) :
    (∑ j : Fin 64, frontierInteriorUp C (debtStep (addressQ j.val) e)) =
      64 * upFlow * C - (e / 64) * C := by
  simp only [frontierInteriorUp, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, frontier_child_debt_sum]
  ring

theorem frontier_top_advance_receive (C e : Rat) (j : Fin 64) :
    frontierTopAdvanceDown C e j +
      (∑ k : Fin 64, frontierInteriorUp (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierTopMass (4 * C) (debtStep (addressQ j.val) e) := by
  rw [frontier_interior_up_sum]
  unfold frontierTopAdvanceDown frontierTopMass boundaryDebtCoeff debtStep upFlow
  ring

theorem frontier_top_retreat_receive (C e : Rat) :
    (∑ j : Fin 64, frontierTopRetreatUp (1024 * C) (debtStep (addressQ j.val) e)) =
      frontierTopMass C e := by
  simp only [frontierTopRetreatUp, add_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.sum_div, frontier_child_debt_sum]
  unfold frontierTopMass boundaryDebtCoeff
  ring

theorem frontier_bottom_mass_sum (B C e : Rat) :
    (∑ j : Fin 64, frontierBottomMass B C (debtStep (addressQ j.val) e)) =
      64 * B - 64 * C / cap - boundaryDebtCoeff * (e / 64) * C := by
  simp only [frontierBottomMass, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, frontier_child_debt_sum]
  ring

theorem frontier_bottom_expand_split (B C e : Rat) :
    frontierInteriorUp C e +
      (∑ j : Fin 64, frontierBottomMass (B / 64) (4 * C)
        (debtStep (addressQ j.val) e)) = frontierBottomMass B C e := by
  rw [frontier_bottom_mass_sum]
  unfold frontierInteriorUp frontierBottomMass boundaryDebtCoeff upFlow cap
  ring

theorem frontier_bottom_contract_receive (B C e : Rat) (j : Fin 64) :
    frontierOrdinaryDown C e j +
      (∑ k : Fin 64, frontierBottomMass (B / 64) (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierBottomMass B (4 * C) (debtStep (addressQ j.val) e) := by
  rw [frontier_bottom_mass_sum]
  have hr := addressDownCoeff_centered j.val
  unfold frontierOrdinaryDown frontierBottomMass boundaryDebtCoeff debtStep cap rBar at *
  linear_combination C * hr

end Tapered945
