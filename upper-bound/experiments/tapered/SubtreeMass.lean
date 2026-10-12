import FrontierDebtFlow

namespace Tapered945

/-! Complete-subtree mass telescoping for static address debt. No key/rank
claim follows without an outsider invariant connecting these masses to keys. -/

theorem frontier_grandchild_bottom_sum (B C e : Rat) :
    (∑ j : Fin 64, ∑ k : Fin 64,
      frontierBottomMass (B / 4096) (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      B - C - boundaryDebtCoeff * e * C := by
  simp_rw [frontier_bottom_mass_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_div, frontier_child_debt_sum]
  unfold cap
  ring

theorem frontier_subtree_mass_fixed_point (B C e : Rat) :
    (1 - 1 / cap) * C +
      (∑ j : Fin 64, ∑ k : Fin 64,
        frontierBottomMass (B / 4096) (4096 * C)
          (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierBottomMass B C e := by
  rw [frontier_grandchild_bottom_sum]
  unfold frontierBottomMass
  ring

def completeSubtreeMass : Nat → Rat → Rat → Rat → Rat
  | 0, B, C, e => frontierBottomMass B C e
  | h + 1, B, C, e => (1 - 1 / cap) * C +
      ∑ j : Fin 64, ∑ k : Fin 64,
        completeSubtreeMass h (B / 4096) (4096 * C)
          (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))

theorem complete_subtree_mass_eq (h : Nat) (B C e : Rat) :
    completeSubtreeMass h B C e = frontierBottomMass B C e := by
  induction h generalizing B C e with
  | zero => rfl
  | succ h ih =>
    simp only [completeSubtreeMass, ih]
    exact frontier_subtree_mass_fixed_point B C e

theorem top_advance_native_child_mass (B C e : Rat) (j : Fin 64) :
    B / 64 - (∑ k : Fin 64,
      frontierBottomMass (B / 4096) (4096 * C)
        (debtStep (addressQ k.val) (debtStep (addressQ j.val) e))) =
      frontierTopAdvanceDown C e j := by
  rw [frontier_bottom_mass_sum]
  unfold frontierTopAdvanceDown debtStep boundaryDebtCoeff cap
  ring

end Tapered945
