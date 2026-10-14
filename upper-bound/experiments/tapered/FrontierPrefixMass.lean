import SubtreeMass

namespace Tapered945

def frontierTopAdvanceDownNat (C e : Rat) (j : Nat) : Rat :=
  (1 / 64 + boundaryDebtCoeff * (addressQ j + e / 64)) * C

/-! The signed top mass agrees child-by-child with the native mass left after
all complete descendant subtrees. Therefore it agrees on every whole-child
prefix as well. -/

theorem top_advance_prefix_native_mass (B C e : Rat) (p : Nat) (hp : p ≤ 64) :
    (∑ j ∈ Finset.range p,
      (B / 64 - (∑ k : Fin 64,
        frontierBottomMass (B / 4096) (4096 * C)
          (debtStep (addressQ k.val) (debtStep (addressQ j) e))))) =
      (∑ j ∈ Finset.range p,
        frontierTopAdvanceDownNat C e j) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j < p := Finset.mem_range.mp hj
  simpa [frontierTopAdvanceDownNat, frontierTopAdvanceDown] using
    top_advance_native_child_mass B C e ⟨j, by omega⟩

end Tapered945
