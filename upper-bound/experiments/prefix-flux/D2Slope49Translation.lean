import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 1000000

namespace Chvatal.D2Slope49Translation

open scoped BigOperators

abbrev Col := Fin 64
abbrev Height := Fin 65

def shiftLayer (shift layer : Col) : Col :=
  ⟨(layer.val + shift.val) % 64, Nat.mod_lt _ (by omega)⟩

def shiftLayerEquiv (shift : Col) : Col ≃ Col where
  toFun := shiftLayer shift
  invFun layer := ⟨(layer.val + 64 - shift.val) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv := by
    intro layer
    apply Fin.ext
    dsimp [shiftLayer]
    omega
  right_inv := by
    intro layer
    apply Fin.ext
    dsimp [shiftLayer]
    omega

theorem shift_sum (shift : Col) (f : Col → Int) :
    (∑ layer : Col, f (shiftLayer shift layer)) = ∑ layer : Col, f layer := by
  exact Equiv.sum_comp (shiftLayerEquiv shift) f

def destinationShift (shift : Col) : Col :=
  ⟨(35 * shift.val) % 64, Nat.mod_lt _ (by omega)⟩

def addDestination (left right : Col) : Col :=
  ⟨(left.val + right.val) % 64, Nat.mod_lt _ (by omega)⟩

def output49Height (height : Col → Height) (destination : Col) : Int :=
  ∑ layer : Col,
    if (17 * ((destination.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
      (height layer).val then 1 else 0

def rotateProfile (height : Col → Height) (shift : Col) : Col → Height :=
  fun layer => height (shiftLayer shift layer)

lemma rotateThreshold (destination shift layer : Col) :
    (17 * ((addDestination destination (destinationShift shift)).val + 64 -
      (35 * (shiftLayer shift layer).val) % 64) % 64) % 64 =
    (17 * ((destination.val + 64 - (35 * layer.val) % 64) % 64) % 64) := by
  dsimp [addDestination, destinationShift, shiftLayer]
  omega

theorem output49Height_rotate (height : Col → Height) (destination shift : Col) :
    output49Height (rotateProfile height shift) destination =
      output49Height height (addDestination destination (destinationShift shift)) := by
  dsimp [output49Height, rotateProfile]
  let f : Col → Int := fun layer =>
    if (17 * ((addDestination destination (destinationShift shift)).val + 64 -
        (35 * layer.val) % 64) % 64) % 64 < (height layer).val then 1 else 0
  calc
    (∑ layer : Col,
        (if (17 * ((destination.val + 64 - (35 * layer.val) % 64) % 64) % 64) <
          (height (shiftLayer shift layer)).val then 1 else 0)) =
      ∑ layer : Col, f (shiftLayer shift layer) := by
      apply Finset.sum_congr rfl
      intro layer _
      change (if (17 * ((destination.val + 64 - (35 * layer.val) % 64) % 64) % 64) <
          (height (shiftLayer shift layer)).val then 1 else 0) = f (shiftLayer shift layer)
      dsimp [f]
      rw [← rotateThreshold]
    _ = ∑ layer : Col, f layer := by
      exact shift_sum shift f
    _ = _ := by
      simp [f]

end Chvatal.D2Slope49Translation
