import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0

namespace Chvatal.D2Slope49Abstract

open scoped BigOperators

abbrev Col := Fin 64
abbrev Height := Fin 65

def predecessor (i : Col) : Col :=
  ⟨(i.val + 63) % 64, Nat.mod_lt _ (by omega)⟩

def predecessorEquiv : Col ≃ Col where
  toFun := predecessor
  invFun i := ⟨(i.val + 1) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv := by
    intro i
    apply Fin.ext
    dsimp [predecessor]
    omega
  right_inv := by
    intro i
    apply Fin.ext
    dsimp [predecessor]
    omega

def unary (delta layer : Col) (height : Height) : Int :=
  (if (17 * ((64 - (35 * layer.val) % 64) % 64)) % 64 < height.val then 1 else 0) +
    (if height.val ≤
      (17 * ((delta.val + 64 - (35 * layer.val) % 64) % 64)) % 64 then 1 else 0)

def output49Height (height : Col → Height) (destination : Col) : Int :=
  ∑ layer : Col,
    if (17 * ((destination.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
      (height layer).val then 1 else 0

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

def rotateProfile (height : Col → Height) (shift : Col) : Col → Height :=
  fun layer => height (shiftLayer shift layer)

def destinationShift (shift : Col) : Col :=
  ⟨(35 * shift.val) % 64, Nat.mod_lt _ (by omega)⟩

def addDestination (left right : Col) : Col :=
  ⟨(left.val + right.val) % 64, Nat.mod_lt _ (by omega)⟩

def shiftForOrigin (origin : Col) : Col :=
  ⟨(11 * origin.val) % 64, Nat.mod_lt _ (by omega)⟩

def relativeDestination (target origin : Col) : Col :=
  ⟨(target.val + 64 - origin.val) % 64, Nat.mod_lt _ (by omega)⟩

lemma shiftForOrigin_correct (origin : Col) :
    destinationShift (shiftForOrigin origin) = origin := by
  apply Fin.ext
  dsimp [destinationShift, shiftForOrigin]
  omega

lemma add_relativeDestination (target origin : Col) :
    addDestination origin (relativeDestination target origin) = target := by
  apply Fin.ext
  dsimp [addDestination, relativeDestination]
  omega

lemma relative_addOrigin (target origin : Col) :
    addDestination (relativeDestination target origin) origin = target := by
  apply Fin.ext
  dsimp [addDestination, relativeDestination]
  omega

lemma addDestination_zero_left (destination : Col) :
    addDestination ⟨0, by omega⟩ destination = destination := by
  apply Fin.ext
  dsimp [addDestination]
  omega

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
      exact Equiv.sum_comp (shiftLayerEquiv shift) f
    _ = _ := by simp [f]

/-- The unary potential objective is exactly 64 plus the directed difference
between the two output-column heights. -/
theorem unary_sum_eq_one_add_output_difference
    (height : Col → Height) (delta : Col) :
    (∑ layer : Col, unary delta layer (height layer)) =
      64 + output49Height height ⟨0, by omega⟩ - output49Height height delta := by
  have hterm (layer : Col) :
      unary delta layer (height layer) =
        (if (17 * ((64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0) +
          (1 - (if (17 * ((delta.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0)) := by
    unfold unary
    by_cases h :
        (17 * ((delta.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
          (height layer).val <;> simp <;> omega
  calc
    _ = ∑ layer : Col,
        ((if (17 * ((64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0) +
          (1 - (if (17 * ((delta.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro layer _
      exact hterm layer
    _ = (∑ layer : Col,
          if (17 * ((64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0) +
        ((∑ layer : Col, (1 : Int)) -
        (∑ layer : Col,
          if (17 * ((delta.val + 64 - (35 * layer.val) % 64) % 64)) % 64 <
            (height layer).val then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 64 + output49Height height ⟨0, by omega⟩ -
        output49Height height delta := by
      simp [output49Height]
      ring

/-- A cyclic family of local max-plus inequalities telescopes: the potential
at each previous height cancels the potential at the next height. -/
theorem cyclic_dual_path_bound
    (delta : Col) (height : Col → Height)
    (potential : Col → Height → Int) (budget : Col → Int)
    (hlocal : ∀ layer,
      unary delta layer (height layer) ≤
        budget layer + potential (predecessor layer) (height (predecessor layer)) -
          potential layer (height layer)) :
    (∑ layer : Col, unary delta layer (height layer)) ≤
      ∑ layer : Col, budget layer := by
  calc
    _ ≤ ∑ layer : Col,
          (budget layer +
            potential (predecessor layer) (height (predecessor layer)) -
              potential layer (height layer)) := by
      apply Finset.sum_le_sum
      intro layer _
      exact hlocal layer
    _ = (∑ layer : Col, budget layer) +
        ((∑ layer : Col,
            potential (predecessor layer) (height (predecessor layer))) -
          (∑ layer : Col, potential layer (height layer))) := by
      calc
        _ = (∑ layer : Col,
              (budget layer +
                potential (predecessor layer) (height (predecessor layer)))) -
              (∑ layer : Col, potential layer (height layer)) := by
          rw [Finset.sum_sub_distrib]
        _ = ((∑ layer : Col, budget layer) +
              (∑ layer : Col,
                potential (predecessor layer) (height (predecessor layer)))) -
              (∑ layer : Col, potential layer (height layer)) := by
          rw [Finset.sum_add_distrib]
        _ = _ := by ring
    _ = ∑ layer : Col, budget layer := by
      have hperm :
          (∑ layer : Col,
            potential (predecessor layer) (height (predecessor layer))) =
          ∑ layer : Col, potential layer (height layer) := by
        exact Equiv.sum_comp predecessorEquiv
          (fun layer => potential layer (height layer))
      rw [hperm]
      ring

/-- A dual path certificate with total budget 77 bounds the directed output
height difference by 13. -/
theorem output_zero_le_output_delta_add_thirteen
    (delta : Col) (height : Col → Height)
    (potential : Col → Height → Int) (budget : Col → Int)
    (hlocal : ∀ layer,
      unary delta layer (height layer) ≤
        budget layer + potential (predecessor layer) (height (predecessor layer)) -
          potential layer (height layer))
    (hbudget : (∑ layer : Col, budget layer) ≤ 77) :
    output49Height height ⟨0, by omega⟩ ≤ output49Height height delta + 13 := by
  have hsum := cyclic_dual_path_bound delta height potential budget hlocal
  rw [unary_sum_eq_one_add_output_difference] at hsum
  omega

/-- Translation of the cyclic profile reduces every ordered output pair to
the certified pair `(0, delta)`. The local dual inequalities are assumed for
each translated profile; this is the reusable wrapper for the table-backed
provider. -/
theorem all_output_pairs_le_thirteen
    (height : Col → Height)
    (potential : Col → Col → Col → Height → Int)
    (budget : Col → Col → Col → Int)
    (hlocal : ∀ origin delta layer,
      unary delta layer
          (rotateProfile height (shiftForOrigin origin) layer) ≤
        budget delta origin layer +
          potential delta origin (predecessor layer)
            (rotateProfile height (shiftForOrigin origin) (predecessor layer)) -
          potential delta origin layer
            (rotateProfile height (shiftForOrigin origin) layer))
    (hbudget : ∀ delta origin,
      (∑ layer : Col, budget delta origin layer) ≤ 77) :
    ∀ origin target,
      output49Height height origin ≤ output49Height height target + 13 := by
  intro origin target
  let shift := shiftForOrigin origin
  let delta := relativeDestination target origin
  have hleft :
      output49Height (rotateProfile height shift) ⟨0, by omega⟩ =
        output49Height height origin := by
    rw [output49Height_rotate]
    rw [addDestination_zero_left, shiftForOrigin_correct]
  have hright :
      output49Height (rotateProfile height shift) delta =
        output49Height height target := by
    rw [output49Height_rotate]
    simp [delta, shift, shiftForOrigin_correct, relative_addOrigin]
  have hbound := output_zero_le_output_delta_add_thirteen
    delta (rotateProfile height shift)
    (fun layer h => potential delta origin layer h) (budget delta origin)
    (by
      intro layer
      simpa [shift, delta] using hlocal origin delta layer)
    (hbudget delta origin)
  calc
    output49Height height origin =
        output49Height (rotateProfile height shift) ⟨0, by omega⟩ := hleft.symm
    _ ≤ output49Height (rotateProfile height shift) delta + 13 := hbound
    _ = output49Height height target + 13 := by rw [hright]

/-- Suffix-minimum certificate entries dominate every admissible predecessor
potential, by one-step induction along the finite height interval. -/
theorem suffix_table_le_potential
    (potential suffix : Nat → Int)
    (hstep : ∀ h, h < 64 → suffix h = min (potential h) (suffix (h + 1)))
    (hend : suffix 64 = potential 64)
    (lower upper : Nat) (hlower : lower ≤ upper) (hupper : upper < 65) :
    suffix lower ≤ potential upper := by
  have hmono : ∀ u, lower ≤ u → u < 65 → suffix lower ≤ suffix u := by
    intro u hlu
    induction u, hlu using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ u hlu ih =>
        intro hu
        have hu64 : u < 64 := by omega
        have hsu : suffix u ≤ suffix (u + 1) := by
          rw [hstep u hu64]
          exact min_le_right _ _
        exact le_trans (ih (by omega)) hsu
  have htop : suffix upper ≤ potential upper := by
    by_cases hu : upper < 64
    · rw [hstep upper hu]
      exact min_le_left _ _
    · have hu' : upper = 64 := by omega
      subst upper
      rw [hend]
  exact le_trans (hmono upper hlower hupper) htop

/-- Turn the compressed suffix-minimum local inequality into the original
edge inequality for every legal adjacent-height transition. -/
theorem dual_edge_of_suffix_certificate
    (unary : Fin 65 → Int) (budget : Int)
    (potentialCurrent potentialPrevious suffixPrevious : Nat → Int)
    (hstep : ∀ h, h < 64 →
      suffixPrevious h = min (potentialPrevious h) (suffixPrevious (h + 1)))
    (hend : suffixPrevious 64 = potentialPrevious 64)
    (hlocal : ∀ t : Fin 65,
      unary t ≤ budget + suffixPrevious (if t.val = 0 then 0 else t.val - 1) -
        potentialCurrent t.val)
    (current previous : Fin 65) (htransition : current.val ≤ previous.val + 1) :
    unary current ≤ budget + potentialPrevious previous.val -
      potentialCurrent current.val := by
  have hthreshold :
      (if current.val = 0 then 0 else current.val - 1) ≤ previous.val := by
    by_cases hc : current.val = 0
    · simp [hc]
    · have hcpos : 0 < current.val := by omega
      simp [hc]
      omega
  have hsuffix := suffix_table_le_potential potentialPrevious suffixPrevious
    hstep hend _ _ hthreshold previous.isLt
  have hl := hlocal current
  omega

end Chvatal.D2Slope49Abstract
