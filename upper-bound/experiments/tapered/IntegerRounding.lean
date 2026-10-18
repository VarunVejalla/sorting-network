import Mathlib.Tactic
import SignedReserve

namespace Tapered945

/-- A finite family of nonnegative rational targets whose sum is an integer can
be rounded to natural numbers with the same total and less than one unit of
coordinatewise error. The construction floors every target, then increments a
subset of the nonintegral coordinates to absorb the residual. -/
theorem balanced_integer_rounding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → Rat) (B : Nat)
    (hy : ∀ i, 0 ≤ y i)
    (hsum : ∑ i, y i = (B : Rat)) :
    ∃ x : ι → Nat, (∑ i, x i) = B ∧ ∀ i, |(x i : Rat) - y i| ≤ 1 := by
  classical
  let f : ι → Nat := fun i => Nat.floor (y i)
  let frac : ι → Rat := fun i => y i - (f i : Rat)
  let S : Finset ι := Finset.univ.filter fun i => frac i ≠ 0
  let b : Nat := ∑ i, f i
  have hfloor_le : ∀ i, (f i : Rat) ≤ y i := by
    intro i
    exact Nat.floor_le (hy i)
  have hfrac_nonneg : ∀ i, 0 ≤ frac i := by
    intro i
    dsimp [frac]
    linarith [hfloor_le i]
  have hfrac_lt_one : ∀ i, frac i < 1 := by
    intro i
    dsimp [frac, f]
    have h := Nat.lt_floor_add_one (y i)
    linarith

  have hbase_le_rat : (b : Rat) ≤ B := by
    dsimp [b]
    rw [Nat.cast_sum]
    calc
      (∑ i, (f i : Rat)) ≤ ∑ i, y i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hfloor_le i
      _ = (B : Rat) := hsum
  have hbase_le : b ≤ B := by exact_mod_cast hbase_le_rat
  let R : Nat := B - b
  have hfrac_sum : (∑ i, frac i) = (R : Rat) := by
    dsimp [frac, R, b]
    rw [Finset.sum_sub_distrib, hsum, ← Nat.cast_sum, Nat.cast_sub hbase_le]
  have hfrac_sum_le : (∑ i, frac i) ≤ (S.card : Rat) := by
    calc
      (∑ i, frac i) = ∑ i, if i ∈ S then frac i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hs : i ∈ S
        · simp [hs]
        · have hz : frac i = 0 := by simpa [S] using hs
          simp [hs, hz]
      _ ≤ ∑ i, if i ∈ S then (1 : Rat) else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hs : i ∈ S
        · simp only [hs, if_true]
          exact (hfrac_lt_one i).le
        · simp [hs]
      _ = (S.card : Rat) := by
        simp
  have hRle : R ≤ S.card := by
    have h : (R : Rat) ≤ (S.card : Rat) := by
      rw [← hfrac_sum]
      exact hfrac_sum_le
    exact_mod_cast h
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hRle
  let x : ι → Nat := fun i => f i + if i ∈ T then 1 else 0
  have hInd : (∑ i, if i ∈ T then 1 else 0) = T.card := by
    simp
  have hsumX : (∑ i, x i) = B := by
    calc
      (∑ i, x i) = (∑ i, f i) + (∑ i, if i ∈ T then 1 else 0) := by
        simp [x, Finset.sum_add_distrib]
      _ = b + R := by rw [hInd, hTcard]
      _ = B := by simpa [R] using Nat.add_sub_cancel' hbase_le
  refine ⟨x, hsumX, ?_⟩
  intro i
  have hfl : (f i : Rat) ≤ y i := hfloor_le i
  have hfr0 : 0 ≤ frac i := hfrac_nonneg i
  have hfr1 : frac i < 1 := hfrac_lt_one i
  by_cases hi : i ∈ T
  · have hS : i ∈ S := hTS hi
    have hfn : frac i ≠ 0 := (Finset.mem_filter.mp hS).2
    have hxi : x i = f i + 1 := by simp [x, hi]
    rw [hxi]
    have heq : ((f i + 1 : Nat) : Rat) - y i = 1 - frac i := by
      dsimp [frac]
      push_cast
      ring
    rw [heq, abs_of_nonneg (by linarith : 0 ≤ 1 - frac i)]
    linarith
  · have hxi : x i = f i := by simp [x, hi]
    rw [hxi]
    have heq : (f i : Rat) - y i = -frac i := by
      dsimp [frac]
      ring
    rw [heq, abs_of_nonpos (by linarith : -frac i ≤ 0)]
    linarith

/-- Every nonnegative rational can be rounded to a nonnegative even integer
with error at most one. -/
theorem exists_even_nat_within_one (x : Rat) (hx : 0 ≤ x) :
    ∃ n : Nat, Even n ∧ |(n : Rat) - x| ≤ 1 := by
  let n : Nat := 2 * Nat.floor ((x + 1) / 2)
  have harg : 0 ≤ (x + 1) / 2 := by positivity
  have hfloor : (Nat.floor ((x + 1) / 2) : Rat) ≤ (x + 1) / 2 :=
    Nat.floor_le harg
  have hstrict : (x + 1) / 2 < (Nat.floor ((x + 1) / 2) : Rat) + 1 :=
    Nat.lt_floor_add_one _
  have hupper : (n : Rat) ≤ x + 1 := by
    dsimp [n]
    push_cast
    linarith
  have hlower : x - 1 ≤ (n : Rat) := by
    dsimp [n]
    push_cast
    linarith
  refine ⟨n, ?_, ?_⟩
  · exact ⟨Nat.floor ((x + 1) / 2), by dsimp [n]; omega⟩
  · rw [abs_le]
    constructor <;> linarith

/-- Round 64 rational targets to a prescribed natural-number total. The targets
are shifted equally by the total discrepancy, then the balanced floor rule
keeps every integer block within one wire of that shifted target. -/
theorem balanced_rounding_with_total_error
    (y : Fin 64 → Rat) (B : Nat)
    (hshift : ∀ j, 0 ≤ y j + ((B : Rat) - ∑ i, y i) / 64) :
    ∃ x : Fin 64 → Nat,
      (∑ j, x j) = B ∧
        ∀ j, |(x j : Rat) - y j| ≤
          1 + |(B : Rat) - ∑ i, y i| / 64 := by
  let delta : Rat := (B : Rat) - ∑ i, y i
  let shifted : Fin 64 → Rat := fun j => y j + delta / 64
  have hsum : (∑ j, shifted j) = (B : Rat) := by
    dsimp [shifted, delta]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    norm_num
    ring
  obtain ⟨x, hxsum, hx⟩ := balanced_integer_rounding shifted B hshift hsum
  refine ⟨x, hxsum, ?_⟩
  intro j
  have hdecomp : (x j : Rat) - y j = ((x j : Rat) - shifted j) + delta / 64 := by
    simp [shifted]
    ring
  rw [hdecomp]
  calc
    |(x j : Rat) - shifted j + delta / 64|
        ≤ |(x j : Rat) - shifted j| + |delta / 64| := abs_add_le _ _
    _ ≤ 1 + |delta| / 64 := by
      have habs : |delta / 64| = |delta| / 64 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : Rat) < 64)]
      rw [habs]
      exact add_le_add (hx j) le_rfl
    _ = 1 + |(B : Rat) - ∑ i, y i| / 64 := by rfl

/-- Round 64 nonnegative targets to even naturals with a prescribed even
total. The error is two wires plus the equal share of the total correction.
This is the version used when a whole up-port must itself be even at the next
stage. -/
theorem balanced_even_rounding_with_total_error
    (y : Fin 64 → Rat) (B : Nat) (hB : Even B)
    (hshift : ∀ j, 0 ≤ y j + ((B : Rat) - ∑ i, y i) / 64) :
    ∃ x : Fin 64 → Nat,
      (∑ j, x j) = B ∧
      (∀ j, Even (x j)) ∧
      ∀ j, |(x j : Rat) - y j| ≤
        2 + |(B : Rat) - ∑ i, y i| / 64 := by
  obtain ⟨half, hBhalf⟩ := hB
  have hBcast : (B : Rat) = 2 * (half : Rat) := by
    rw [hBhalf]
    push_cast
    ring
  let delta : Rat := (B : Rat) - ∑ i, y i
  let shifted : Fin 64 → Rat := fun j => (y j + delta / 64) / 2
  have hshifted : ∀ j, 0 ≤ shifted j := by
    intro j
    exact div_nonneg (hshift j) (by norm_num)
  have hsum : (∑ j, shifted j) = (half : Rat) := by
    have hsumY : (∑ j : Fin 64, (y j + delta / 64)) = (B : Rat) := by
      dsimp [delta]
      simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
      norm_num
      ring
    calc
      (∑ j, shifted j) = (∑ j : Fin 64, (y j + delta / 64)) / 2 := by
        simp [shifted, Finset.sum_div]
      _ = (B : Rat) / 2 := by rw [hsumY]
      _ = (half : Rat) := by rw [hBcast]; norm_num
  obtain ⟨z, hzsum, hzerr⟩ := balanced_integer_rounding shifted half hshifted hsum
  let x : Fin 64 → Nat := fun j => 2 * z j
  refine ⟨x, ?_, ?_, ?_⟩
  · calc
      (∑ j, x j) = 2 * ∑ j, z j := by simp [x, Finset.mul_sum]
      _ = 2 * half := by rw [hzsum]
      _ = B := by omega
  · intro j
    exact ⟨z j, by simp [x, two_mul]⟩
  · intro j
    have hdecomp : (x j : Rat) - y j =
        2 * ((z j : Rat) - shifted j) + delta / 64 := by
      simp [x, shifted]
      ring
    rw [hdecomp]
    calc
      |2 * ((z j : Rat) - shifted j) + delta / 64|
          ≤ |2 * ((z j : Rat) - shifted j)| + |delta / 64| := abs_add_le _ _
      _ = 2 * |(z j : Rat) - shifted j| + |delta / 64| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Rat) ≤ 2)]
      _ ≤ 2 + |delta| / 64 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : Rat) < 64)]
            have h := hzerr j
            dsimp [shifted] at h
            dsimp [delta]
            linarith
      _ = 2 + |(B : Rat) - ∑ i, y i| / 64 := by rfl

/-- End and middle child targets remain nonnegative after the equal correction
needed to hit a prescribed integer total. -/
theorem candidate_child_shift_nonnegative
    (C debt correction : Rat) (coefficient : Fin 64 → Rat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcorrection : |correction| ≤ 70)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid) :
    ∀ j, 0 ≤ coefficient j * C + debt / 64 + correction / 64 := by
  intro j
  have hpos := candidate_adjusted_child_targets_positive C debt correction
    hC hdebtLo hdebtHi hcorrection
  rcases hcoeff j with hEnd | hMid
  · rw [hEnd]
    exact hpos.1.le
  · rw [hMid]
    exact hpos.2.le

/-- Integerize a candidate parent’s 64 child blocks once the real targets are
of the candidate end/middle forms and the prescribed total differs from their
sum by at most 70 wires. -/
theorem candidate_child_block_rounding
    (C debt : Rat) (coefficient : Fin 64 → Rat) (B : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid)
    (hdelta : |(B : Rat) - ∑ j, (coefficient j * C + debt / 64)| ≤ 70) :
    ∃ x : Fin 64 → Nat,
      (∑ j, x j) = B ∧
        ∀ j, |(x j : Rat) - (coefficient j * C + debt / 64)| ≤ 1 + 70 / 64 := by
  let target : Fin 64 → Rat := fun j => coefficient j * C + debt / 64
  have hshift := candidate_child_shift_nonnegative C debt
    ((B : Rat) - ∑ j, target j) coefficient hC hdebtLo hdebtHi ?_ hcoeff
  · obtain ⟨x, hxsum, hx⟩ := balanced_rounding_with_total_error target B hshift
    refine ⟨x, hxsum, ?_⟩
    intro j
    have hbound : |(B : Rat) - ∑ i, target i| ≤ 70 := by
      simpa [target] using hdelta
    have hscaled : |(B : Rat) - ∑ i, target i| / 64 ≤ 70 / 64 := by
      exact div_le_div_of_nonneg_right hbound (by norm_num)
    have h := hx j
    dsimp [target] at h ⊢
    linarith
  · simpa [target] using hdelta

/-- At the active cutoff, the candidate up-flow can be rounded to an even
natural number that fits inside the parent bag. -/
theorem candidate_even_up_flow_exists
    (C debt idealUp eta : Rat) (coefficient : Fin 64 → Rat) (parent : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid)
    (heta : |eta| ≤ 69)
    (hidealUp : idealUp = upFlow * C - debt)
    (hparent : (parent : Rat) = idealUp +
      (∑ j, (coefficient j * C + debt / 64)) + eta) :
    ∃ up : Nat, Even up ∧ up ≤ parent ∧ |(up : Rat) - idealUp| ≤ 1 := by
  have hCpos : 0 < C := by
    have h : (0 : Rat) < 2 ^ 34 := by norm_num
    linarith
  have hupPos : 0 < idealUp := by
    rw [hidealUp]
    unfold upFlow ePos at *
    nlinarith
  have hcoeffLower : ∀ j, rEnd ≤ coefficient j := by
    intro j
    rcases hcoeff j with hEnd | hMid
    · rw [hEnd]
    · rw [hMid]
      unfold rEnd rMid
      norm_num
  have hsumCoeff : (64 : Rat) * rEnd ≤ ∑ j, coefficient j := by
    calc
      (64 : Rat) * rEnd = ∑ _j : Fin 64, rEnd := by simp
      _ ≤ ∑ j, coefficient j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hcoeffLower j
  have hsumLower : (64 : Rat) * rEnd * C + debt ≤
      ∑ j, (coefficient j * C + debt / 64) := by
    calc
      (64 : Rat) * rEnd * C + debt =
          ((64 : Rat) * rEnd) * C + 64 * (debt / 64) := by ring
      _ ≤ (∑ j, coefficient j) * C + 64 * (debt / 64) := by
        gcongr
      _ = ∑ j, (coefficient j * C + debt / 64) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp
  have hetaLo : -69 ≤ eta := (abs_le.mp heta).1
  have hsurplus : 1 ≤ (∑ j, (coefficient j * C + debt / 64)) + eta := by
    unfold rEnd at hsumLower
    unfold eAbs at hdebtLo
    nlinarith
  have hroom : idealUp + 1 ≤ (parent : Rat) := by
    rw [hparent]
    linarith
  obtain ⟨up, hupEven, hupNear⟩ := exists_even_nat_within_one idealUp hupPos.le
  have hupUpper' : (up : Rat) - idealUp ≤ 1 := (abs_le.mp hupNear).2
  have hupUpper : (up : Rat) ≤ idealUp + 1 := by linarith
  have hupFits : up ≤ parent := by
    exact_mod_cast (le_trans hupUpper hroom)
  exact ⟨up, hupEven, hupFits, hupNear⟩

/-- Complete the local integer split, given an actual parent occupancy within
69 wires of the real flow total and an up-flow rounded within one wire. -/
theorem candidate_integerize_parent
    (C debt idealUp eta : Rat) (coefficient : Fin 64 → Rat)
    (parent up : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid)
    (heta : |eta| ≤ 69)
    (hparent : (parent : Rat) = idealUp +
      (∑ j, (coefficient j * C + debt / 64)) + eta)
    (hup : |(up : Rat) - idealUp| ≤ 1)
    (hupLe : up ≤ parent) :
    ∃ blocks : Fin 64 → Nat,
      (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) - (coefficient j * C + debt / 64)| ≤ 1 + 70 / 64 := by
  have hcastSub : ((parent - up : Nat) : Rat) = (parent : Rat) - (up : Rat) := by
    exact Nat.cast_sub hupLe
  have hdeltaEq : ((parent - up : Nat) : Rat) -
      (∑ j, (coefficient j * C + debt / 64)) = eta + idealUp - up := by
    rw [hcastSub, hparent]
    ring
  have hdelta : |((parent - up : Nat) : Rat) -
      (∑ j, (coefficient j * C + debt / 64))| ≤ 70 := by
    rw [hdeltaEq]
    calc
      |eta + idealUp - up| = |eta + (idealUp - up)| := by congr 1 <;> ring
      _ ≤ |eta| + |idealUp - up| := abs_add_le _ _
      _ ≤ 69 + 1 := add_le_add heta (by simpa [abs_sub_comm] using hup)
      _ = 70 := by norm_num
  exact candidate_child_block_rounding C debt coefficient (parent - up)
    hC hdebtLo hdebtHi hcoeff hdelta

/-- Bootstrap variant of the signed integer flow: the parent is exactly the
sum of the chosen ideal up-flow and ideal child blocks, rather than an
interior flow with a bounded occupancy discrepancy. If the ideal up-flow is
positive and has one wire of room, the same balanced rounding realizes it. -/
theorem candidate_bootstrap_integer_flow_split
    (C debt idealUp : Rat) (coefficient : Fin 64 → Rat) (parent : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid)
    (hidealUp : 0 ≤ idealUp)
    (hparent : (parent : Rat) = idealUp +
      (∑ j, (coefficient j * C + debt / 64)))
    (hroom : idealUp + 1 ≤ parent) :
    ∃ up : Nat, ∃ blocks : Fin 64 → Nat,
      Even up ∧ up ≤ parent ∧ |(up : Rat) - idealUp| ≤ 1 ∧
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) - (coefficient j * C + debt / 64)| ≤
          1 + 70 / 64 := by
  obtain ⟨up, hupEven, hupNear⟩ := exists_even_nat_within_one idealUp hidealUp
  have hupUpper : (up : Rat) ≤ idealUp + 1 := by
    have h := (abs_le.mp hupNear).2
    linarith
  have hupLe : up ≤ parent := by
    exact_mod_cast le_trans hupUpper hroom
  obtain ⟨blocks, hblocks, hblockError⟩ := candidate_integerize_parent
    C debt idealUp 0 coefficient parent up hC hdebtLo hdebtHi hcoeff
    (by norm_num) (by simpa using hparent) hupNear hupLe
  exact ⟨up, blocks, hupEven, hupLe, hupNear, hblocks, hblockError⟩

/-- Full local integer realization of the signed parent flow: the up-flow is
even and all 64 child blocks are nonnegative integers summing to the remaining
parent wires. -/
theorem candidate_integer_flow_split
    (C debt idealUp eta : Rat) (coefficient : Fin 64 → Rat)
    (parent : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcoeff : ∀ j, coefficient j = rEnd ∨ coefficient j = rMid)
    (heta : |eta| ≤ 69)
    (hidealUp : idealUp = upFlow * C - debt)
    (hparent : (parent : Rat) = idealUp +
      (∑ j, (coefficient j * C + debt / 64)) + eta) :
    ∃ up : Nat, ∃ blocks : Fin 64 → Nat,
      Even up ∧ up ≤ parent ∧ |(up : Rat) - idealUp| ≤ 1 ∧
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) - (coefficient j * C + debt / 64)| ≤ 1 + 70 / 64 := by
  obtain ⟨up, hupEven, hupLe, hupError⟩ := candidate_even_up_flow_exists
    C debt idealUp eta coefficient parent hC hdebtLo hdebtHi hcoeff heta hidealUp hparent
  obtain ⟨blocks, hblocks, hblockError⟩ := candidate_integerize_parent
    C debt idealUp eta coefficient parent up hC hdebtLo hdebtHi hcoeff heta hparent
      hupError hupLe
  exact ⟨up, blocks, hupEven, hupLe, hupError, hblocks, hblockError⟩

/-- The integer occupancy error after one interior round stays below 69 wires:
one rounded block contributes at most `1 + 70/64`, and the 64 child up-flows
contribute at most one wire each. -/
theorem candidate_integer_occupancy_step_bound
    (blockError : Rat) (upError : Fin 64 → Rat)
    (hblock : |blockError| ≤ 1 + 70 / 64)
    (hup : ∀ j, |upError j| ≤ 1) :
    |blockError + ∑ j, upError j| ≤ 69 := by
  calc
    |blockError + ∑ j, upError j|
        ≤ |blockError| + |∑ j, upError j| := abs_add_le _ _
    _ ≤ (1 + 70 / 64) + ∑ j, |upError j| :=
      add_le_add hblock (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 + 70 / 64) + ∑ _j : Fin 64, (1 : Rat) := by
      gcongr with j
      exact hup j
    _ = 1 + 70 / 64 + 64 := by norm_num
    _ ≤ 69 := by norm_num

/-- Combine exact real occupancy conservation with the local integerized
parent split. One parent block error and the 64 independently rounded child
up-flows give the next bag's occupancy discrepancy. -/
theorem candidate_next_bag_discrepancy
    (actual : Nat) (parentBlock : Nat) (targetBlock : Rat)
    (childUp : Fin 64 → Nat) (targetChildUp : Fin 64 → Rat) (target : Rat)
    (hblock : |(parentBlock : Rat) - targetBlock| ≤ 1 + 70 / 64)
    (hup : ∀ j, |(childUp j : Rat) - targetChildUp j| ≤ 1)
    (hreal : target = targetBlock + ∑ j, targetChildUp j)
    (hactual : (actual : Rat) = parentBlock + ∑ j, (childUp j : Rat)) :
    |(actual : Rat) - target| ≤ 69 := by
  have heq : (actual : Rat) - target =
      ((parentBlock : Rat) - targetBlock) +
        ∑ j, ((childUp j : Rat) - targetChildUp j) := by
    rw [hactual, hreal, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact candidate_integer_occupancy_step_bound
    ((parentBlock : Rat) - targetBlock)
    (fun j => (childUp j : Rat) - targetChildUp j) hblock hup

end Tapered945
