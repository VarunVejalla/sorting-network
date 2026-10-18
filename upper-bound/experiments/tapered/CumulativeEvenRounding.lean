import IntegerRounding

namespace Tapered945

/-! A possible repair for the retirement capacity gate: round cumulative
mass boundaries rather than rounding each register independently. Every
contiguous group then has error below two wires, and groups between exact
even boundaries have no error. The tree-order/scheduler integration is not
asserted here. -/

def evenCumulativeFloor (x : Rat) : Nat := 2 * Nat.floor (x / 2)

theorem evenCumulativeFloor_gap (x : Rat) (hx : 0 ≤ x) :
    0 ≤ x - (evenCumulativeFloor x : Rat) ∧
      x - (evenCumulativeFloor x : Rat) < 2 := by
  have hlo := Nat.floor_le (show 0 ≤ x / 2 by positivity)
  have hhi := Nat.lt_floor_add_one (x / 2)
  unfold evenCumulativeFloor
  push_cast
  constructor <;> linarith

theorem evenCumulativeFloor_mono : Monotone evenCumulativeFloor := by
  intro x y hxy
  unfold evenCumulativeFloor
  exact Nat.mul_le_mul_left 2 (Nat.floor_mono (by linarith : x / 2 ≤ y / 2))

@[simp] theorem evenCumulativeFloor_even (k : Nat) :
    evenCumulativeFloor (2 * (k : Rat)) = 2 * k := by
  simp [evenCumulativeFloor]

def massPrefix (y : Nat → Rat) (k : Nat) : Rat := ∑ i ∈ Finset.range k, y i

def roundedMassPrefix (y : Nat → Rat) (k : Nat) : Nat := evenCumulativeFloor (massPrefix y k)

def roundedMassCell (y : Nat → Rat) (i : Nat) : Nat :=
  roundedMassPrefix y (i + 1) - roundedMassPrefix y i

theorem massPrefix_nonneg (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i) (k : Nat) :
    0 ≤ massPrefix y k := Finset.sum_nonneg (fun i _ => hy i)

theorem roundedMassPrefix_mono (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i) :
    Monotone (roundedMassPrefix y) := by
  intro p q hpq
  apply evenCumulativeFloor_mono
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpq) (fun i _ _ => hy i)

theorem roundedMassCell_even (y : Nat → Rat) (i : Nat) : Even (roundedMassCell y i) := by
  unfold roundedMassCell roundedMassPrefix evenCumulativeFloor
  exact ⟨Nat.floor (massPrefix y (i + 1) / 2) - Nat.floor (massPrefix y i / 2), by omega⟩

theorem roundedMassCell_sum (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i) (k : Nat) :
    (∑ i ∈ Finset.range k, roundedMassCell y i) = roundedMassPrefix y k := by
  induction k with
  | zero => simp [roundedMassPrefix, massPrefix, evenCumulativeFloor]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hle := roundedMassPrefix_mono y hy (show k ≤ k + 1 by omega)
    unfold roundedMassCell
    omega

theorem roundedMassCell_interval (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i)
    (p q : Nat) (hpq : p ≤ q) :
    (∑ i ∈ Finset.Ico p q, roundedMassCell y i) =
      roundedMassPrefix y q - roundedMassPrefix y p := by
  have h := Finset.sum_range_add_sum_Ico (f := roundedMassCell y) hpq
  rw [roundedMassCell_sum y hy, roundedMassCell_sum y hy] at h
  omega

/-- A whole contiguous subtree costs fewer than two rounding wires,
independently of its number of descendant registers. -/
theorem roundedMassCell_interval_error (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i)
    (p q : Nat) (hpq : p ≤ q) :
    |((∑ i ∈ Finset.Ico p q, roundedMassCell y i) : Rat) -
      (massPrefix y q - massPrefix y p)| < 2 := by
  rw [← Nat.cast_sum, roundedMassCell_interval y hy p q hpq,
    Nat.cast_sub (roundedMassPrefix_mono y hy hpq)]
  have hp := evenCumulativeFloor_gap (massPrefix y p) (massPrefix_nonneg y hy p)
  have hq := evenCumulativeFloor_gap (massPrefix y q) (massPrefix_nonneg y hy q)
  change |(evenCumulativeFloor (massPrefix y q) : Rat) -
    (evenCumulativeFloor (massPrefix y p) : Rat) - (massPrefix y q - massPrefix y p)| < 2
  rw [abs_lt]
  constructor <;> linarith

/-- Exact even cumulative boundaries preserve a retiring component's
cardinality exactly. This is stronger than registerwise error control. -/
theorem roundedMassCell_interval_exact (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i)
    (p q a b : Nat) (hpq : p ≤ q)
    (hp : massPrefix y p = 2 * (a : Rat))
    (hq : massPrefix y q = 2 * (b : Rat)) :
    (∑ i ∈ Finset.Ico p q, roundedMassCell y i) = 2 * b - 2 * a := by
  rw [roundedMassCell_interval y hy p q hpq]
  simp only [roundedMassPrefix, hp, hq, evenCumulativeFloor_even]

/-- At retirement, take the exact native complement of the stored subtree.
If cumulative rounding placed the stored subtree within two wires of its
nominal mass, the complementary outgoing block is even and remains within
the same error of the complementary signed-flow target. The hypotheses
`hstoredEven` and `hstoredLe` are the parity and capacity obligations for the
global tree scheduler. -/
theorem retirement_complement_from_rounded_interval
    (y : Nat → Rat) (hy : ∀ i, 0 ≤ y i)
    (p q B stored : Nat) (targetDown : Rat) (hpq : p ≤ q)
    (hstored : stored = ∑ i ∈ Finset.Ico p q, roundedMassCell y i)
    (hstoredEven : Even stored) (hBEven : Even B) (hstoredLe : stored ≤ B)
    (hnative : (B : Rat) = targetDown + (massPrefix y q - massPrefix y p)) :
    Even (B - stored) ∧
      |((B - stored : Nat) : Rat) - targetDown| < 2 := by
  have hround := roundedMassCell_interval_error y hy p q hpq
  have herror : |(stored : Rat) - (massPrefix y q - massPrefix y p)| < 2 := by
    rw [← Nat.cast_sum, ← hstored] at hround
    exact hround
  constructor
  · obtain ⟨b, hb⟩ := hBEven
    obtain ⟨s, hs⟩ := hstoredEven
    refine ⟨b - s, ?_⟩
    omega
  · rw [Nat.cast_sub hstoredLe]
    have hbalance : (B : Rat) - (stored : Rat) - targetDown =
        (massPrefix y q - massPrefix y p) - (stored : Rat) := by
      rw [hnative]
      ring
    rw [hbalance, abs_sub_comm]
    exact herror

end Tapered945
