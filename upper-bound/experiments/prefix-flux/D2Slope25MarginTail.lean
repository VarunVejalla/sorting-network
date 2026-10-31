import D2Slope25LiftArea

open Chvatal.D2Slope25LiftArea

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Chvatal.D2Slope25MarginTail

abbrev Col := Fin 64

/-- A single positive-part tail is paid for by the squared deviation. -/
theorem four_mul_posPart_margin_le_sq (z r : Rat) :
    4 * r * max 0 (z - r) <= z ^ 2 := by
  by_cases hz : r <= z
  · rw [max_eq_right (show 0 <= z - r by linarith)]
    nlinarith [sq_nonneg (z - 2 * r)]
  · rw [max_eq_left (show z - r <= 0 by linarith)]
    nlinarith [sq_nonneg z]

/-- A 2704 total squared-deviation budget gives a reciprocal margin tail. -/
theorem sum_posPart_margin_le_of_sq_sum_le
    (z : Col -> Rat) (r : Rat) (hr : 0 < r)
    (hsq : (Finset.univ.sum fun c : Col => (z c) ^ 2) <= 2704) :
    (Finset.univ.sum fun c : Col => max 0 (z c - r)) <= 676 / r := by
  have hpoint (c : Col) := four_mul_posPart_margin_le_sq (z c) r
  have hsum :
      4 * r * (Finset.univ.sum fun c : Col => max 0 (z c - r)) <=
        Finset.univ.sum fun c : Col => (z c) ^ 2 := by
    calc
      _ = Finset.univ.sum fun c : Col => 4 * r * max 0 (z c - r) := by
        rw [Finset.mul_sum]
      _ <= Finset.univ.sum fun c : Col => (z c) ^ 2 :=
        Finset.sum_le_sum fun c _ => hpoint c
  have hscaled :
      4 * r * (Finset.univ.sum fun c : Col => max 0 (z c - r)) <= 2704 :=
    le_trans hsum hsq
  have hden : 0 < 4 * r := by positivity
  have hdiv :
      (Finset.univ.sum fun c : Col => max 0 (z c - r)) <= 2704 / (4 * r) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
  calc
    _ <= 2704 / (4 * r) := hdiv
    _ = 676 / r := by ring

/-- The checked D2 variance bound gives a pointwise 52-row deviation bound,
since each column's squared deviation is one term of the total area. -/
theorem fullHeightTwoShuffle_column_deviation_le_52
    (sourceHeight : Col -> Nat) :
    let x : Col -> Rat := fun c => fullHeightTwoShuffle sourceHeight c
    let mu : Rat := (Finset.univ.sum fun d : Col => x d) / 64
    forall c, mu - 52 <= x c /\ x c <= mu + 52 := by
  let x : Col -> Rat := fun c => fullHeightTwoShuffle sourceHeight c
  let mu : Rat := (Finset.univ.sum fun d : Col => x d) / 64
  have harea := fullHeightTwoShuffle_area_per_column_le_169_over_eight sourceHeight
  have hvariance :
      (Finset.univ.sum fun c : Col => (x c - mu) ^ 2) <= 2704 := by
    dsimp [mu] at harea ⊢
    nlinarith [harea]
  change forall c : Col, mu - 52 <= x c /\ x c <= mu + 52
  intro c
  have hterm : (x c - mu) ^ 2 <=
      (Finset.univ.sum fun d : Col => (x d - mu) ^ 2) := by
    exact Finset.single_le_sum (fun d hd => sq_nonneg (x d - mu)) (Finset.mem_univ c)
  have hcoord : (x c - mu) ^ 2 <= 2704 := le_trans hterm hvariance
  constructor <;> nlinarith [sq_nonneg (x c - mu - 52),
    sq_nonneg (x c - mu + 52)]

/-- Beyond 52 rows from the exact rational mean, no column has any positive
excess or deficit at all. -/
theorem fullHeightTwoShuffle_margin_52_excess_eq_zero
    (sourceHeight : Col -> Nat) :
    let x : Col -> Rat := fun c => fullHeightTwoShuffle sourceHeight c
    let mu : Rat := (Finset.univ.sum fun d : Col => x d) / 64
    (Finset.univ.sum fun c : Col => max 0 (x c - mu - 52)) = 0 /\
      (Finset.univ.sum fun c : Col => max 0 (mu - x c - 52)) = 0 := by
  let x : Col -> Rat := fun c => fullHeightTwoShuffle sourceHeight c
  let mu : Rat := (Finset.univ.sum fun d : Col => x d) / 64
  have hdev := fullHeightTwoShuffle_column_deviation_le_52 sourceHeight
  change forall c : Col, mu - 52 <= x c /\ x c <= mu + 52 at hdev
  have hu (c : Col) : max 0 (x c - mu - 52) = 0 := by
    rw [max_eq_left]
    linarith [(hdev c).2]
  have hl (c : Col) : max 0 (mu - x c - 52) = 0 := by
    rw [max_eq_left]
    linarith [(hdev c).1]
  change (Finset.univ.sum fun c : Col => max 0 (x c - mu - 52)) = 0 /\
      (Finset.univ.sum fun c : Col => max 0 (mu - x c - 52)) = 0
  constructor <;> simp [hu, hl]

/-- The checked two-shuffle area theorem implies upper and lower margin tails
of at most `676/r` keys for every input height profile. -/
theorem fullHeightTwoShuffle_margin_tails_le
    (sourceHeight : Col -> Nat)
    (r : Rat) (hr : 0 < r) :
    (Finset.univ.sum fun c : Col =>
      max 0 ((fullHeightTwoShuffle sourceHeight c : Rat) -
        (Finset.univ.sum fun d : Col => (fullHeightTwoShuffle sourceHeight d : Rat)) / 64 - r)) <=
        676 / r ∧
    (Finset.univ.sum fun c : Col =>
      max 0 ((Finset.univ.sum fun d : Col => (fullHeightTwoShuffle sourceHeight d : Rat)) / 64 -
        (fullHeightTwoShuffle sourceHeight c : Rat) - r)) <= 676 / r := by
  let x : Col -> Rat := fun c => fullHeightTwoShuffle sourceHeight c
  let mu : Rat := (Finset.univ.sum fun d : Col => x d) / 64
  have harea := fullHeightTwoShuffle_area_per_column_le_169_over_eight sourceHeight
  have hvariance :
      (Finset.univ.sum fun c : Col => (x c - mu) ^ 2) <= 2704 := by
    dsimp [mu] at harea ⊢
    nlinarith [harea]
  have hupper := sum_posPart_margin_le_of_sq_sum_le
    (fun c => x c - mu) r hr hvariance
  have hlower := sum_posPart_margin_le_of_sq_sum_le
    (fun c => mu - x c) r hr (by
      have hsquare (c : Col) : (mu - x c) ^ 2 = (x c - mu) ^ 2 := by ring
      simpa only [hsquare] using hvariance)
  constructor
  · simpa [x, mu] using hupper
  · simpa [x, mu] using hlower

end Chvatal.D2Slope25MarginTail
