import D2RankAlignment
import D2Slope25LiftProvider

open scoped BigOperators

namespace Chvatal.D2WeightedPortDefect

open Chvatal.D2RankAlignment
open Chvatal.D2Slope25LiftProvider

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

abbrev Col := Fin 64

/-- Exact row-major rank profile on the 64 output columns. -/
def exactRankColumnHeight (H : Nat) (c : Col) : Nat :=
  H / 64 + if c.val < H % 64 then 1 else 0

/-- Prefix-mass discrepancy at a wire cut. -/
def endpointDefect (actual ideal : Nat) (cuts : Nat → Nat) (i : Nat) : Rat :=
  ((min actual (cuts i) : Nat) : Rat) -
    ((min ideal (cuts i) : Nat) : Rat)

/-- A weighted sum of signed port errors is exactly the discrete integration-
by-parts expression for the endpoint defects. The first term is the final
boundary contribution; the remaining sum prices changes in the spatial weight
at internal cuts. -/
theorem weighted_port_error_by_parts
    (actual ideal ports : Nat) (cuts : Nat → Nat) (weight : Nat → Rat)
    (hports : 0 < ports)
    (hmono : ∀ i < ports, cuts i ≤ cuts (i + 1)) :
    (∑ i ∈ Finset.range ports,
      weight i *
        ((prefixIntervalMass actual (cuts i) (cuts (i + 1)) : Rat) -
          (prefixIntervalMass ideal (cuts i) (cuts (i + 1)) : Rat))) =
      weight (ports - 1) * endpointDefect actual ideal cuts ports -
          weight 0 * endpointDefect actual ideal cuts 0 +
        ∑ i ∈ Finset.range (ports - 1),
          (weight i - weight (i + 1)) * endpointDefect actual ideal cuts (i + 1) := by
  let defect : Nat → Rat := endpointDefect actual ideal cuts
  have hlocal (i : Nat) (hi : i < ports) :
      (prefixIntervalMass actual (cuts i) (cuts (i + 1)) : Rat) -
          (prefixIntervalMass ideal (cuts i) (cuts (i + 1)) : Rat) =
        defect (i + 1) - defect i := by
    simpa [defect, endpointDefect] using
      prefixIntervalMass_signed_error_eq_endpoint_defects
        actual ideal (cuts i) (cuts (i + 1)) (hmono i hi)
  calc
    _ = ∑ i ∈ Finset.range ports,
        weight i * (defect (i + 1) - defect i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hlocal i (Finset.mem_range.mp hi)]
    _ = weight (ports - 1) * defect ports - weight 0 * defect 0 +
        ∑ i ∈ Finset.range (ports - 1),
          (weight i - weight (i + 1)) * defect (i + 1) := by
      have hsum := sum_weighted_prefix_increments_by_parts
        weight defect (ports - 1)
      simpa [defect, endpointDefect, Nat.sub_add_cancel hports] using hsum

/-- If every endpoint prefix defect is at most `K`, summation by parts bounds
the weighted port error by `K` times the total variation of the port weights,
including the two boundary weights. -/
theorem abs_weighted_prefix_increments_le_variation
    (weight defect : Nat → Rat) (n K : Nat)
    (hdefect : ∀ i ≤ n + 1, |defect i| ≤ K) :
    |∑ i ∈ Finset.range (n + 1),
        weight i * (defect (i + 1) - defect i)| ≤
      K * (|weight n| + |weight 0| +
        ∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by
  have hsum := sum_weighted_prefix_increments_by_parts weight defect n
  let internal : Rat :=
    ∑ i ∈ Finset.range n,
      (weight i - weight (i + 1)) * defect (i + 1)
  have hInternal :
      |internal| ≤ K * (∑ i ∈ Finset.range n,
        |weight i - weight (i + 1)|) := by
    calc
      |internal| ≤ ∑ i ∈ Finset.range n,
          |(weight i - weight (i + 1)) * defect (i + 1)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
          K * |weight i - weight (i + 1)| := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        rw [abs_mul]
        have hdi := hdefect (i + 1) (by omega : i + 1 ≤ n + 1)
        calc
          |weight i - weight (i + 1)| * |defect (i + 1)| ≤
              |weight i - weight (i + 1)| * (K : Rat) :=
            mul_le_mul_of_nonneg_left hdi (abs_nonneg _)
          _ = (K : Rat) * |weight i - weight (i + 1)| := by ring
      _ = K * (∑ i ∈ Finset.range n,
          |weight i - weight (i + 1)|) := by rw [Finset.mul_sum]
  have hleft : |weight n * defect (n + 1)| ≤ K * |weight n| := by
    rw [abs_mul]
    calc
      |weight n| * |defect (n + 1)| ≤ |weight n| * (K : Rat) :=
        mul_le_mul_of_nonneg_left
          (hdefect (n + 1) (by omega)) (abs_nonneg _)
      _ = (K : Rat) * |weight n| := by ring
  have hright : |weight 0 * defect 0| ≤ K * |weight 0| := by
    rw [abs_mul]
    calc
      |weight 0| * |defect 0| ≤ |weight 0| * (K : Rat) :=
        mul_le_mul_of_nonneg_left
          (hdefect 0 (by omega)) (abs_nonneg _)
      _ = (K : Rat) * |weight 0| := by ring
  have htriangle :
      |weight n * defect (n + 1) - weight 0 * defect 0 + internal| ≤
        |weight n * defect (n + 1)| + |weight 0 * defect 0| + |internal| := by
    calc
      _ ≤ |weight n * defect (n + 1) - weight 0 * defect 0| + |internal| :=
        abs_add_le _ _
      _ ≤ |weight n * defect (n + 1)| +
          |weight 0 * defect 0| + |internal| := by
        have hsub := abs_sub_le
          (weight n * defect (n + 1)) (0 : Rat) (weight 0 * defect 0)
        simpa using add_le_add_right hsub |internal|
  rw [hsum]
  change |weight n * defect (n + 1) - weight 0 * defect 0 + internal| ≤ _
  calc
    _ ≤ |weight n * defect (n + 1)| + |weight 0 * defect 0| + |internal| :=
      htriangle
    _ ≤ K * |weight n| + K * |weight 0| +
        K * (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by
      exact add_le_add (add_le_add hleft hright) hInternal
    _ = K * (|weight n| + |weight 0| +
        ∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by ring

/-- If the signed endpoint defects vanish at both ends, summation by parts
charges only internal variation of the spatial weights. In particular a
constant weight incurs zero fresh error; this is the form needed to charge a
local core only when a global prefix cuts through its sender. -/
theorem abs_weighted_prefix_increments_le_internal_variation
    (weight defect : Nat → Rat) (n K : Nat)
    (hdefect : ∀ i ≤ n + 1, |defect i| ≤ K)
    (hstart : defect 0 = 0) (hend : defect (n + 1) = 0) :
    |∑ i ∈ Finset.range (n + 1),
        weight i * (defect (i + 1) - defect i)| ≤
      K * (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by
  have hparts := sum_weighted_prefix_increments_by_parts weight defect n
  have hparts' :
      (∑ i ∈ Finset.range (n + 1),
        weight i * (defect (i + 1) - defect i)) =
        ∑ i ∈ Finset.range n,
          (weight i - weight (i + 1)) * defect (i + 1) := by
    simpa [hstart, hend] using hparts
  let internal : Rat :=
    ∑ i ∈ Finset.range n,
      (weight i - weight (i + 1)) * defect (i + 1)
  have hInternal :
      |internal| ≤ K * (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by
    calc
      |internal| ≤ ∑ i ∈ Finset.range n,
          |(weight i - weight (i + 1)) * defect (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
          K * |weight i - weight (i + 1)| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have hi' : i < n := Finset.mem_range.mp hi
        have hdi := hdefect (i + 1) (by omega : i + 1 ≤ n + 1)
        calc
          |weight i - weight (i + 1)| * |defect (i + 1)| ≤
              |weight i - weight (i + 1)| * (K : Rat) :=
            mul_le_mul_of_nonneg_left hdi (abs_nonneg _)
          _ = (K : Rat) * |weight i - weight (i + 1)| := by ring
      _ = K * (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := by
        rw [Finset.mul_sum]
  calc
    |∑ i ∈ Finset.range (n + 1),
        weight i * (defect (i + 1) - defect i)| = |internal| := by
          rw [hparts']
    _ ≤ K * (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) := hInternal

/-- A nonincreasing binary prefix indicator has total internal variation at
most one. Combined with the previous theorem, each sender pays fresh error
only when its physical prefix indicator changes across a port boundary. -/
theorem monotone_binary_weight_internal_variation_le_one
    (weight : Nat → Rat) (n : Nat)
    (hbinary : ∀ i ≤ n, weight i = 0 ∨ weight i = 1)
    (hmono : ∀ i j, i ≤ j → weight j ≤ weight i) :
    ∑ i ∈ Finset.range n, |weight i - weight (i + 1)| ≤ 1 := by
  have htel (m : Nat) :
      (∑ i ∈ Finset.range m, (weight i - weight (i + 1))) =
        weight 0 - weight m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hvariation :
      (∑ i ∈ Finset.range n, |weight i - weight (i + 1)|) =
        weight 0 - weight n := by
    calc
      _ = ∑ i ∈ Finset.range n, (weight i - weight (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_of_nonneg]
        exact sub_nonneg.mpr (hmono i (i + 1) (by omega))
      _ = weight 0 - weight n := htel n
  rw [hvariation]
  rcases hbinary 0 (Nat.zero_le n) with hstart0 | hstart1
  · rcases hbinary n (Nat.le_refl n) with hend0 | hend1
    · rw [hstart0, hend0]
      norm_num
    · have hcontra := hmono 0 n (Nat.zero_le n)
      rw [hstart0, hend1] at hcontra
      norm_num at hcontra
  · rcases hbinary n (Nat.le_refl n) with hend0 | hend1
    · rw [hstart1, hend0]
      norm_num
    · rw [hstart1, hend1]
      norm_num

/-- The range-13 fixed-core profile has a sender-size-independent prefix
defect at every row-major cut. The loose constant 896 is 64 columns times a
pointwise height discrepancy of at most14 from the exact rank-column profile.
This upgrades the aggregate 448 port error to a spatial endpoint contract. -/
theorem fullHeightTwoShuffle_row_cut_defect_le_896
    (sourceHeight : Col → Nat) (cuts : Col → Nat) :
    countDistance
      (Finset.univ.sum fun c : Col =>
        prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c))
      (Finset.univ.sum fun c : Col =>
        prefixIntervalMass
          (exactRankColumnHeight
            (Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c) c)
          0 (cuts c)) ≤ 896 := by
  let H := Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c
  have hdecomp : H = 64 * (H / 64) + H % 64 := by omega
  have hrem : H % 64 < 64 := Nat.mod_lt H (by decide)
  have hpoint (c : Col) :
      countDistance (fullHeightTwoShuffle sourceHeight c)
        (exactRankColumnHeight H c) ≤ 14 := by
    have hupper (d : Col) :
        fullHeightTwoShuffle sourceHeight d <=
          fullHeightTwoShuffle sourceHeight c + 13 :=
      fullHeightTwoShuffle_range_le_thirteen sourceHeight d c
    have hlower (d : Col) :
        fullHeightTwoShuffle sourceHeight c <=
          fullHeightTwoShuffle sourceHeight d + 13 :=
      fullHeightTwoShuffle_range_le_thirteen sourceHeight c d
    have hsumUpper : H <= 64 * (fullHeightTwoShuffle sourceHeight c + 13) := by
      dsimp [H]
      calc
        (Finset.univ.sum fun d : Col => fullHeightTwoShuffle sourceHeight d) <=
            Finset.univ.sum fun _ : Col => fullHeightTwoShuffle sourceHeight c + 13 :=
          Finset.sum_le_sum fun d hd => hupper d
        _ = 64 * (fullHeightTwoShuffle sourceHeight c + 13) := by simp
    have hsumLower : 64 * fullHeightTwoShuffle sourceHeight c <= H + 832 := by
      calc
        64 * fullHeightTwoShuffle sourceHeight c =
            Finset.univ.sum fun _ : Col => fullHeightTwoShuffle sourceHeight c := by simp
        _ <= Finset.univ.sum fun d : Col => fullHeightTwoShuffle sourceHeight d + 13 :=
          Finset.sum_le_sum fun d hd => hlower d
        _ = H + 832 := by simp [H, Finset.sum_add_distrib]
    have hqlo : H / 64 <= fullHeightTwoShuffle sourceHeight c + 13 := by
      omega
    have hqhi : fullHeightTwoShuffle sourceHeight c <= H / 64 + 13 := by
      omega
    have htargetLo : H / 64 <= exactRankColumnHeight H c := by
      unfold exactRankColumnHeight
      omega
    have htargetHi : exactRankColumnHeight H c <= H / 64 + 1 := by
      unfold exactRankColumnHeight
      split_ifs <;> omega
    unfold countDistance
    omega
  have hcut (c : Col) :
      countDistance
        (prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c))
        (prefixIntervalMass (exactRankColumnHeight H c) 0 (cuts c)) ≤
        countDistance (fullHeightTwoShuffle sourceHeight c)
          (exactRankColumnHeight H c) := by
    have hmass := prefixIntervalMass_count_change
      (fullHeightTwoShuffle sourceHeight c) (exactRankColumnHeight H c)
      0 (cuts c) (Nat.zero_le _)
    rcases hmass with ⟨hab, hba⟩
    unfold countDistance at *
    omega
  have hsum :
      (Finset.univ.sum fun c : Col =>
        countDistance
          (prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c))
          (prefixIntervalMass (exactRankColumnHeight H c) 0 (cuts c))) ≤ 896 := by
    calc
      _ ≤ Finset.univ.sum fun _ : Col => 14 :=
        Finset.sum_le_sum fun c hc => (hcut c).trans (hpoint c)
      _ = 896 := by simp [Fintype.card_fin]
  calc
    _ ≤ Finset.univ.sum fun c : Col =>
        countDistance
          (prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c))
          (prefixIntervalMass (exactRankColumnHeight H c) 0 (cuts c)) :=
      countDistance_sum_le Finset.univ _ _
    _ ≤ 896 := hsum

/-- Convert the natural-number prefix discrepancy above into the signed
rational endpoint error used by summation by parts. -/
theorem fullHeightTwoShuffle_row_cut_abs_endpoint_error_le_896
    (sourceHeight : Col → Nat) (cuts : Col → Nat) :
    |(Finset.univ.sum fun c : Col =>
        (prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c) : Rat)) -
      (Finset.univ.sum fun c : Col =>
        (prefixIntervalMass
          (exactRankColumnHeight
            (Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c) c)
          0 (cuts c) : Rat))| ≤ 896 := by
  let a := Finset.univ.sum fun c : Col =>
    prefixIntervalMass (fullHeightTwoShuffle sourceHeight c) 0 (cuts c)
  let b := Finset.univ.sum fun c : Col =>
    prefixIntervalMass
      (exactRankColumnHeight
        (Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c) c)
      0 (cuts c)
  have hdist : countDistance a b ≤ 896 := by
    simpa [a, b] using fullHeightTwoShuffle_row_cut_defect_le_896 sourceHeight cuts
  have hab : a - b ≤ 896 := by unfold countDistance at hdist; omega
  have hba : b - a ≤ 896 := by unfold countDistance at hdist; omega
  have hcastDist : (countDistance a b : Rat) =
      |(a : Rat) - (b : Rat)| := by
    unfold countDistance
    by_cases hab' : a ≤ b
    · have hz : a - b = 0 := Nat.sub_eq_zero_of_le hab'
      have hsub : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) :=
        Nat.cast_sub hab'
      push_cast
      rw [hz, hsub]
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab'))]
      ring
    · have hba' : b ≤ a := Nat.le_of_not_ge hab'
      have hz : b - a = 0 := Nat.sub_eq_zero_of_le hba'
      have hsub : ((a - b : Nat) : Rat) = (a : Rat) - (b : Rat) :=
        Nat.cast_sub hba'
      push_cast
      rw [hz, hsub]
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba'))]
      ring
  have hdistRat : (countDistance a b : Rat) ≤ 896 := by exact_mod_cast hdist
  have hboundRat : |(a : Rat) - (b : Rat)| ≤ 896 := by
    rw [← hcastDist]
    exact hdistRat
  simpa [a, b, Nat.cast_sum] using hboundRat

/-- Weighted signed port errors for a sequence of arbitrary monotone column
cuts are controlled by the total variation of the port weights. This composes
the pointwise row-cut contract with summation by parts; it is still a local
fixed-core statement and makes no claim about how the scheduler chooses cuts. -/
theorem fullHeightTwoShuffle_weighted_column_port_error_le_896_variation
    (sourceHeight : Col → Nat) (ports : Nat) (cuts : Nat → Col → Nat)
    (weight : Nat → Rat) (hports : 0 < ports)
    (hmono : ∀ c i, i < ports → cuts i c ≤ cuts (i + 1) c) :
    |∑ i ∈ Finset.range ports,
        weight i * (∑ c : Col,
          ((prefixIntervalMass (fullHeightTwoShuffle sourceHeight c)
              (cuts i c) (cuts (i + 1) c) : Rat) -
            (prefixIntervalMass
              (exactRankColumnHeight
                (∑ c : Col, fullHeightTwoShuffle sourceHeight c) c)
              (cuts i c) (cuts (i + 1) c) : Rat)))| ≤
      896 * (|weight (ports - 1)| + |weight 0| +
        ∑ i ∈ Finset.range (ports - 1), |weight i - weight (i + 1)|) := by
  let defect : Nat → Rat := fun i =>
    Finset.univ.sum fun col : Col =>
      ((min (fullHeightTwoShuffle sourceHeight col) (cuts i col) : Nat) : Rat) -
        ((min (exactRankColumnHeight
          (Finset.univ.sum fun d : Col => fullHeightTwoShuffle sourceHeight d) col)
            (cuts i col) : Nat) : Rat)
  have hbound (i : Nat) (hi : i ≤ ports) : |defect i| ≤ 896 := by
    have hrow := fullHeightTwoShuffle_row_cut_abs_endpoint_error_le_896
      sourceHeight (cuts i)
    simpa [defect, prefixIntervalMass] using hrow
  have hincrement (i : Nat) (hi : i < ports) :
      (∑ c : Col,
        ((prefixIntervalMass (fullHeightTwoShuffle sourceHeight c)
            (cuts i c) (cuts (i + 1) c) : Rat) -
          (prefixIntervalMass
            (exactRankColumnHeight
              (∑ c : Col, fullHeightTwoShuffle sourceHeight c) c)
            (cuts i c) (cuts (i + 1) c) : Rat))) =
        defect (i + 1) - defect i := by
    unfold defect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    simpa using prefixIntervalMass_signed_error_eq_endpoint_defects
      (fullHeightTwoShuffle sourceHeight c)
      (exactRankColumnHeight
        (∑ c : Col, fullHeightTwoShuffle sourceHeight c) c)
      (cuts i c) (cuts (i + 1) c) (hmono c i hi)
  have hsumEq :
      (∑ i ∈ Finset.range ports,
        weight i * (∑ c : Col,
          ((prefixIntervalMass (fullHeightTwoShuffle sourceHeight c)
              (cuts i c) (cuts (i + 1) c) : Rat) -
            (prefixIntervalMass
              (exactRankColumnHeight
                (∑ c : Col, fullHeightTwoShuffle sourceHeight c) c)
              (cuts i c) (cuts (i + 1) c) : Rat)))) =
        ∑ i ∈ Finset.range ports, weight i * (defect (i + 1) - defect i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hincrement i (Finset.mem_range.mp hi)]
  rw [hsumEq]
  have hgeneric := abs_weighted_prefix_increments_le_variation
    weight defect (ports - 1) 896 (by
      intro i hi
      apply hbound
      omega)
  have hports' : 1 ≤ ports := by omega
  simpa [Nat.sub_add_cancel hports'] using hgeneric

/-- The spatially weighted error bound adds over an arbitrary finite family
of sender tiles. Each tile may use its own monotone column cuts and its own
weights; the charged quantity is the sum of the per-tile weight variations. -/
theorem tiled_weighted_column_port_error_le_896_variation
    {tiles : Nat} (sourceHeight : Fin tiles → Col → Nat) (ports : Nat)
    (cuts : Nat → Fin tiles → Col → Nat)
    (weight : Fin tiles → Nat → Rat) (hports : 0 < ports)
    (hmono : ∀ t c i, i < ports → cuts i t c ≤ cuts (i + 1) t c) :
    |∑ t : Fin tiles, ∑ i ∈ Finset.range ports,
        weight t i * (∑ c : Col,
          ((prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) c)
              (cuts i t c) (cuts (i + 1) t c) : Rat) -
            (prefixIntervalMass
              (exactRankColumnHeight
                (∑ c : Col, fullHeightTwoShuffle (sourceHeight t) c) c)
              (cuts i t c) (cuts (i + 1) t c) : Rat)))| ≤
      896 * ∑ t : Fin tiles,
        (|weight t (ports - 1)| + |weight t 0| +
          ∑ i ∈ Finset.range (ports - 1), |weight t i - weight t (i + 1)|) := by
  let err : Fin tiles → Rat := fun t =>
    ∑ i ∈ Finset.range ports,
      weight t i * (∑ c : Col,
        ((prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) c)
            (cuts i t c) (cuts (i + 1) t c) : Rat) -
          (prefixIntervalMass
            (exactRankColumnHeight
              (∑ c : Col, fullHeightTwoShuffle (sourceHeight t) c) c)
            (cuts i t c) (cuts (i + 1) t c) : Rat)))
  let cost : Fin tiles → Rat := fun t =>
    |weight t (ports - 1)| + |weight t 0| +
      ∑ i ∈ Finset.range (ports - 1), |weight t i - weight t (i + 1)|
  have hlocal (t : Fin tiles) : |err t| ≤ 896 * cost t := by
    have h := fullHeightTwoShuffle_weighted_column_port_error_le_896_variation
      (sourceHeight t) ports (fun i c => cuts i t c) (weight t) hports
      (by intro c i hi; exact hmono t c i hi)
    simpa [err, cost] using h
  have hsum : |∑ t : Fin tiles, err t| ≤ 896 * ∑ t : Fin tiles, cost t := by
    calc
      |∑ t : Fin tiles, err t| ≤ ∑ t : Fin tiles, |err t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : Fin tiles, 896 * cost t :=
        Finset.sum_le_sum fun t ht => hlocal t
      _ = 896 * ∑ t : Fin tiles, cost t := by rw [Finset.mul_sum]
  simpa [err, cost] using hsum

end Chvatal.D2WeightedPortDefect
