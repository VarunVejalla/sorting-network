import PacketCountBridge
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A scale-transfer fact for sorted Boolean packets. It compares the counts
in fixed 64-wire rank cells to the ideal sorted profile at the same total
count, avoiding the incorrect assumption that these cells are individually
close to the packet mean. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

/-- Number of ones in the final `r` ranks of a sorted `m`-wire Boolean packet
with `X` ones. -/
def profileTail (m X r : Nat) : Nat := X - (m - r)

/-- Ideal number of ones in cell `i` of a sorted packet split into 64-wire
cells. This is the difference between two consecutive suffix counts. -/
def profileCell (K X i : Nat) : Nat :=
  profileTail (64 * K) X (64 * (i + 1)) - profileTail (64 * K) X (64 * i)

private theorem profileTail_mono_X (m r X Y : Nat) (h : Y ≤ X) :
    profileTail m Y r ≤ profileTail m X r := by
  simp only [profileTail]
  omega

private theorem profileTail_mono_r (m X a b : Nat) (h : a ≤ b) :
    profileTail m X a ≤ profileTail m X b := by
  simp only [profileTail]
  omega

private theorem profileTail_interval_count (m X a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    profileTail m X b - profileTail m X a =
      min (b - a) (X - (m - b)) := by
  by_cases h0 : X ≤ m - b
  · simp [profileTail, h0]
  · by_cases h1 : X ≤ m - a
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega

private theorem profileCell_mono_X (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileCell K Y i ≤ profileCell K X i := by
  have hab : 64 * i ≤ 64 * (i + 1) := by omega
  have hb : 64 * (i + 1) ≤ 64 * K := by omega
  rw [show profileCell K Y i = min 64 (Y - (64 * K - 64 * (i + 1))) from ?_]
  rw [show profileCell K X i = min 64 (X - (64 * K - 64 * (i + 1))) from ?_]
  · exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)
  · unfold profileCell
    rw [profileTail_interval_count (64 * K) X (64 * i) (64 * (i + 1)) hab hb]
    simp [Nat.mul_add]
  · unfold profileCell
    rw [profileTail_interval_count (64 * K) Y (64 * i) (64 * (i + 1)) hab hb]
    simp [Nat.mul_add]

private theorem sum_profileTail_differences (m K X : Nat) (hK : 64 * K ≤ m) :
    (∑ i ∈ range K,
      (profileTail m X (64 * (i + 1)) - profileTail m X (64 * i))) =
      profileTail m X (64 * K) - profileTail m X 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ]
      rw [ih (by omega)]
      simp only [profileTail]
      omega

theorem sum_profileCell_eq_total (K X : Nat) (hX : X ≤ 64 * K) :
    (∑ i ∈ range K, profileCell K X i) = X := by
  simp only [profileCell]
  rw [sum_profileTail_differences (64 * K) K X (by omega)]
  simp only [profileTail]
  omega

theorem profileCell_formula (K X i : Nat) (hi : i < K) :
    profileCell K X i = min 64 (X - (64 * K - 64 * (i + 1))) := by
  have hab : 64 * i ≤ 64 * (i + 1) := by omega
  have hb : 64 * (i + 1) ≤ 64 * K := by omega
  unfold profileCell
  rw [profileTail_interval_count (64 * K) X (64 * i) (64 * (i + 1)) hab hb]
  simp [Nat.mul_add]

theorem profileCell_mono (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileCell K Y i ≤ profileCell K X i := by
  exact profileCell_mono_X K X Y i hXY hi

/-- If one ideal sorted packet has at least as many ones as another, every
fixed rank cell receives at least as many. Across a partition, the absolute
cell-count differences add to exactly the total-count difference. -/
theorem profileCell_L1_exact (K X Y : Nat) (hXY : Y ≤ X) (hX : X ≤ 64 * K) :
    (∑ i ∈ range K,
      ((profileCell K X i - profileCell K Y i) +
        (profileCell K Y i - profileCell K X i))) = X - Y := by
  have hmono : ∀ i ∈ range K, profileCell K Y i ≤ profileCell K X i := by
    intro i hi
    exact profileCell_mono K X Y i hXY (mem_range.mp hi)
  have hzero : ∀ i ∈ range K, profileCell K Y i - profileCell K X i = 0 := by
    intro i hi
    exact Nat.sub_eq_zero_of_le (hmono i hi)
  have hsumX := sum_profileCell_eq_total K X hX
  have hsumY := sum_profileCell_eq_total K Y (by omega)
  have hsumDiff : (∑ i ∈ range K,
      (profileCell K X i - profileCell K Y i)) = X - Y := by
    have hcastSum : ((∑ i ∈ range K,
        (profileCell K X i - profileCell K Y i) : Nat) : Int) =
        ∑ i ∈ range K, ((profileCell K X i : Int) - (profileCell K Y i : Int)) := by
      simp only [Nat.cast_sum]
      apply sum_congr rfl
      intro i hi
      rw [Nat.cast_sub (hmono i hi)]
    have hcast : ((∑ i ∈ range K,
        (profileCell K X i - profileCell K Y i) : Nat) : Int) = ((X - Y : Nat) : Int) := by
      have hxInt : (∑ i ∈ range K, (profileCell K X i : Int)) = (X : Int) := by
        exact_mod_cast hsumX
      have hyInt : (∑ i ∈ range K, (profileCell K Y i : Int)) = (Y : Int) := by
        exact_mod_cast hsumY
      calc
        _ = (∑ i ∈ range K, (profileCell K X i : Int)) -
              (∑ i ∈ range K, (profileCell K Y i : Int)) := by
                rw [hcastSum, Finset.sum_sub_distrib]
        _ = (X : Int) - (Y : Int) := by rw [hxInt, hyInt]
        _ = ((X - Y : Nat) : Int) := by rw [Nat.cast_sub hXY]
    exact_mod_cast hcast
  have hsum : (∑ i ∈ range K,
      ((profileCell K X i - profileCell K Y i) +
        (profileCell K Y i - profileCell K X i))) =
      ∑ i ∈ range K, (profileCell K X i - profileCell K Y i) := by
    apply sum_congr rfl
    intro i hi
    rw [hzero i hi]
    omega
  rw [hsum]
  rw [hsumDiff]

/-- Fractional ideal profile for the common packet count `q + λ`. It is the
convex interpolation of the two neighboring sorted Boolean profiles. -/
def profileCellMean (K q : Nat) (frac : Real) (i : Nat) : Real :=
  (1 - frac) * profileCell K q i + frac * profileCell K (q + 1) i

theorem profileCellMean_sum (K q : Nat) (frac : Real) (hq : q < 64 * K) :
    (∑ i ∈ range K, profileCellMean K q frac i) = q + frac := by
  have hqsum : (∑ i ∈ range K, (profileCell K q i : Real)) = q := by
    exact_mod_cast sum_profileCell_eq_total K q (by omega)
  have hq1sum : (∑ i ∈ range K, (profileCell K (q + 1) i : Real)) = q + 1 := by
    exact_mod_cast sum_profileCell_eq_total K (q + 1) (by omega)
  unfold profileCellMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, hq1sum]
  ring

/-- The aggregate absolute error of a sorted packet's 64-cell counts from
its fractional ideal profile is exactly its whole-packet count error. Thus
the 64-cell baseline variation does not get charged to the mixing error. -/
theorem profileCellMean_L1_exact (K X q : Nat) (frac : Real) (hq : q < 64 * K)
    (hXbound : X ≤ 64 * K) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range K,
      |(profileCell K X i : Real) - profileCellMean K q frac i|) =
        |(X : Real) - (q + frac)| := by
  have hmean := profileCellMean_sum K q frac hq
  have hxsum : (∑ i ∈ range K, (profileCell K X i : Real)) = X := by
    exact_mod_cast sum_profileCell_eq_total K X hXbound
  by_cases hX : X ≤ q
  · have hpoint : ∀ i ∈ range K,
        (profileCell K X i : Real) ≤ profileCellMean K q frac i := by
      intro i hi
      have hbase := profileCell_mono K q X i (by omega) (mem_range.mp hi)
      have hnext := profileCell_mono K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileCellMean
      have hn : (profileCell K q i : Real) ≤ profileCell K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileCell K X i : Real) ≤ profileCell K q i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileCell K X i : Real) - profileCellMean K q frac i|) =
          ∑ i ∈ range K, (profileCellMean K q frac i - (profileCell K X i : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range K, profileCellMean K q frac i) -
          (∑ i ∈ range K, (profileCell K X i : Real)) := by
        rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hmean, hxsum]
        have hXR : (X : Real) ≤ (q : Real) := by exact_mod_cast hX
        rw [abs_of_nonpos (by linarith [hfrac0])]
        ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range K,
        profileCellMean K q frac i ≤ (profileCell K X i : Real) := by
      intro i hi
      have hbase := profileCell_mono K X (q + 1) i (by omega) (mem_range.mp hi)
      have hnext := profileCell_mono K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileCellMean
      have hn : (profileCell K q i : Real) ≤ profileCell K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileCell K (q + 1) i : Real) ≤ profileCell K X i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileCell K X i : Real) - profileCellMean K q frac i|) =
          ∑ i ∈ range K, ((profileCell K X i : Real) - profileCellMean K q frac i) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range K, (profileCell K X i : Real)) -
          (∑ i ∈ range K, profileCellMean K q frac i) := by
        rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hxsum, hmean]
        have hXR : (q : Real) + 1 ≤ (X : Real) := by exact_mod_cast hX'
        rw [abs_of_nonneg (by linarith [hfrac1])]

theorem profileCellMean_cohort_L1_exact {c K : Nat} (X : Fin c → Nat)
    (q : Nat) (frac : Real) (hq : q < 64 * K) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hX : ∀ i, X i ≤ 64 * K) :
    (∑ i : Fin c, ∑ j ∈ range K,
      |(profileCell K (X i) j : Real) - profileCellMean K q frac j|) =
        ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro i _
  exact profileCellMean_L1_exact K (X i) q frac hq (hX i) hfrac0 hfrac1

/-- The fine-profile error of a cohort is bounded in square by cohort size
times the coarse packet-count energy. -/
theorem profileCellMean_cohort_L1_sq {c K : Nat} (X : Fin c → Nat)
    (q : Nat) (frac : Real) (hq : q < 64 * K) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hX : ∀ i, X i ≤ 64 * K) :
    ((∑ i : Fin c, ∑ j ∈ range K,
      |(profileCell K (X i) j : Real) - profileCellMean K q frac j|)^2) ≤
      (c : Real) * ∑ i : Fin c, ((X i : Real) - (q + frac))^2 := by
  rw [profileCellMean_cohort_L1_exact X q frac hq hfrac0 hfrac1 hX]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(X i : Real) - (q + frac)|) (fun _ => (1 : Real)))

