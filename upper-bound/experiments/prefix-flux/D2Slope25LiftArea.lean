import D2Slope25LiftProvider

open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25Provider
open Chvatal.D2Slope25LiftProvider

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Chvatal.D2Slope25LiftArea

abbrev Col := Fin 64

def shiftedDestEquiv (b : Nat) : Equiv.Perm Col where
  toFun := shiftedDest b
  invFun := fun d => Fin.mk ((d.val + (25 * b) % 64) % 64) (Nat.mod_lt _ (by decide))
  left_inv := by
    intro d
    apply Fin.ext
    dsimp [shiftedDest]
    have hs : (25 * b) % 64 < 64 := Nat.mod_lt _ (by decide)
    omega
  right_inv := by
    intro d
    apply Fin.ext
    dsimp [shiftedDest]
    have hs : (25 * b) % 64 < 64 := Nat.mod_lt _ (by decide)
    omega

theorem sum_shiftedDest (b : Nat) (f : Col -> Rat) :
    (Finset.univ.sum fun d : Col => f (shiftedDest b d)) =
      (Finset.univ.sum fun d : Col => f d) := by
  let e := shiftedDestEquiv b
  change (Finset.univ.sum fun d : Col => f (e d)) = _
  exact Equiv.sum_comp e f

theorem fullHeightTwoShuffle_area_per_column_le_169_over_eight
    (h : Col -> Nat) :
    (1 / 2 : Rat) *
      (Finset.univ.sum fun i : Col =>
        ((fullHeightTwoShuffle h i : Rat) -
          (Finset.univ.sum fun j : Col => (fullHeightTwoShuffle h j : Rat)) / 64) ^ 2) / 64
      <= 169 / 8 := by
  let qNat := Finset.univ.sum fun c : Col => h c / 64
  let q : Rat := qNat
  let profile := residualProfile h
  let g := fun d : Col => slope35Then25PhysicalOutputHeight profile d
  let gsum := Finset.univ.sum fun d : Col => (g d : Rat)
  have hpoint (d : Col) :
      (fullHeightTwoShuffle h d : Rat) = q + (g (shiftedDest qNat d) : Rat) := by
    have hn : fullHeightTwoShuffle h d =
        qNat + g (shiftedDest qNat d) := by
      rw [fullHeightTwoShuffle_eq_quotient_residual,
        residualTwoShuffle_eq_provider]
    have hcast := congrArg (fun x : Nat => (x : Rat)) hn
    simpa only [Nat.cast_add, q] using hcast
  have hsum :
      (Finset.univ.sum fun d : Col => (fullHeightTwoShuffle h d : Rat)) =
        64 * q + gsum := by
    calc
      (Finset.univ.sum fun d : Col => (fullHeightTwoShuffle h d : Rat)) =
          Finset.univ.sum fun d : Col => q + (g (shiftedDest qNat d) : Rat) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hpoint d
      _ = (Finset.univ.sum fun _ : Col => q) +
          (Finset.univ.sum fun d : Col => (g (shiftedDest qNat d) : Rat)) :=
        Finset.sum_add_distrib
      _ = 64 * q + gsum := by
        have hshift := sum_shiftedDest qNat (fun d : Col => (g d : Rat))
        change (Finset.univ.sum fun _ : Col => q) +
          (Finset.univ.sum fun d : Col => (g (shiftedDest qNat d) : Rat)) =
          64 * q + gsum
        rw [hshift]
        simp [q, gsum, Finset.sum_const, Fintype.card_fin]
  have hmean :
      (Finset.univ.sum fun j : Col => (fullHeightTwoShuffle h j : Rat)) / 64 =
        q + gsum / 64 := by
    rw [hsum]
    ring
  have hcenter (d : Col) :
      (fullHeightTwoShuffle h d : Rat) -
          (Finset.univ.sum fun j : Col => (fullHeightTwoShuffle h j : Rat)) / 64 =
        (g (shiftedDest qNat d) : Rat) - gsum / 64 := by
    rw [hpoint d, hmean]
    ring
  have hsq :
      (Finset.univ.sum fun d : Col =>
        ((fullHeightTwoShuffle h d : Rat) -
          (Finset.univ.sum fun j : Col => (fullHeightTwoShuffle h j : Rat)) / 64) ^ 2) =
      (Finset.univ.sum fun d : Col =>
        ((g (shiftedDest qNat d) : Rat) - gsum / 64) ^ 2) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcenter]
  calc
    (1 / 2 : Rat) *
        (Finset.univ.sum fun i : Col =>
          ((fullHeightTwoShuffle h i : Rat) -
            (Finset.univ.sum fun j : Col => (fullHeightTwoShuffle h j : Rat)) / 64) ^ 2) / 64 =
      (1 / 2 : Rat) *
        (Finset.univ.sum fun d : Col =>
          ((g (shiftedDest qNat d) : Rat) - gsum / 64) ^ 2) / 64 := by rw [hsq]
    _ = (1 / 2 : Rat) *
        (Finset.univ.sum fun d : Col => ((g d : Rat) - gsum / 64) ^ 2) / 64 := by
      exact congrArg (fun x : Rat => (1 / 2 : Rat) * x / 64)
        (sum_shiftedDest qNat (fun d : Col => ((g d : Rat) - gsum / 64) ^ 2))
    _ <= 169 / 8 := by
      simpa [g, gsum] using
        slope35_then_slope25_area_per_column_le_169_over_eight profile



def rectangularUniformDensity (actual : Col -> Nat) : Rat :=
  (Finset.univ.sum fun c : Col => (actual c : Rat)) / (64 * 4096)

def rectangularPortError (actual : Col -> Nat) (cuts : Col -> Nat -> Nat)
    (p : Fin ports) : Rat :=
  abs (Finset.univ.sum fun c : Col =>
    ((Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
        (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
      Chvatal.D2RankAlignment.ratPrefixIntervalMass
        (rectangularUniformDensity actual * 4096)
        (cuts c p.val) (cuts c (p.val + 1))))

theorem area_to_ragged_port_l1_le_416
    (actual : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hactual : forall c, actual c <= 4096)
    (harea : (1 / 2 : Rat) *
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) / 64 <= 169 / 8) :
    (Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p) <= 416 := by
  let theta : Rat := rectangularUniformDensity actual
  have htheta_avg : theta * 4096 =
      (Finset.univ.sum fun c : Col => (actual c : Rat)) / 64 := by
    dsimp [theta, rectangularUniformDensity]
    field_simp
  have htheta_nonneg : 0 <= theta := by
    dsimp [theta, rectangularUniformDensity]
    exact div_nonneg
      (Finset.sum_nonneg fun c hc => Nat.cast_nonneg (actual c))
      (by norm_num)
  have htotal_le :
      (Finset.univ.sum fun c : Col => (actual c : Rat)) <= (64 : Rat) * 4096 := by
    calc
      (Finset.univ.sum fun c : Col => (actual c : Rat)) <=
          (Finset.univ.sum fun _ : Col => (4096 : Rat)) :=
        Finset.sum_le_sum fun c hc => by exact_mod_cast hactual c
      _ = (64 : Rat) * 4096 := by simp
  have htheta_le : theta <= 1 := by
    dsimp [theta, rectangularUniformDensity]
    field_simp
    nlinarith [htotal_le]
  have hdev :
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) - theta * 4096) ^ 2) =
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [htheta_avg]
  have hsumSq :
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) - theta * 4096) ^ 2) <= 2704 := by
    rw [hdev]
    nlinarith [harea]
  have hport := Chvatal.D2RankAlignment.ragged_nat_rational_port_variance_bound
    actual (fun _ : Col => 4096) cuts ports theta
    hzero hend hmono hactual htheta_nonneg htheta_le
  have hport' :
      (Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p) ^ 2 <=
        64 * (Finset.univ.sum fun c : Col =>
          ((actual c : Rat) - theta * 4096) ^ 2) := by
    simpa [rectangularPortError, rectangularUniformDensity, theta,
      Fintype.card_fin] using hport
  have hport416 :
      (Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p) ^ 2 <=
        416 ^ 2 := by
    rw [hdev] at hport'
    nlinarith [hport', hsumSq]
  have hnonneg :
      0 <= Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p :=
    Finset.sum_nonneg fun p hp => abs_nonneg _
  have hdesired :
      (Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p) <= 416 :=
    by nlinarith [hport416]
  exact hdesired

/-- Refining every port by its output column still costs at most416 in l1.
Unlike `area_to_ragged_port_l1_le_416`, this does not sum column errors before
taking absolute values. The stronger form is what permits splitting ports at
tile/column offsets before rebatching them into the next sender profile. -/
theorem area_to_column_refined_port_l1_le_416
    (actual : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hactual : forall c, actual c <= 4096)
    (harea : (1 / 2 : Rat) *
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) / 64 <= 169 / 8) :
    (Finset.univ.sum fun c : Col =>
      Finset.univ.sum fun p : Fin ports =>
        abs ((Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
          Chvatal.D2RankAlignment.ratPrefixIntervalMass
            (rectangularUniformDensity actual * 4096)
            (cuts c p.val) (cuts c (p.val + 1)))) <= 416 := by
  let theta : Rat := rectangularUniformDensity actual
  have htheta_avg : theta * 4096 =
      (Finset.univ.sum fun c : Col => (actual c : Rat)) / 64 := by
    dsimp [theta, rectangularUniformDensity]
    field_simp
  have htheta_nonneg : 0 <= theta := by
    dsimp [theta, rectangularUniformDensity]
    exact div_nonneg
      (Finset.sum_nonneg fun c hc => Nat.cast_nonneg (actual c)) (by norm_num)
  have htotal_le :
      (Finset.univ.sum fun c : Col => (actual c : Rat)) <= (64 : Rat) * 4096 := by
    calc
      _ <= Finset.univ.sum fun _ : Col => (4096 : Rat) :=
        Finset.sum_le_sum fun c hc => by exact_mod_cast hactual c
      _ = (64 : Rat) * 4096 := by simp
  have htheta_le : theta <= 1 := by
    dsimp [theta, rectangularUniformDensity]
    field_simp
    nlinarith [htotal_le]
  have hdev :
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) - theta * 4096) ^ 2) =
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [htheta_avg]
  have hsumSq :
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) - theta * 4096) ^ 2) <= 2704 := by
    rw [hdev]
    nlinarith [harea]
  have hcolumn (c : Col) :
      (Finset.univ.sum fun p : Fin ports =>
        abs ((Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
          Chvatal.D2RankAlignment.ratPrefixIntervalMass
            (theta * 4096) (cuts c p.val) (cuts c (p.val + 1)))) =
        abs ((actual c : Rat) - theta * 4096) := by
    have href_le : theta * 4096 <= (4096 : Rat) := by nlinarith [htheta_le]
    have href_nonneg : 0 <= theta * 4096 :=
      mul_nonneg htheta_nonneg (by norm_num)
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      abs ((Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
          (cuts c i) (cuts c (i + 1)) : Rat) -
        Chvatal.D2RankAlignment.ratPrefixIntervalMass
          (theta * 4096) (cuts c i) (cuts c (i + 1))))]
    exact Chvatal.D2RankAlignment.nat_actual_rational_reference_port_partition
      (actual c) (theta * 4096) (cuts c) ports (hzero c) 4096 (hend c)
      (by intro i hi; exact hmono c i hi) (hactual c)
      href_le href_nonneg
  have hsumAbs :
      (Finset.univ.sum fun c : Col => abs ((actual c : Rat) - theta * 4096)) ^ 2 <=
        64 * (Finset.univ.sum fun c : Col =>
          ((actual c : Rat) - theta * 4096) ^ 2) := by
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Col) (fun _ : Col => (1 : Rat))
      (fun c => abs ((actual c : Rat) - theta * 4096))
    simpa [Fintype.card_fin] using hcauchy
  have hsq :
      (Finset.univ.sum fun c : Col => abs ((actual c : Rat) - theta * 4096)) ^ 2 <=
        416 ^ 2 := by
    calc
      _ <= 64 * (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) - theta * 4096) ^ 2) := hsumAbs
      _ <= 64 * 2704 := by nlinarith [hsumSq]
      _ = 416 ^ 2 := by norm_num
  have hnonneg :
      0 <= Finset.univ.sum fun c : Col => abs ((actual c : Rat) - theta * 4096) :=
    Finset.sum_nonneg fun c hc => abs_nonneg _
  calc
    _ = Finset.univ.sum fun c : Col => abs ((actual c : Rat) - theta * 4096) := by
      apply Finset.sum_congr rfl
      intro c hc
      simpa [theta] using hcolumn c
    _ <= 416 := by nlinarith [hsq]

/-- The physical 4096-row two-shuffle core satisfies the refined
column/port l1 contract for every complete interval partition in every
output column. -/
theorem fullHeightTwoShuffle_column_refined_port_l1_le_416
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096) :
    (Finset.univ.sum fun c : Col =>
      Finset.univ.sum fun p : Fin ports =>
        abs ((Chvatal.D2RankAlignment.prefixIntervalMass
            (fullHeightTwoShuffle sourceHeight c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
          Chvatal.D2RankAlignment.ratPrefixIntervalMass
            (rectangularUniformDensity
              (fun d => fullHeightTwoShuffle sourceHeight d) * 4096)
            (cuts c p.val) (cuts c (p.val + 1)))) <= 416 := by
  apply area_to_column_refined_port_l1_le_416
    (fun c => fullHeightTwoShuffle sourceHeight c) cuts ports hzero hend hmono
    (fun c => fullHeightTwoShuffle_le_4096 sourceHeight hinput c)
  exact fullHeightTwoShuffle_area_per_column_le_169_over_eight sourceHeight


theorem fullHeightTwoShuffle_ragged_port_l1_le_416
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096) :
    (Finset.univ.sum fun p : Fin ports =>
      rectangularPortError (fun c => fullHeightTwoShuffle sourceHeight c) cuts p) <= 416 := by
  apply area_to_ragged_port_l1_le_416
    (fun c => fullHeightTwoShuffle sourceHeight c) cuts ports hzero hend hmono
    (fun c => fullHeightTwoShuffle_le_4096 sourceHeight hinput c)
  exact fullHeightTwoShuffle_area_per_column_le_169_over_eight sourceHeight

end Chvatal.D2Slope25LiftArea
