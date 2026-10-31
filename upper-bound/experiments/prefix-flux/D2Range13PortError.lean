import D2ColumnRebatchBridge
import D2Slope25LiftArea
import D2Range13Area

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Chvatal.D2Range13PortError

open Chvatal.D2RankAlignment
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2Slope25LiftArea

abbrev Col := Fin 64

/-- A complete port partition costs at most 448 exact-rank count error for
any 64-column profile of range at most 13. The proof is 416 to uniform density
from the variance bound, plus 32 for row-major rank rounding. -/
theorem exact_rank_port_error_le_448
    (actual : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hactual : forall c, actual c <= 4096)
    (hHsum : H = Finset.univ.sum fun c : Col => actual c)
    (lo hi : Nat) (hlo : forall c, lo <= actual c)
    (hhi : forall c, actual c <= hi) (hrange : hi - lo <= 13) :
    (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs ((prefixIntervalMass (actual cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
        (prefixIntervalMass (exactRankColumnHeight H cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat))) <= 448 := by
  let theta : Rat := (H : Rat) / 64
  have hsumRat : (Finset.univ.sum fun c : Col => (actual c : Rat)) = (H : Rat) := by
    exact_mod_cast hHsum.symm
  have htheta : theta = rectangularUniformDensity actual * 4096 := by
    dsimp [theta, rectangularUniformDensity]
    rw [hsumRat]
    field_simp
  have harea := Chvatal.D2Range13Area.area_le_169_over_eight actual lo hi hlo hhi hrange
  have h416 := Chvatal.D2Slope25LiftArea.area_to_column_refined_port_l1_le_416
    actual cuts ports
    hzero hend hmono hactual harea
  have htargetColumn (c : Col) :
      (Finset.univ.sum fun p : Fin ports =>
        abs ((prefixIntervalMass (exactRankColumnHeight H c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
          ratPrefixIntervalMass theta (cuts c p.val) (cuts c (p.val + 1)))) =
        abs ((exactRankColumnHeight H c : Rat) - theta) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      abs ((prefixIntervalMass (exactRankColumnHeight H c)
          (cuts c i) (cuts c (i + 1)) : Rat) -
        ratPrefixIntervalMass theta (cuts c i) (cuts c (i + 1))))]
    have hmod : H % 64 < 64 := Nat.mod_lt H (by decide)
    have hdecomp : H = 64 * (H / 64) + H % 64 := by omega
    have hHbound : H <= 64 * 4096 := by
      rw [hHsum]
      calc
        (Finset.univ.sum fun c : Col => actual c) <=
            Finset.univ.sum fun _ : Col => 4096 :=
          Finset.sum_le_sum fun c hc => hactual c
        _ = 64 * 4096 := by simp
    have hq : H / 64 <= 4096 := by omega
    have hcol : exactRankColumnHeight H c <= 4096 := by
      unfold exactRankColumnHeight
      split_ifs <;> omega
    have hrefNonneg : 0 <= theta := by
      dsimp [theta]
      exact div_nonneg (Nat.cast_nonneg H) (by norm_num)
    have hrefLe : theta <= 4096 := by
      dsimp [theta]
      have hr : (H : Rat) <= (64 : Rat) * 4096 := by exact_mod_cast hHbound
      calc
        (H : Rat) / 64 <= ((64 : Rat) * 4096) / 64 :=
          div_le_div_of_nonneg_right hr (by norm_num)
        _ = 4096 := by norm_num
    exact nat_actual_rational_reference_port_partition
      (exactRankColumnHeight H c) theta (cuts c) ports
      (hzero c) 4096 (hend c) (fun i hi => hmono c i hi)
      hcol hrefLe hrefNonneg
  have htarget :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          abs ((prefixIntervalMass (exactRankColumnHeight H c)
              (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
            ratPrefixIntervalMass theta (cuts c p.val) (cuts c (p.val + 1)))) <= 32 := by
    calc
      _ = Finset.univ.sum fun c : Col => abs ((exactRankColumnHeight H c : Rat) - theta) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact htargetColumn c
      _ <= 32 := by
        simpa [theta] using exactRankColumnHeight_uniform_l1_le_32 H
  let a : Prod Col (Fin ports) -> Rat := fun cell =>
    (prefixIntervalMass (actual cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)
  let i : Prod Col (Fin ports) -> Rat := fun cell =>
    (prefixIntervalMass (exactRankColumnHeight H cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)
  let u : Prod Col (Fin ports) -> Rat := fun cell =>
    ratPrefixIntervalMass theta (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1))
  have htriangle :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) => abs (a cell - i cell)) <=
      (Finset.univ.sum fun cell : Prod Col (Fin ports) => abs (a cell - u cell)) +
      (Finset.univ.sum fun cell : Prod Col (Fin ports) => abs (u cell - i cell)) := by
    calc
      _ <= Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          abs (a cell - u cell) + abs (u cell - i cell) := by
        apply Finset.sum_le_sum
        intro cell hc
        exact abs_sub_le _ _ _
      _ = _ := by rw [Finset.sum_add_distrib]
  have h416' : (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs (a cell - u cell)) <= 416 := by
    rw [Fintype.sum_prod_type' (fun c p => abs (a (c, p) - u (c, p)))]
    simpa [a, u, htheta] using h416
  have h32' : (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs (u cell - i cell)) <= 32 := by
    rw [Fintype.sum_prod_type' (fun c p => abs (u (c, p) - i (c, p)))]
    simpa [u, i, abs_sub_comm] using htarget
  calc
    _ = Finset.univ.sum fun cell : Prod Col (Fin ports) => abs (a cell - i cell) := by
      apply Finset.sum_congr rfl
      intro cell hc
      simp [a, i]
    _ <= 416 + 32 := le_trans htriangle (add_le_add h416' h32')
    _ = 448 := by norm_num

end Chvatal.D2Range13PortError
