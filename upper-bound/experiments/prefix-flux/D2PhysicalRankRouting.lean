import D2ColumnRebatchBridge
import D2RankProfileRouting

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

namespace Chvatal.D2PhysicalRankRouting

open Chvatal.D2RankAlignment
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2RankProfileRouting

abbrev Col := Fin 64

/-- Count marked wires in one row-major column-port cell when each column is
sorted and has the indicated false-prefix height. -/
def rowMajorPortCount (m h lo hi : Nat) : Nat :=
  (Finset.range m).sum fun r =>
    if lo <= r ∧ r < hi ∧ r < h then 1 else 0

/-- The physical row-major cell count is exactly the interval mass used in
the fixed-core rank-profile transfer. -/
theorem rowMajorPortCount_eq_prefixIntervalMass
    (m h lo hi : Nat) (hhi : hi <= m) :
    rowMajorPortCount m h lo hi = prefixIntervalMass h lo hi := by
  classical
  have hfilter :
      (Finset.range m).filter (fun r => lo <= r ∧ r < hi ∧ r < h) =
        Finset.Ico lo (min hi h) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  unfold rowMajorPortCount
  rw [Finset.sum_boole, hfilter, Nat.card_Ico]
  unfold prefixIntervalMass
  by_cases hih : hi <= h
  · rw [Nat.min_eq_left hih,
      Nat.min_eq_right (Nat.sub_le_sub_right hih lo)]
    simp
  · have hhi' : h <= hi := Nat.le_of_not_ge hih
    rw [Nat.min_eq_right hhi',
      Nat.min_eq_left (Nat.sub_le_sub_right hhi' lo)]
    simp

private theorem cut_le_end {ports : Nat} (cuts : Nat -> Nat)
    (hmono : forall i, i < ports -> cuts i <= cuts (i + 1))
    {i : Nat} (hi : i <= ports) : cuts i <= cuts ports := by
  have hstep : forall d, d <= ports - i -> cuts i <= cuts (i + d) := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
        have hd' : d <= ports - i := by omega
        have ih' := ih hd'
        have hidx : i + d < ports := by omega
        have hnext := hmono (i + d) hidx
        simpa [Nat.add_assoc] using le_trans ih' hnext
  have hidx : i + (ports - i) = ports := by omega
  rw [← hidx]
  exact hstep _ (Nat.le_refl _)

/-- A `Fin 64` column profile, split at arbitrary monotone row boundaries,
has exactly the fixed-core cell counts. This is the local count adapter used
when a routed rank interval is refined by physical row-major columns. -/
theorem rowMajorPortProfileCount_eq
    (h : Col -> Nat) (m ports : Nat) (cuts : Col -> Nat -> Nat)
    (hend : forall c, cuts c ports = m)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (c : Col) (p : Fin ports) :
    rowMajorPortCount m (h c) (cuts c p.val) (cuts c (p.val + 1)) =
      prefixIntervalMass (h c) (cuts c p.val) (cuts c (p.val + 1)) := by
  apply rowMajorPortCount_eq_prefixIntervalMass
  · have hbound := cut_le_end (cuts c) (hmono c)
      (Nat.succ_le_of_lt p.isLt)
    rw [hend c] at hbound
    exact hbound

private def rankCellError (sourceHeight : Col -> Nat)
    (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (cell : Prod Col (Fin ports)) : Rat :=
  (prefixIntervalMass (fullHeightTwoShuffle sourceHeight cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
    (prefixIntervalMass (exactRankColumnHeight H cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)

/-- Literal row-major discrepancy on one column-port cell. -/
def rowMajorExactRankCellError (sourceHeight : Col -> Nat)
    (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (cell : Prod Col (Fin ports)) : Rat :=
  (rowMajorPortCount 4096
      (fullHeightTwoShuffle sourceHeight cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
    (rowMajorPortCount 4096
      (exactRankColumnHeight H cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)

/-- The literal count is exactly the rank-profile interval mass on both sides. -/
private theorem rowMajorExactRankCellError_eq
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hend : forall c, cuts c ports = 4096)
    (cell : Prod Col (Fin ports)) :
    rowMajorExactRankCellError sourceHeight cuts ports H cell =
      rankCellError sourceHeight cuts ports H cell := by
  have hindex : cell.2.val < ports := cell.2.isLt
  have hend' := hend cell.1
  have hbound := cut_le_end (cuts cell.1) (hmono cell.1) (Nat.succ_le_of_lt hindex)
  rw [hend'] at hbound
  have hact := rowMajorPortCount_eq_prefixIntervalMass 4096
    (fullHeightTwoShuffle sourceHeight cell.1)
    (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) hbound
  have hideal' := rowMajorPortCount_eq_prefixIntervalMass 4096
    (exactRankColumnHeight H cell.1)
    (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) hbound
  simp only [rowMajorExactRankCellError, rankCellError, hact, hideal']

/-- After routing physical row-major port cells to arbitrary receivers, the
literal wire-count profile inherits the fixed core's 448-key l1 bound. This
adapts the algebraic certificate to addresses; the scheduler must still prove
that its actual cuts and receiver tags are these ones. -/
theorem rowMajorPhysicalGroupedError_le_448
    {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (group : Prod Col (Fin ports) -> J)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
        group cell = j).sum
          (rowMajorExactRankCellError sourceHeight cuts ports H))) <= 448 := by
  have hsame (cell : Prod Col (Fin ports)) :
      rowMajorExactRankCellError sourceHeight cuts ports H cell =
        rankCellError sourceHeight cuts ports H cell :=
    rowMajorExactRankCellError_eq sourceHeight cuts ports H hmono hend cell
  have hsum :
      (Finset.univ.sum fun j : J =>
        abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
          group cell = j).sum
            (rowMajorExactRankCellError sourceHeight cuts ports H))) =
      Finset.univ.sum fun j : J =>
        abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
          group cell = j).sum
            (rankCellError sourceHeight cuts ports H)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg abs
    apply Finset.sum_congr rfl
    intro cell hcell
    exact hsame cell
  rw [hsum]
  exact fullHeightTwoShuffle_exact_rank_rebinned_l1_le_448
    sourceHeight cuts ports H group hzero hend hmono hinput hHsum

end Chvatal.D2PhysicalRankRouting
