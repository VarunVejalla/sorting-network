import D2Slope25RowMajorBridge
import D2RankRebatch

open scoped BigOperators
open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25RowMajorBridge

namespace Chvatal.D2Slope25TiledBridge

abbrev Col := Fin 64

private theorem rat_countDistance_eq_abs (a b : Nat) :
    (Chvatal.D2RankAlignment.countDistance a b : Rat) =
      abs ((a : Rat) - (b : Rat)) := by
  unfold Chvatal.D2RankAlignment.countDistance
  by_cases hab : a <= b
  · have hz : a - b = 0 := Nat.sub_eq_zero_of_le hab
    have hsub : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) :=
      Nat.cast_sub hab
    push_cast
    rw [hz, hsub]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    ring
  · have hba : b <= a := Nat.le_of_not_ge hab
    have hz : b - a = 0 := Nat.sub_eq_zero_of_le hba
    have hsub : ((a - b : Nat) : Rat) = (a : Rat) - (b : Rat) :=
      Nat.cast_sub hba
    push_cast
    rw [hz, hsub]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    ring

/-- The fixed-core provider's rational l1 estimate also bounds the exact
integer count-distance sum over all ports and tiles. -/
theorem tiled_exact_rank_count_distance_le_448_mul_tiles
    {tiles ports : Nat}
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (H : Fin tiles -> Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, H t <= 64 * 4096)
    (hHsum : forall t,
      H t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) p)
          (exactRankPortTargetCount (boundary t) (H t) p)) <= 448 * tiles := by
  have hEq :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          (Chvatal.D2RankAlignment.countDistance
            (exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)
            (exactRankPortTargetCount (boundary t) (H t) p) : Rat)) =
      Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortError
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) (H t) p := by
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro p hp
    rw [rat_countDistance_eq_abs]
    simp [exactRankPortError, exactRankPortActualCount,
      exactRankPortTargetCount, Nat.cast_sum]
  have hRat' :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          (Chvatal.D2RankAlignment.countDistance
            (exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)
            (exactRankPortTargetCount (boundary t) (H t) p) : Rat)) <=
        448 * tiles := by
    rw [hEq]
    calc
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortError
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) (H t) p) <=
        Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
          apply Finset.sum_le_sum
          intro t ht
          exact fullHeightTwoShuffle_exact_rank_port_l1_le_448
            (sourceHeight t) (boundary t) ports (H t)
            (hzero t) (hend t) (hmono t) (hH t) (hHsum t) (hinput t)
      _ = 448 * tiles := by simp [Finset.sum_const, Fintype.card_fin]; ring
  exact_mod_cast hRat'

/-- The same fixed-core estimate is available per source tile, which is
needed when bounding the error delivered to one receiver rather than summing
over all receivers. -/
theorem one_tile_exact_rank_count_distance_le_448
    {ports : Nat}
    (sourceHeight : Col -> Nat) (boundary : Nat -> Nat) (H : Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = 64 * 4096)
    (hmono : forall i, boundary i <= boundary (i + 1))
    (hH : H <= 64 * 4096)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c)
    (hinput : forall c, sourceHeight c <= 4096) :
    (Finset.univ.sum fun p : Fin ports =>
      Chvatal.D2RankAlignment.countDistance
        (exactRankPortActualCount
          (fun c => fullHeightTwoShuffle (sourceHeight) c) boundary p)
        (exactRankPortTargetCount boundary H p)) <= 448 := by
  have hCore := fullHeightTwoShuffle_exact_rank_port_l1_le_448
    sourceHeight boundary ports H hzero hend hmono hH hHsum hinput
  have hEq :
      (Finset.univ.sum fun p : Fin ports =>
        (Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle sourceHeight c) boundary p)
          (exactRankPortTargetCount boundary H p) : Rat)) =
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortError
            (fun c => fullHeightTwoShuffle sourceHeight c) boundary H p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [rat_countDistance_eq_abs]
    simp [exactRankPortError, exactRankPortActualCount,
      exactRankPortTargetCount, Nat.cast_sum]
  have hRat :
      (Finset.univ.sum fun p : Fin ports =>
        (Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle sourceHeight c) boundary p)
          (exactRankPortTargetCount boundary H p) : Rat)) <= 448 := by
    rw [hEq]
    exact hCore
  exact_mod_cast hRat

/-- A fixed-core transfer has a uniform per-receiver seam bound when each
source tile has bounded parent mass error and each receiver receives only a
bounded number of refined source tile-port cells. The local 448 estimate is
paid once per such cell, not once per global tile. -/
theorem tiled_receiver_rank_error_le_fiber_bound
    {tiles ports : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (outputCell : Prod (Fin tiles) (Fin ports) -> J)
    (fiberCap parentBound : Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, tileMass t <= 64 * 4096)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096)
    (hparent : forall t,
      Chvatal.D2RankAlignment.countDistance (tileMass t) (idealTileMass t) <=
        parentBound)
    (hfiber : forall j : J,
      (Finset.univ.filter fun x : Prod (Fin tiles) (Fin ports) => outputCell x = j).card <=
        fiberCap) :
    forall j : J,
      Chvatal.D2RankAlignment.countDistance
        (∑ x ∈ Finset.univ.filter (fun x : Prod (Fin tiles) (Fin ports) => outputCell x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (boundary x.1) x.2)
        (∑ x ∈ Finset.univ.filter (fun x : Prod (Fin tiles) (Fin ports) => outputCell x = j),
          exactRankPortTargetCount (boundary x.1)
            (idealTileMass x.1) x.2) <= fiberCap * (parentBound + 448) := by
  let actual : Prod (Fin tiles) (Fin ports) -> Nat := fun x =>
    exactRankPortActualCount
      (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
      (boundary x.1) x.2
  let reference : Prod (Fin tiles) (Fin ports) -> Nat := fun x =>
    exactRankPortTargetCount (boundary x.1) (tileMass x.1) x.2
  let ideal : Prod (Fin tiles) (Fin ports) -> Nat := fun x =>
    exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) x.2
  have hcell : forall x, Chvatal.D2RankAlignment.countDistance (actual x) (ideal x) <= parentBound + 448 := by
    intro x
    have hlocal := one_tile_exact_rank_count_distance_le_448
      (sourceHeight x.1) (boundary x.1) (tileMass x.1)
      (hzero x.1) (hend x.1) (hmono x.1) (hH x.1)
      (hHsum x.1) (hinput x.1)
    have hlocalCell :
        Chvatal.D2RankAlignment.countDistance (actual x) (reference x) <= 448 := by
      calc
        Chvatal.D2RankAlignment.countDistance (actual x) (reference x) <=
            Finset.univ.sum fun p : Fin ports =>
              Chvatal.D2RankAlignment.countDistance
                (exactRankPortActualCount
                  (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
                  (boundary x.1) p)
                (exactRankPortTargetCount (boundary x.1) (tileMass x.1) p) := by
          exact Finset.single_le_sum (f := fun p : Fin ports =>
            Chvatal.D2RankAlignment.countDistance
              (exactRankPortActualCount
                (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
                (boundary x.1) p)
              (exactRankPortTargetCount (boundary x.1) (tileMass x.1) p))
            (fun p hp => Nat.zero_le _) (Finset.mem_univ x.2)
        _ <= 448 := hlocal
    have hparentPorts :
        (Finset.univ.sum fun p : Fin ports =>
          Chvatal.D2RankAlignment.countDistance
            (exactRankPortTargetCount (boundary x.1) (tileMass x.1) p)
            (exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) p)) <=
          parentBound := by
      change (Finset.univ.sum fun p : Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (Chvatal.D2RankAlignment.prefixIntervalMass (tileMass x.1)
            (boundary x.1 p.val) (boundary x.1 (p.val + 1)))
          (Chvatal.D2RankAlignment.prefixIntervalMass (idealTileMass x.1)
            (boundary x.1 p.val) (boundary x.1 (p.val + 1)))) <= parentBound
      rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
        Chvatal.D2RankAlignment.countDistance
          (Chvatal.D2RankAlignment.prefixIntervalMass (tileMass x.1)
            (boundary x.1 i) (boundary x.1 (i + 1)))
          (Chvatal.D2RankAlignment.prefixIntervalMass (idealTileMass x.1)
            (boundary x.1 i) (boundary x.1 (i + 1))))]
      have hpart := Chvatal.D2RankAlignment.prefixIntervalMass_partition_distance
        (tileMass x.1) (idealTileMass x.1) (boundary x.1) ports (64 * 4096)
        (hzero x.1) (hend x.1) (fun i hi => hmono x.1 i)
      simpa [exactRankPortTargetCount] using le_trans hpart (hparent x.1)
    have hparentCell :
        Chvatal.D2RankAlignment.countDistance (reference x) (ideal x) <= parentBound := by
      calc
        Chvatal.D2RankAlignment.countDistance (reference x) (ideal x) <=
            Finset.univ.sum fun p : Fin ports =>
              Chvatal.D2RankAlignment.countDistance
                (exactRankPortTargetCount (boundary x.1) (tileMass x.1) p)
                (exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) p) := by
          exact Finset.single_le_sum (f := fun p : Fin ports =>
            Chvatal.D2RankAlignment.countDistance
              (exactRankPortTargetCount (boundary x.1) (tileMass x.1) p)
              (exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) p))
            (fun p hp => Nat.zero_le _) (Finset.mem_univ x.2)
        _ <= parentBound := hparentPorts
    calc
      Chvatal.D2RankAlignment.countDistance (actual x) (ideal x) <=
          Chvatal.D2RankAlignment.countDistance (actual x) (reference x) +
            Chvatal.D2RankAlignment.countDistance (reference x) (ideal x) :=
        Chvatal.D2RankAlignment.countDistance_triangle _ _ _
      _ <= 448 + parentBound := Nat.add_le_add hlocalCell hparentCell
      _ = parentBound + 448 := Nat.add_comm _ _
  intro j
  simpa [actual, ideal] using
    (Chvatal.D2RankAlignment.grouped_countDistance_each_receiver_le_of_bounded_fiber
      outputCell actual ideal fiberCap (parentBound + 448) hcell hfiber j)

/-- A partition of each tile turns its total-count error into an aggregate
reference-port error, paying the parent's tilewise rank displacement once.
The tile masses here are the counts before local sorting; their errors are the
spatial alignment state that the global flow argument must control. -/
theorem tiled_reference_port_error_le_macro_parent_error
    {tiles ports : Nat}
    (boundary : Fin tiles -> Nat -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (parentError : Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hMacroParent :
      (Finset.univ.sum fun t : Fin tiles =>
        Chvatal.D2RankAlignment.countDistance
          (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (exactRankPortTargetCount (boundary t) (tileMass t) p)
          (exactRankPortTargetCount (boundary t) (idealTileMass t) p)) <=
      parentError := by
  calc
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (exactRankPortTargetCount (boundary t) (tileMass t) p)
          (exactRankPortTargetCount (boundary t) (idealTileMass t) p)) <=
      Finset.univ.sum fun t : Fin tiles =>
        Chvatal.D2RankAlignment.countDistance
          (tileMass t) (idealTileMass t) := by
        apply Finset.sum_le_sum
        intro t ht
        change (Finset.univ.sum fun p : Fin ports =>
          Chvatal.D2RankAlignment.countDistance
            (Chvatal.D2RankAlignment.prefixIntervalMass (tileMass t)
              (boundary t p.val) (boundary t (p.val + 1)))
            (Chvatal.D2RankAlignment.prefixIntervalMass (idealTileMass t)
              (boundary t p.val) (boundary t (p.val + 1)))) <= _
        rw [Fin.sum_univ_eq_sum_range (fun p =>
          Chvatal.D2RankAlignment.countDistance
            (Chvatal.D2RankAlignment.prefixIntervalMass (tileMass t)
              (boundary t p) (boundary t (p + 1)))
            (Chvatal.D2RankAlignment.prefixIntervalMass (idealTileMass t)
              (boundary t p) (boundary t (p + 1))))]
        exact Chvatal.D2RankAlignment.prefixIntervalMass_partition_distance
          (tileMass t) (idealTileMass t) (boundary t) ports (64 * 4096)
          (hzero t) (hend t) (by
            intro i hi
            exact hmono t i)
    _ <= parentError := hMacroParent

/-- The exact-rank error after local sorting a tiled sender is bounded by its
parent's tile-count misalignment plus448 per tile. This is the composable
one-stage contract: if parent error is at most capacity/512, then the local
error also fits the same budget before the D2 doubling of child capacity. -/
theorem tiled_global_rank_error_le_parent_add_448_per_tile
    {tiles ports : Nat}
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (parentError : Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, tileMass t <= 64 * 4096)
    (hHsum : forall t,
      tileMass t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096)
    (hMacroParent :
      (Finset.univ.sum fun t : Fin tiles =>
        Chvatal.D2RankAlignment.countDistance
          (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) p)
          (exactRankPortTargetCount (boundary t) (idealTileMass t) p)) <=
      parentError + 448 * tiles := by
  let actual : Fin tiles -> Fin ports -> Nat := fun t p =>
    exactRankPortActualCount
      (fun c => fullHeightTwoShuffle (sourceHeight t) c) (boundary t) p
  let reference : Fin tiles -> Fin ports -> Nat := fun t p =>
    exactRankPortTargetCount (boundary t) (tileMass t) p
  let ideal : Fin tiles -> Fin ports -> Nat := fun t p =>
    exactRankPortTargetCount (boundary t) (idealTileMass t) p
  let transfer : Fin tiles -> Fin ports -> Nat := fun t p =>
    Chvatal.D2RankAlignment.countDistance (actual t p) (reference t p)
  have hParent := tiled_reference_port_error_le_macro_parent_error
    boundary tileMass idealTileMass parentError hzero hend hmono hMacroParent
  have hTransfer := tiled_exact_rank_count_distance_le_448_mul_tiles
    sourceHeight boundary tileMass hzero hend hmono hH hHsum hinput
  have hUpper : forall t p, actual t p <= reference t p + transfer t p := by
    intro t p
    simp [actual, reference, transfer,
      Chvatal.D2RankAlignment.countDistance]
    omega
  have hLower : forall t p, reference t p <= actual t p + transfer t p := by
    intro t p
    simp [actual, reference, transfer,
      Chvatal.D2RankAlignment.countDistance]
    omega
  have hParentProd :
      (Finset.univ.sum fun x : Fin tiles × Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (reference x.1 x.2) (ideal x.1 x.2)) <= parentError := by
    rw [Fintype.sum_prod_type'
      (fun t p => Chvatal.D2RankAlignment.countDistance
        (reference t p) (ideal t p))]
    simpa [reference, ideal] using hParent
  have hTransferProd :
      (Finset.univ.sum fun x : Fin tiles × Fin ports =>
        transfer x.1 x.2) <= 448 * tiles := by
    rw [Fintype.sum_prod_type'
      (fun t p => transfer t p)]
    simpa [transfer, actual, reference] using hTransfer
  have hUpperProd : forall x : Fin tiles × Fin ports,
      actual x.1 x.2 <= reference x.1 x.2 + transfer x.1 x.2 := by
    intro x
    exact hUpper x.1 x.2
  have hLowerProd : forall x : Fin tiles × Fin ports,
      reference x.1 x.2 <= actual x.1 x.2 + transfer x.1 x.2 := by
    intro x
    exact hLower x.1 x.2
  have hAggregate := Chvatal.D2RankAlignment.aggregate_child_count_error_le_parent_add_transfer
    (fun x : Fin tiles × Fin ports => actual x.1 x.2)
    (fun x => reference x.1 x.2)
    (fun x => ideal x.1 x.2)
    (fun x => transfer x.1 x.2)
    parentError hUpperProd hLowerProd hParentProd
  have hAggregate' :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          Chvatal.D2RankAlignment.countDistance
            (actual t p) (ideal t p)) <= parentError + 448 * tiles := by
    rw [← Fintype.sum_prod_type'
      (fun t p => Chvatal.D2RankAlignment.countDistance
        (actual t p) (ideal t p))]
    calc
      (Finset.univ.sum fun x : Fin tiles × Fin ports =>
        Chvatal.D2RankAlignment.countDistance
          (actual x.1 x.2) (ideal x.1 x.2)) <=
        parentError +
          Finset.univ.sum fun x : Fin tiles × Fin ports => transfer x.1 x.2 :=
            hAggregate
      _ <= parentError + 448 * tiles := Nat.add_le_add_left hTransferProd parentError
  simpa [actual, ideal] using hAggregate'

/-- If the parent tile-mass profile already has l1 error at most1/512 of
capacity, then after the D2 capacity doubling the fixed core contracts the
normalized allowance by15/16: the parent allowance is512 keys per tile, the
core contributes448, and the doubled child capacity is twice262144 keys per
tile. This is the one-stage contraction interface sought by the rank
recurrence, conditional on the parent's tile-mass invariant. -/
theorem tiled_global_rank_error_preserves_doubled_budget
    {tiles ports : Nat}
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, tileMass t <= 64 * 4096)
    (hHsum : forall t,
      tileMass t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096)
    (hTiles : 0 < tiles)
    (hMacroParent :
      (Finset.univ.sum fun t : Fin tiles =>
        Chvatal.D2RankAlignment.countDistance
          (tileMass t) (idealTileMass t)) <= 512 * tiles) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        (Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) p)
          (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat) /
          (2 * (262144 * tiles : Rat))) <= (15 : Rat) / 8192 := by
  have hError := tiled_global_rank_error_le_parent_add_448_per_tile
    sourceHeight boundary tileMass idealTileMass (512 * tiles)
    hzero hend hmono hH hHsum hinput hMacroParent
  have hErrorRat :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          (Chvatal.D2RankAlignment.countDistance
            (exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)
            (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat)) <=
        (512 * tiles + 448 * tiles : Nat) := by
    exact_mod_cast hError
  have hErrorRat' :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          (Chvatal.D2RankAlignment.countDistance
            (exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)
            (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat)) <=
        960 * (tiles : Rat) := by
    calc
      _ <= ((512 * tiles + 448 * tiles : Nat) : Rat) := hErrorRat
      _ = 960 * (tiles : Rat) := by norm_num; ring
  have hden : 0 < 2 * (262144 * (tiles : Rat)) := by
    exact mul_pos (by norm_num) (mul_pos (by norm_num) (by exact_mod_cast hTiles))
  calc
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        (Chvatal.D2RankAlignment.countDistance
          (exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight t) c)
            (boundary t) p)
          (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat) /
            (2 * (262144 * tiles : Rat))) =
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          (Chvatal.D2RankAlignment.countDistance
            (exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)
            (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat)) /
        (2 * (262144 * tiles : Rat)) := by
          simp only [div_eq_mul_inv]
          let f : Fin tiles -> Fin ports -> Rat := fun t p =>
            (Chvatal.D2RankAlignment.countDistance
              (exactRankPortActualCount
                (fun c => fullHeightTwoShuffle (sourceHeight t) c)
                (boundary t) p)
              (exactRankPortTargetCount (boundary t) (idealTileMass t) p) : Rat)
          let invDen : Rat := (2 * (262144 * (tiles : Rat)))⁻¹
          change (Finset.univ.sum fun t : Fin tiles =>
            Finset.univ.sum fun p : Fin ports => f t p * invDen) =
            (Finset.univ.sum fun t : Fin tiles =>
              Finset.univ.sum fun p : Fin ports => f t p) * invDen
          calc
            (Finset.univ.sum fun t : Fin tiles =>
              Finset.univ.sum fun p : Fin ports => f t p * invDen) =
              Finset.univ.sum fun t : Fin tiles =>
                (Finset.univ.sum fun p : Fin ports => f t p) * invDen := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  exact (Finset.sum_mul Finset.univ (fun p : Fin ports => f t p) invDen).symm
            _ = (Finset.univ.sum fun t : Fin tiles =>
              Finset.univ.sum fun p : Fin ports => f t p) * invDen :=
                (Finset.sum_mul Finset.univ
                  (fun t : Fin tiles => Finset.univ.sum fun p : Fin ports => f t p)
                  invDen).symm
    _ <= (15 : Rat) / 8192 := by
      apply (div_le_iff₀ hden).2
      nlinarith [hErrorRat']

/-- The one-tile rank-transfer estimate composes additively over complete
4096-by-64 tiles. Each tile is compared with its own exact rank split; this
does not identify the collection of tile references with a single global
sender rank split. -/
theorem tiled_exact_rank_port_l1_le_448_mul_tiles
    {tiles ports : Nat}
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (H : Fin tiles -> Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, H t <= 64 * 4096)
    (hHsum : forall t,
      H t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        exactRankPortError (fun c => fullHeightTwoShuffle (sourceHeight t) c)
          (boundary t) (H t) p) <= 448 * tiles := by
  calc
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun p : Fin ports =>
        exactRankPortError (fun c => fullHeightTwoShuffle (sourceHeight t) c)
          (boundary t) (H t) p) <=
      Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
        apply Finset.sum_le_sum
        intro t ht
        exact fullHeightTwoShuffle_exact_rank_port_l1_le_448
          (sourceHeight t) (boundary t) ports (H t)
          (hzero t) (hend t) (hmono t) (hH t) (hHsum t) (hinput t)
    _ = 448 * tiles := by simp [Finset.sum_const, Fintype.card_fin]; ring

/-- Tilewise conservation makes positive and negative local port leakage each
at most224 per tile, so the scaled error fits the D2 capacity/512 reserve for
the complete tiled sender. The rank target is still tile-local here. -/
theorem tiled_directional_leakage_fits_d2_cap
    {tiles ports : Nat}
    (sourceHeight : Fin tiles -> Col -> Nat)
    (boundary : Fin tiles -> Nat -> Nat)
    (H : Fin tiles -> Nat)
    (hzero : forall t, boundary t 0 = 0)
    (hend : forall t, boundary t ports = 64 * 4096)
    (hmono : forall t i, boundary t i <= boundary t (i + 1))
    (hH : forall t, H t <= 64 * 4096)
    (hHsum : forall t,
      H t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= 4096) :
    512 * (8192 *
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p -
            exactRankPortTargetCount (boundary t) (H t) p)) <=
      8192 * (262144 * tiles) /\
    512 * (8192 *
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortTargetCount (boundary t) (H t) p -
            exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p)) <=
      8192 * (262144 * tiles) := by
  have hlocal (t : Fin tiles) :=
    fullHeightTwoShuffle_directional_leakage_le_224
      (sourceHeight t) (boundary t) ports (H t)
      (hzero t) (hend t) (hmono t) (hH t) (hHsum t) (hinput t)
  have hforward :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p -
            exactRankPortTargetCount (boundary t) (H t) p) <= 224 * tiles := by
    calc
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p -
            exactRankPortTargetCount (boundary t) (H t) p) <=
        Finset.univ.sum fun _ : Fin tiles => (224 : Nat) := by
          apply Finset.sum_le_sum
          intro t ht
          exact (hlocal t).1
      _ = 224 * tiles := by simp; omega
  have hbackward :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortTargetCount (boundary t) (H t) p -
            exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p) <= 224 * tiles := by
    calc
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun p : Fin ports =>
          exactRankPortTargetCount (boundary t) (H t) p -
            exactRankPortActualCount
              (fun c => fullHeightTwoShuffle (sourceHeight t) c)
              (boundary t) p) <=
        Finset.univ.sum fun _ : Fin tiles => (224 : Nat) := by
          apply Finset.sum_le_sum
          intro t ht
          exact (hlocal t).2
      _ = 224 * tiles := by simp; omega
  constructor
  · exact scaled_directional_mismatch_fits_d2_deficit_cap tiles _ hforward
  · exact scaled_directional_mismatch_fits_d2_deficit_cap tiles _ hbackward

end Chvatal.D2Slope25TiledBridge
