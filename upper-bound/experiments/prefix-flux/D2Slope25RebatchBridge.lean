import D2Slope25TiledBridge
import D2RankRebatch

set_option maxHeartbeats 500000

open scoped BigOperators
open Chvatal.D2Slope25RowMajorBridge
open Chvatal.D2Slope25TiledBridge
open Chvatal.D2RankAlignment

namespace Chvatal.D2Slope25RebatchBridge

abbrev Col := Fin 64

/-- The fixed-core local contract survives arbitrary regrouping of its
tile-port cells into output profile cells. The output index may include both
tile and column. When ports are split at every partial-offset boundary, this
theorem charges each incoming parent mismatch once and each local core error
once. Proving that the real D2 routing induces this map and these cell counts
remains a schedule bridge obligation. -/
theorem rebinned_tiled_rank_error_le_parent_add_448_per_tile
    {tiles ports : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Fin tiles → Col → Nat)
    (boundary : Fin tiles → Nat → Nat)
    (tileMass idealTileMass : Fin tiles → Nat)
    (outputCell : Fin tiles × Fin ports → J)
    (parentError : Nat)
    (hzero : ∀ t, boundary t 0 = 0)
    (hend : ∀ t, boundary t ports = 64 * 4096)
    (hmono : ∀ t i, boundary t i ≤ boundary t (i + 1))
    (hH : ∀ t, tileMass t ≤ 64 * 4096)
    (hHsum : ∀ t,
      tileMass t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : ∀ t c, sourceHeight t c ≤ 4096)
    (hMacroParent :
      (Finset.univ.sum fun t : Fin tiles =>
        countDistance (tileMass t) (idealTileMass t)) ≤ parentError) :
    (∑ j : J,
      countDistance
        (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
          outputCell x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (boundary x.1) x.2)
        (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
          outputCell x = j),
          exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) x.2)) ≤
      parentError + 448 * tiles := by
  let actualCell : Fin tiles × Fin ports → Nat := fun x =>
    exactRankPortActualCount
      (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
      (boundary x.1) x.2
  let idealCell : Fin tiles × Fin ports → Nat := fun x =>
    exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) x.2
  have hlocal := tiled_global_rank_error_le_parent_add_448_per_tile
    sourceHeight boundary tileMass idealTileMass parentError
    hzero hend hmono hH hHsum hinput hMacroParent
  have hlocalProduct :
      (∑ x : Fin tiles × Fin ports,
        countDistance (actualCell x) (idealCell x)) ≤
        parentError + 448 * tiles := by
    rw [Fintype.sum_prod_type' (fun t p =>
      countDistance (actualCell (t, p)) (idealCell (t, p)))]
    simpa [actualCell, idealCell] using hlocal
  calc
    _ ≤ ∑ x : Fin tiles × Fin ports,
        countDistance (actualCell x) (idealCell x) :=
      grouped_countDistance_le_refined_countDistance outputCell actualCell idealCell
    _ ≤ parentError + 448 * tiles := hlocalProduct

/-- If the explicit routing map doubles the number of output tiles, the
rebinned error contracts to at most 15/8192 of total output capacity. The
group type J is arbitrary; choosing Fin outputTiles × Col makes the state
the complete 64-column height profile, not just one scalar per tile. -/
theorem rebinned_tiled_rank_error_preserves_doubled_budget
    {tiles ports outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Fin tiles → Col → Nat)
    (boundary : Fin tiles → Nat → Nat)
    (tileMass idealTileMass : Fin tiles → Nat)
    (outputCell : Fin tiles × Fin ports → J)
    (hzero : ∀ t, boundary t 0 = 0)
    (hend : ∀ t, boundary t ports = 64 * 4096)
    (hmono : ∀ t i, boundary t i ≤ boundary t (i + 1))
    (hH : ∀ t, tileMass t ≤ 64 * 4096)
    (hHsum : ∀ t,
      tileMass t = Finset.univ.sum fun c : Col =>
        fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : ∀ t c, sourceHeight t c ≤ 4096)
    (hTiles : 0 < tiles)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent :
      (Finset.univ.sum fun t : Fin tiles =>
        countDistance (tileMass t) (idealTileMass t)) ≤ 512 * tiles) :
    ((∑ j : J,
      countDistance
        (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
          outputCell x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (boundary x.1) x.2)
        (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
          outputCell x = j),
          exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) x.2) : ℚ) /
      (262144 * (outputTiles : ℚ))) ≤ (15 : ℚ) / 8192 := by
  let actualCell : Fin tiles × Fin ports → Nat := fun x =>
    exactRankPortActualCount
      (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
      (boundary x.1) x.2
  let idealCell : Fin tiles × Fin ports → Nat := fun x =>
    exactRankPortTargetCount (boundary x.1) (idealTileMass x.1) x.2
  have hError := rebinned_tiled_rank_error_le_parent_add_448_per_tile
    sourceHeight boundary tileMass idealTileMass outputCell (512 * tiles)
    hzero hend hmono hH hHsum hinput hMacroParent
  have hErrorNat :
      (∑ j : J,
        countDistance
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), actualCell x)
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), idealCell x)) ≤ 960 * tiles := by
    calc
      _ ≤ 512 * tiles + 448 * tiles := hError
      _ = 960 * tiles := by ring
  have hErrorRat :
      (∑ j : J,
        (countDistance
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), actualCell x)
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), idealCell x) : ℚ)) ≤
        960 * (tiles : ℚ) := by
    exact_mod_cast hErrorNat
  have hden : 0 < 262144 * (outputTiles : ℚ) := by
    rw [hOutputTiles]
    positivity
  calc
    _ = (∑ j : J,
        (countDistance
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), actualCell x)
          (∑ x ∈ Finset.univ.filter (fun x : Fin tiles × Fin ports =>
            outputCell x = j), idealCell x) : ℚ)) /
        (262144 * (outputTiles : ℚ)) := by
      simp only [actualCell, idealCell]
    _ ≤ (960 * (tiles : ℚ)) / (262144 * (outputTiles : ℚ)) :=
      div_le_div_of_nonneg_right hErrorRat (le_of_lt hden)
    _ = (960 * (tiles : ℚ)) / (262144 * (2 * (tiles : ℚ))) := by
      rw [hOutputTiles]
      norm_num
    _ = (15 : ℚ) / 8192 := by
      have ht : (tiles : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hTiles)
      field_simp [ht]
      norm_num

end Chvatal.D2Slope25RebatchBridge
