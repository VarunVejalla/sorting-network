import D2ClippedFlowProfileTransfer
import D2ClippedTilePrefixAllocation

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Chvatal.D2ClippedTilePortAggregation

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2RowMajorFlowCuts
open Chvatal.D2RankAlignment

abbrev Col := Fin 64

/-- If each source tile receives the restriction of one global ideal prefix,
then its exact-rank cells over one port add back to that port's global prefix
mass. This is the all-tile/all-column identity needed before applying receiver
tags. -/
theorem clippedFlowProfileRankCount_sum_tiles_columns
    {ports tiles : Nat} (bounds : Fin (ports + 1) -> Nat)
    (idealTileMass : Fin tiles -> Nat) (G a b : Nat) (p : Fin ports)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 262144 * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hlo : bounds (Fin.castSucc p) = a)
    (hhi : bounds (Fin.succ p) = b)
    (hab : a <= b) (hb : b <= tiles * 262144) (htiles : 0 < tiles)
    (hMass : forall t : Fin tiles,
      idealTileMass t = prefixIntervalMass G (t.val * 262144)
        ((t.val + 1) * 262144)) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun c : Col =>
        clippedFlowProfileRankCount 4096 bounds idealTileMass t (c, p)) =
      prefixIntervalMass G a b := by
  let tileOf (t : Nat) : Fin tiles := ⟨t % tiles, Nat.mod_lt _ htiles⟩
  let f (t : Fin tiles) := Finset.univ.sum fun c : Col =>
    clippedFlowProfileRankCount 4096 bounds idealTileMass t (c, p)
  have hreplace : (Finset.univ.sum fun t : Fin tiles => f t) =
      Finset.univ.sum fun t : Fin tiles => f (tileOf t.val) := by
    apply Finset.sum_congr rfl
    intro t ht
    congr 1
    apply Fin.ext
    simp [tileOf, Nat.mod_eq_of_lt t.isLt]
  rw [hreplace, Fin.sum_univ_eq_sum_range (fun t : Nat => f (tileOf t)) tiles]
  calc
    (Finset.sum (Finset.range tiles) fun t => f (tileOf t)) =
      Finset.sum (Finset.range tiles) fun t =>
        prefixIntervalMass
          (prefixIntervalMass G (t * 262144) ((t + 1) * 262144))
          (min 262144 (a - t * 262144))
          (min 262144 (b - t * 262144)) := by
        apply Finset.sum_congr rfl
        intro t ht
        let tile : Fin tiles := ⟨t, Finset.mem_range.mp ht⟩
        have hcols := clippedFlowProfileRankCount_sum_columns bounds
          idealTileMass tile p hfirst hlast hmono (by
            rw [hMass]
            unfold prefixIntervalMass
            calc
              _ <= ((tile.val + 1) * 262144 - tile.val * 262144) :=
                Nat.min_le_right _ _
              _ = 262144 := by omega)
        have htile : tileOf t = tile := by
          apply Fin.ext
          simp [tileOf, tile, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
        simpa [f, tile, htile, clippedTileFlowBounds, hlo, hhi, hMass] using hcols
    _ = prefixIntervalMass G a b := by
      simpa using
        Chvatal.D2ClippedTilePrefixAllocation.prefixIntervalMass_tiled_interval_sum
          G a b 262144 tiles hab hb

end Chvatal.D2ClippedTilePortAggregation
