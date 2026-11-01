import D2ClippedFlowProfileTransfer
import D2ClippedTilePrefixAllocation
import D2FlowRankBridge

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

/-- If a tag selects exactly one port uniformly in every tile and column,
its grouped ideal mass is just that port's all-tile/all-column mass. -/
theorem clippedFlowGroupedRank_eq_uniform_port
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (bounds : Fin (ports + 1) -> Nat) (idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) (p : Fin ports)
    (htag : forall t c q, tag t (c, q) = j <-> q = p) :
    clippedFlowGroupedRank 4096 bounds idealTileMass tag j =
      Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun c : Col =>
          clippedFlowProfileRankCount 4096 bounds idealTileMass t (c, p) := by
  classical
  let source := Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j
  have hsum := Finset.sum_bij
    (fun x _ => (x.1, x.2.1))
    (s := source) (t := (Finset.univ : Finset (Fin tiles × Col)))
    (f := fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
      clippedFlowProfileRankCount 4096 bounds idealTileMass x.1 x.2)
    (g := fun y : Fin tiles × Col =>
      clippedFlowProfileRankCount 4096 bounds idealTileMass y.1 (y.2, p))
    ?_ ?_ ?_ ?_
  · simpa [clippedFlowGroupedRank, source, Fintype.sum_prod_type] using hsum
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy heq
    obtain ⟨xt, ⟨xc, xp⟩⟩ := x
    obtain ⟨yt, ⟨yc, yp⟩⟩ := y
    have hxp : xp = p := (htag xt xc xp).1 (Finset.mem_filter.mp hx).2
    have hyp : yp = p := (htag yt yc yp).1 (Finset.mem_filter.mp hy).2
    simp_all
  · intro y hy
    obtain ⟨yt, yc⟩ := y
    exact ⟨(yt, (yc, p)),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (htag yt yc p).2 rfl⟩, rfl⟩
  · intro x hx
    obtain ⟨xt, ⟨xc, xp⟩⟩ := x
    have hxp : xp = p := (htag xt xc xp).1 (Finset.mem_filter.mp hx).2
    simp [hxp]

/- With the standard child rank boundaries and a tag constant on each child
port, grouped ideal mass equals the shifted global flow interval. The actual
scheduler still must justify the tag and boundary hypotheses. -/
theorem clippedFlowGroupedRank_eq_shifted_child_interval
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (bounds : Fin (ports + 1) -> Nat) (idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (label : Fin 8 -> J)
    (port : Fin 8 -> Fin ports) (sizes : Fin 8 -> Nat)
    (G offset : Nat) (j : Fin 8)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 262144 * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hMass : forall t : Fin tiles,
      idealTileMass t = prefixIntervalMass G (t.val * 262144)
        ((t.val + 1) * 262144))
    (htag : forall t c q, tag t (c, q) = label j <-> q = port j)
    (hlo : bounds (Fin.castSucc (port j)) =
      offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes j.val)
    (hhi : bounds (Fin.succ (port j)) =
      offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes (j.val + 1))
    (hb : offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes (j.val + 1) <=
      tiles * 262144)
    (htiles : 0 < tiles) :
    clippedFlowGroupedRank 4096 bounds idealTileMass tag (label j) =
      prefixIntervalMass G
        (offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes j.val)
        (offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes (j.val + 1)) := by
  have hab : offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes j.val <=
      offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes (j.val + 1) := by
    exact Nat.add_le_add_left
      (Chvatal.D2Reserve.d2FlowRankBoundary_mono sizes j.val j.isLt) offset
  rw [clippedFlowGroupedRank_eq_uniform_port bounds idealTileMass tag
    (label j) (port j) htag]
  exact clippedFlowProfileRankCount_sum_tiles_columns bounds idealTileMass G
    (offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes j.val)
    (offset + Chvatal.D2Reserve.d2FlowRankBoundary sizes (j.val + 1))
    (port j) hfirst hlast hmono hlo hhi hab hb htiles hMass

end Chvatal.D2ClippedTilePortAggregation
