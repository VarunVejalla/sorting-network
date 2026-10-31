import D2Slope25RebatchBridge

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

open scoped BigOperators
open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25RowMajorBridge

namespace Chvatal.D2ClippedFlowRankTransfer

/-- The valid finite index obtained by clipping a natural rank boundary to
its range. -/
def clippedFlowIndex {ports : Nat} (i : Nat) : Fin (ports + 1) :=
  Fin.mk (min i ports) (by omega)

/-- Clip one global D2 rank boundary to the local rank interval of a tile.
All nonfinal ports keep their exact intersection; the final port is extended
through the all-one padding rows to a full core tile. -/
def clippedFlowTileBoundary {ports tiles : Nat} (m : Nat)
    (globalBounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (i : Nat) : Nat :=
  if i < ports then
    min (64 * m) (globalBounds (clippedFlowIndex i) - t.val * (64 * m))
  else 262144

theorem clippedFlowIndex_zero {ports : Nat} : clippedFlowIndex (ports := ports) 0 = 0 := by
  apply Fin.ext
  simp [clippedFlowIndex]

theorem clippedFlowIndex_end {ports : Nat} :
    clippedFlowIndex (ports := ports) ports = Fin.last ports := by
  apply Fin.ext
  simp [clippedFlowIndex]

theorem clippedFlowIndex_castSucc {ports : Nat} (i : Fin ports) :
    clippedFlowIndex (ports := ports) i.val = Fin.castSucc i := by
  apply Fin.ext
  simp [clippedFlowIndex, Nat.min_eq_left (Nat.le_of_lt i.isLt)]

theorem clippedFlowIndex_succ {ports : Nat} (i : Fin ports) :
    clippedFlowIndex (ports := ports) (i.val + 1) = Fin.succ i := by
  apply Fin.ext
  have hle : i.val + 1 <= ports := Nat.succ_le_of_lt i.isLt
  simp [clippedFlowIndex, Nat.min_eq_left hle]

theorem clippedFlowIndex_val {ports : Nat} (i : Fin (ports + 1)) :
    clippedFlowIndex i.val = i := by
  apply Fin.ext
  have hle : i.val <= ports := by omega
  simp [clippedFlowIndex, Nat.min_eq_left hle]

/-- Every tile sees a valid complete 4096-row port partition after padding. -/
theorem clippedFlowTileBoundary_valid {ports tiles : Nat} (m : Nat)
    (globalBounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : globalBounds 0 = 0)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      globalBounds (Fin.castSucc i) <= globalBounds (Fin.succ i)) :
    clippedFlowTileBoundary m globalBounds t 0 = 0 ∧
    clippedFlowTileBoundary m globalBounds t ports = 262144 ∧
    (forall i, clippedFlowTileBoundary m globalBounds t i <=
      clippedFlowTileBoundary m globalBounds t (i + 1)) := by
  apply And.intro
  case left =>
    unfold clippedFlowTileBoundary
    rw [if_pos hports, clippedFlowIndex_zero, hfirst]
    simp
  case right =>
    apply And.intro
    case left =>
      unfold clippedFlowTileBoundary
      rw [if_neg (Nat.lt_irrefl ports)]
    case right =>
      intro i
      by_cases hi : i < ports
      case pos =>
        by_cases hnext : i + 1 < ports
        case pos =>
          let fi : Fin ports := Fin.mk i hi
          have hglobal : globalBounds (clippedFlowIndex i) <=
              globalBounds (clippedFlowIndex (i + 1)) := by
            rw [clippedFlowIndex_castSucc fi, clippedFlowIndex_succ fi]
            exact hmono fi
          have hsub := Nat.sub_le_sub_right hglobal (t.val * (64 * m))
          have hclip := min_le_min_left (64 * m) hsub
          unfold clippedFlowTileBoundary
          rw [if_pos hi, if_pos hnext]
          exact hclip
        case neg =>
          have hlastPort : i + 1 = ports := by omega
          have hcap : 64 * m <= 262144 := by omega
          have hbound : clippedFlowTileBoundary m globalBounds t i <= 64 * m := by
            unfold clippedFlowTileBoundary
            rw [if_pos hi]
            exact Nat.min_le_left _ _
          have hnot : Not (i + 1 < ports) := by omega
          have hright : clippedFlowTileBoundary m globalBounds t (i + 1) = 262144 := by
            unfold clippedFlowTileBoundary
            rw [if_neg hnot]
          rw [hright]
          exact hbound.trans hcap
      case neg =>
        have hnext : Not (i + 1 < ports) := by omega
        unfold clippedFlowTileBoundary
        rw [if_neg hi, if_neg hnext]

/-- On the live `64*m` rows, clipping a global boundary to a tile is exactly
the global boundary translated by the tile's starting rank and clamped to the
live tile width. The padded final boundary therefore has the same live
intersection as the true global endpoint. -/
theorem clippedFlowTileBoundary_live {ports tiles : Nat} (m : Nat)
    (globalBounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (hm : m <= 4096)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (i : Fin (ports + 1)) :
    min (64 * m) (clippedFlowTileBoundary m globalBounds t i.val) =
      min (64 * m) (globalBounds i - t.val * (64 * m)) := by
  let W := 64 * m
  by_cases hi : i.val < ports
  · have hindex : clippedFlowIndex i.val = i := clippedFlowIndex_val i
    simp [clippedFlowTileBoundary, hi, hindex, W, Nat.min_assoc]
  · have hiend : i.val = ports := by omega
    have hifin : i = Fin.last ports := Fin.ext hiend
    subst i
    have hbound : globalBounds (Fin.last ports) = W * tiles := by
      simpa [W, Nat.mul_comm] using hlast
    have ht : t.val + 1 <= tiles := Nat.succ_le_of_lt t.isLt
    have hmul : (t.val + 1) * W <= tiles * W := Nat.mul_le_mul_right W ht
    have hmul' : t.val * W + W <= tiles * W := by
      simpa [Nat.add_mul] using hmul
    have hroom : t.val * W + W <= W * tiles := by
      calc
        t.val * W + W <= tiles * W := hmul'
        _ = W * tiles := Nat.mul_comm _ _
    have hsub : W <= W * tiles - t.val * W := by omega
    have hcap : W <= 262144 := by dsimp [W]; omega
    simp [clippedFlowTileBoundary, hiend, hbound, W,
      Nat.min_eq_left hcap, Nat.min_eq_left hsub]

def clippedFlowBoundaryFamily {ports tiles : Nat} (m : Nat)
    (globalBounds : Fin (ports + 1) -> Nat) : Fin tiles -> Nat -> Nat :=
  fun t i => clippedFlowTileBoundary m globalBounds t i

def clippedFlowOutputCell {ports tiles : Nat} {J : Type*}
    (tag : Fin tiles -> Fin ports -> J) : Prod (Fin tiles) (Fin ports) -> J :=
  fun x => tag x.1 x.2

/-- Apply the established parent-error plus 448-per-tile rank transfer to a
single global D2 rank partition. The clipped boundaries are derived from that
partition, rather than supplied independently for each tile. -/
theorem clipped_global_flow_rank_transfer
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (globalBounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (parentError : Nat) (tag : Fin tiles -> Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : globalBounds 0 = 0)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      globalBounds (Fin.castSucc i) <= globalBounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= m)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      Chvatal.D2RankAlignment.countDistance (tileMass t) (idealTileMass t)) <=
        parentError) :
    (Finset.univ.sum fun j : J =>
      Chvatal.D2RankAlignment.countDistance
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) => clippedFlowOutputCell tag x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (clippedFlowBoundaryFamily m globalBounds x.1) x.2)
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) => clippedFlowOutputCell tag x = j),
          exactRankPortTargetCount
            (clippedFlowBoundaryFamily m globalBounds x.1)
            (idealTileMass x.1) x.2)) <= parentError + 448 * tiles := by
  let boundary : Fin tiles -> Nat -> Nat :=
    clippedFlowBoundaryFamily m globalBounds
  have hzero : forall t, boundary t 0 = 0 := by
    intro t
    exact (clippedFlowTileBoundary_valid m globalBounds t hports hm
      hfirst hlast hmono).1
  have hend : forall t, boundary t ports = 64 * 4096 := by
    intro t
    have h := (clippedFlowTileBoundary_valid m globalBounds t hports hm
      hfirst hlast hmono).2.1
    simpa [boundary] using h
  have hboundaryMono : forall t i,
      boundary t i <= boundary t (i + 1) := by
    intro t i
    exact (clippedFlowTileBoundary_valid m globalBounds t hports hm
      hfirst hlast hmono).2.2 i
  have hcore := Chvatal.D2Slope25RebatchBridge.rebinned_tiled_rank_error_le_parent_add_448_per_tile
    sourceHeight boundary tileMass idealTileMass (clippedFlowOutputCell tag) parentError
    hzero hend hboundaryMono hH hHsum (fun t c => (hinput t c).trans hm)
    hMacroParent
  simpa [boundary, clippedFlowBoundaryFamily] using hcore

/-- A clipped global partition preserves the normalized rank-error budget
when the schedule doubles the tile count. This packages the parent-mass
correction and the fixed-core 448 allowance into the one-step invariant
needed by an all-depth argument. -/
theorem clipped_global_flow_rank_error_preserves_doubled_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (globalBounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : globalBounds 0 = 0)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      globalBounds (Fin.castSucc i) <= globalBounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= m)
    (hTiles : 0 < tiles)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      Chvatal.D2RankAlignment.countDistance (tileMass t) (idealTileMass t)) <=
        512 * tiles) :
    ((∑ j : J,
      Chvatal.D2RankAlignment.countDistance
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (clippedFlowBoundaryFamily m globalBounds x.1) x.2)
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortTargetCount
            (clippedFlowBoundaryFamily m globalBounds x.1)
            (idealTileMass x.1) x.2) : Rat) /
      (262144 * (outputTiles : Rat))) <= (15 : Rat) / 8192 := by
  have hvalid (t : Fin tiles) :=
    clippedFlowTileBoundary_valid m globalBounds t hports hm hfirst hlast hmono
  have hzero : forall t : Fin tiles,
      clippedFlowBoundaryFamily m globalBounds t 0 = 0 :=
    fun t => (hvalid t).1
  have hend : forall t : Fin tiles,
      clippedFlowBoundaryFamily m globalBounds t ports = 64 * 4096 := by
    intro t
    simpa [clippedFlowBoundaryFamily] using (hvalid t).2.1
  have hboundaryMono : forall (t : Fin tiles) (i : Nat),
      clippedFlowBoundaryFamily m globalBounds t i <=
        clippedFlowBoundaryFamily m globalBounds t (i + 1) := by
    intro t i
    exact (hvalid t).2.2 i
  have hcore := Chvatal.D2Slope25RebatchBridge.rebinned_tiled_rank_error_preserves_doubled_budget
      sourceHeight (clippedFlowBoundaryFamily m globalBounds)
      tileMass idealTileMass (clippedFlowOutputCell tag)
      hzero hend hboundaryMono hH hHsum
      (fun t c => (hinput t c).trans hm) hTiles hOutputTiles hMacroParent
  simpa [clippedFlowBoundaryFamily] using hcore

/-- Natural-number form of the doubled-budget induction step: parent error
at most 512 per tile plus the fresh 448-per-tile core error fits within the
512-per-output-tile budget after doubling. -/
theorem clipped_global_flow_rank_error_le_next_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (globalBounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : globalBounds 0 = 0)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      globalBounds (Fin.castSucc i) <= globalBounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= m)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      Chvatal.D2RankAlignment.countDistance (tileMass t) (idealTileMass t)) <=
        512 * tiles) :
    ∑ j : J,
      Chvatal.D2RankAlignment.countDistance
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (clippedFlowBoundaryFamily m globalBounds x.1) x.2)
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortTargetCount
            (clippedFlowBoundaryFamily m globalBounds x.1)
            (idealTileMass x.1) x.2) <= 512 * outputTiles := by
  have hlocal := clipped_global_flow_rank_transfer
    m globalBounds sourceHeight tileMass idealTileMass (512 * tiles) tag
    hports hm hfirst hlast hmono hH hHsum hinput hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 512 * tiles + 448 * tiles := hlocal
    _ <= 512 * tiles + 512 * tiles := by omega
    _ = 512 * (2 * tiles) := by ring

/-- The 448-per-tile rank-error allowance is itself a fixed point of the
clipped transfer: parent error `448 * tiles` plus the fresh `448 * tiles`
local-core error fits exactly in `448` per output tile when the tile count
doubles. This is the sharp closed recurrence supported by the local provider.
-/
theorem clipped_global_flow_rank_error_preserves_448_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (globalBounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : globalBounds 0 = 0)
    (hlast : globalBounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      globalBounds (Fin.castSucc i) <= globalBounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hinput : forall t c, sourceHeight t c <= m)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      Chvatal.D2RankAlignment.countDistance (tileMass t) (idealTileMass t)) <=
        448 * tiles) :
    ∑ j : J,
      Chvatal.D2RankAlignment.countDistance
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortActualCount
            (fun c => fullHeightTwoShuffle (sourceHeight x.1) c)
            (clippedFlowBoundaryFamily m globalBounds x.1) x.2)
        (∑ x ∈ Finset.univ.filter
          (fun x : Prod (Fin tiles) (Fin ports) =>
            clippedFlowOutputCell tag x = j),
          exactRankPortTargetCount
            (clippedFlowBoundaryFamily m globalBounds x.1)
            (idealTileMass x.1) x.2) <= 448 * outputTiles := by
  have hlocal := clipped_global_flow_rank_transfer
    m globalBounds sourceHeight tileMass idealTileMass (448 * tiles) tag
    hports hm hfirst hlast hmono hH hHsum hinput hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 448 * tiles + 448 * tiles := hlocal
    _ = 448 * (2 * tiles) := by ring

/-- Iterate the sharp one-stage accounting: if the number of rank tiles
doubles and each transition adds at most448 errors per old tile, an initial
448-per-tile error bound holds at every depth. -/
theorem doubled_rank_error_recurrence_le_448
    (tiles error : Nat → Nat)
    (hTstep : ∀ t, tiles (t + 1) = 2 * tiles t)
    (hE0 : error 0 ≤ 448 * tiles 0)
    (hEstep : ∀ t, error (t + 1) ≤ error t + 448 * tiles t) :
    ∀ t, error t ≤ 448 * tiles t := by
  intro t
  induction t with
  | zero => exact hE0
  | succ t ih =>
      rw [hTstep t]
      calc
        error (t + 1) ≤ error t + 448 * tiles t := hEstep t
        _ ≤ 448 * tiles t + 448 * tiles t := Nat.add_le_add_right ih _
        _ = 448 * (2 * tiles t) := by ring

end Chvatal.D2ClippedFlowRankTransfer
