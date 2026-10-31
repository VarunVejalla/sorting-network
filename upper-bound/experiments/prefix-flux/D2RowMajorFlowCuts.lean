import D2ColumnRebatchBridge
import AKS.Chvatal.ExecPlacement

set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

namespace Chvatal.D2RowMajorFlowCuts

open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2RankAlignment
open Chvatal.D2Slope25Physical

abbrev Col := Fin 64

def rowCutAtRank (x : Nat) (c : Col) : Nat :=
  min 4096 ((x + 63 - c.val) / 64)

theorem row_lt_rowCutAtRank_iff {x r : Nat} (c : Col) (hr : r < 4096) :
    r < rowCutAtRank x c <-> 64 * r + c.val < x := by
  have hc : c.val < 64 := c.isLt
  unfold rowCutAtRank
  omega

theorem rowCut_interval_flattened {lo hi r : Nat} (c : Col)
    (hr : r < 4096)
    (hrowlo : rowCutAtRank lo c <= r)
    (hrowhi : r < rowCutAtRank hi c) :
    lo <= 64 * r + c.val ∧ 64 * r + c.val < hi := by
  have hge : lo <= 64 * r + c.val := by
    by_contra hn
    have hlt : 64 * r + c.val < lo := by omega
    have hcut := (row_lt_rowCutAtRank_iff c hr).2 hlt
    omega
  have hlt := (row_lt_rowCutAtRank_iff c hr).1 hrowhi
  exact And.intro hge hlt

theorem rowCutAtRank_mono {x y : Nat} (c : Col) (hxy : x <= y) :
    rowCutAtRank x c <= rowCutAtRank y c := by
  unfold rowCutAtRank
  omega

def rowMajorFlowCuts {ports : Nat}
    (bounds : Fin (ports + 1) -> Nat) (c : Col) (i : Nat) : Nat :=
  rowCutAtRank (bounds (Fin.mk (min i ports) (by omega))) c

theorem rowMajorFlowCuts_valid {ports : Nat}
    (bounds : Fin (ports + 1) -> Nat)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 262144)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i)) :
    (forall c : Col, rowMajorFlowCuts bounds c 0 = 0) ∧
    (forall c : Col, rowMajorFlowCuts bounds c ports = 4096) ∧
    (forall c i, i < ports ->
      rowMajorFlowCuts bounds c i <= rowMajorFlowCuts bounds c (i + 1)) := by
  constructor
  intro c
  change rowCutAtRank (bounds 0) c = 0
  rw [hfirst]
  unfold rowCutAtRank
  have hc : c.val < 64 := c.isLt
  omega
  constructor
  intro c
  change rowCutAtRank
    (bounds (Fin.mk (min ports ports) (by omega))) c = 4096
  have hidx :
      (Fin.mk (min ports ports) (by omega) : Fin (ports + 1)) = Fin.last ports := by
    apply Fin.ext
    simp
  rw [hidx, hlast]
  unfold rowCutAtRank
  have hc : c.val < 64 := c.isLt
  omega
  intro c i hi
  have hleft : min i ports = i := Nat.min_eq_left (Nat.le_of_lt hi)
  have hright : min (i + 1) ports = i + 1 := Nat.min_eq_left (by omega)
  have hbound : bounds (Fin.mk i (by omega)) <=
      bounds (Fin.mk (i + 1) (by omega)) := by
    simpa [Fin.castSucc, Fin.succ] using hmono (Fin.mk i hi)
  have hcut := rowCutAtRank_mono c hbound
  simpa [rowMajorFlowCuts, hleft, hright] using hcut

theorem rowMajorFlowCuts_port_contained {ports : Nat}
    (bounds : Fin (ports + 1) -> Nat) (i : Fin ports) (c : Col)
    {r : Nat} (hr : r < 4096)
    (hmono : forall j : Fin ports,
      bounds (Fin.castSucc j) <= bounds (Fin.succ j))
    (hrowlo : rowMajorFlowCuts bounds c i.val <= r)
    (hrowhi : r < rowMajorFlowCuts bounds c (i.val + 1)) :
    bounds (Fin.castSucc i) <= 64 * r + c.val ∧
      64 * r + c.val < bounds (Fin.succ i) := by
  have hbound : bounds (Fin.castSucc i) <= bounds (Fin.succ i) := hmono i
  have h := rowCut_interval_flattened c hr
    (by simpa [rowMajorFlowCuts, Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hrowlo)
    (by simpa [rowMajorFlowCuts,
      Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)] using hrowhi)
  exact h

/-- The fixed-core 448 exact-rank error bound applies directly to any
monotone D2 rank partition of a complete row-major tile: rank boundaries are
converted to per-column cuts, and each column-port error is grouped by the
flow destination tag of its rank interval. -/
theorem rowMajorFlowCuts_rebinned_core_error_le_448
    {ports : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Col -> Nat) (H : Nat) (tag : Fin ports -> J)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 262144)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hinput : forall c, sourceHeight c <= 4096)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
        tag cell.2 = j).sum fun cell =>
          (prefixIntervalMass (fullHeightTwoShuffle sourceHeight cell.1)
            (rowMajorFlowCuts bounds cell.1 cell.2.val)
            (rowMajorFlowCuts bounds cell.1 (cell.2.val + 1)) : Rat) -
          prefixIntervalMass (exactRankColumnHeight H cell.1)
            (rowMajorFlowCuts bounds cell.1 cell.2.val)
            (rowMajorFlowCuts bounds cell.1 (cell.2.val + 1)))) <= 448 := by
  let cuts : Col -> Nat -> Nat := fun c i => rowMajorFlowCuts bounds c i
  have hvalid := rowMajorFlowCuts_valid bounds hfirst hlast hmono
  have hcore := Chvatal.D2ColumnRebatchBridge.fullHeightTwoShuffle_exact_rank_rebinned_l1_le_448
    sourceHeight cuts ports H (fun cell => tag cell.2)
    hvalid.1 hvalid.2.1 hvalid.2.2 hinput hHsum
  simpa only [cuts] using hcore

/-- Per-column cutoff for a live `m`-row tile, with any padded rows
excluded from the live rank interval. -/
def rowCutAtRankM (m x : Nat) (c : Col) : Nat :=
  min m ((x + 63 - c.val) / 64)

theorem row_lt_rowCutAtRankM_iff {m x r : Nat} (c : Col)
    (hr : r < m) :
    r < rowCutAtRankM m x c <-> 64 * r + c.val < x := by
  have hc : c.val < 64 := c.isLt
  unfold rowCutAtRankM
  omega

def rowMajorFlowCutsM {ports m : Nat}
    (bounds : Fin (ports + 1) -> Nat) (c : Col) (i : Nat) : Nat :=
  rowCutAtRankM m (bounds (Fin.mk (min i ports) (by omega))) c

theorem rowCutAtRankM_mono {m x y : Nat} (c : Col) (hxy : x <= y) :
    rowCutAtRankM m x c <= rowCutAtRankM m y c := by
  unfold rowCutAtRankM
  omega

theorem rowMajorFlowCutsM_valid {ports m : Nat}
    (bounds : Fin (ports + 1) -> Nat)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 64 * m)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i)) :
    (forall c : Col, rowMajorFlowCutsM (m := m) bounds c 0 = 0) ∧
    (forall c : Col, rowMajorFlowCutsM (m := m) bounds c ports = m) ∧
    (forall c i, i < ports ->
      rowMajorFlowCutsM (m := m) bounds c i <= rowMajorFlowCutsM (m := m) bounds c (i + 1)) := by
  constructor
  intro c
  change rowCutAtRankM m (bounds 0) c = 0
  rw [hfirst]
  unfold rowCutAtRankM
  have hc : c.val < 64 := c.isLt
  omega
  constructor
  intro c
  change rowCutAtRankM m (bounds (Fin.mk (min ports ports) (by omega))) c = m
  have hidx :
      (Fin.mk (min ports ports) (by omega) : Fin (ports + 1)) = Fin.last ports := by
    apply Fin.ext
    simp
  rw [hidx, hlast]
  unfold rowCutAtRankM
  have hc : c.val < 64 := c.isLt
  omega
  intro c i hi
  have hleft : min i ports = i := Nat.min_eq_left (Nat.le_of_lt hi)
  have hright : min (i + 1) ports = i + 1 := Nat.min_eq_left (by omega)
  have hbound : bounds (Fin.mk i (by omega)) <=
      bounds (Fin.mk (i + 1) (by omega)) := by
    simpa [Fin.castSucc, Fin.succ] using hmono (Fin.mk i hi)
  have hcut := rowCutAtRankM_mono (m := m) c hbound
  simpa [rowMajorFlowCutsM, hleft, hright] using hcut

theorem rowMajorFlowCutsM_port_contained {ports m : Nat}
    (bounds : Fin (ports + 1) -> Nat) (i : Fin ports) (c : Col)
    {r : Nat} (hr : r < m)
    (hmono : forall j : Fin ports,
      bounds (Fin.castSucc j) <= bounds (Fin.succ j))
    (hrowlo : rowMajorFlowCutsM (m := m) bounds c i.val <= r)
    (hrowhi : r < rowMajorFlowCutsM (m := m) bounds c (i.val + 1)) :
    bounds (Fin.castSucc i) <= 64 * r + c.val ∧
      64 * r + c.val < bounds (Fin.succ i) := by
  have hbound : bounds (Fin.castSucc i) <= bounds (Fin.succ i) := hmono i
  have hrowlo' : rowCutAtRankM m (bounds (Fin.castSucc i)) c <= r := by
    simpa [rowMajorFlowCutsM,
      Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hrowlo
  have hrowhi' : r < rowCutAtRankM m (bounds (Fin.succ i)) c := by
    simpa [rowMajorFlowCutsM,
      Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)] using hrowhi
  have hge : bounds (Fin.castSucc i) <= 64 * r + c.val := by
    by_contra hn
    have hlt : 64 * r + c.val < bounds (Fin.castSucc i) := by omega
    have hcut := (row_lt_rowCutAtRankM_iff c hr).2 hlt
    omega
  have hlt := (row_lt_rowCutAtRankM_iff c hr).1 hrowhi'
  exact And.intro hge hlt

/-- The partial-row core's 448 exact-rank contract also accepts D2 flow
boundaries directly after converting them to live per-column cuts. The core's
existing padding theorem extends only the final port to 4096 rows. -/
theorem rowMajorFlowCutsM_rebinned_core_error_le_448
    {ports : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (bounds : Fin (ports + 1) -> Nat) (m : Nat)
    (sourceHeight : Col -> Nat) (H : Nat) (tag : Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = 64 * m)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hinput : forall c, sourceHeight c <= m)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
        tag cell.2 = j).sum fun cell =>
          (prefixIntervalMass (fullHeightTwoShuffle sourceHeight cell.1)
            (rowMajorFlowCutsM (m := m) bounds cell.1 cell.2.val)
            (rowMajorFlowCutsM (m := m) bounds cell.1 (cell.2.val + 1)) : Rat) -
          prefixIntervalMass (exactRankColumnHeight H cell.1)
            (rowMajorFlowCutsM (m := m) bounds cell.1 cell.2.val)
            (rowMajorFlowCutsM (m := m) bounds cell.1 (cell.2.val + 1)))) <= 448 := by
  let cuts : Col -> Nat -> Nat := fun c i => rowMajorFlowCutsM (m := m) bounds c i
  have hvalid := rowMajorFlowCutsM_valid bounds hfirst hlast hmono
  have hcore := Chvatal.D2ColumnRebatchBridge.fullHeightTwoShuffle_partial_rows_rebinned_l1_le_448
    sourceHeight cuts ports m H (fun cell => tag cell.2)
    hports hm hvalid.1 hvalid.2.1 hvalid.2.2 hinput hHsum
  simpa only [cuts] using hcore

/-- Clip a global flow rank boundary to one tile's local rank interval. -/
def clippedTileFlowBounds {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (i : Fin (ports + 1)) : Nat :=
  min (64 * m) (bounds i - t.val * (64 * m))

theorem clippedTileFlowBounds_valid {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i)) :
    clippedTileFlowBounds m bounds t 0 = 0 ∧
    clippedTileFlowBounds m bounds t (Fin.last ports) = 64 * m ∧
    (forall i : Fin ports,
      clippedTileFlowBounds m bounds t (Fin.castSucc i) <=
        clippedTileFlowBounds m bounds t (Fin.succ i)) := by
  constructor
  simp [clippedTileFlowBounds, hfirst]
  constructor
  let W : Nat := 64 * m
  have htile : t.val + 1 <= tiles := Nat.succ_le_of_lt t.isLt
  have hmul : (t.val + 1) * W <= tiles * W :=
    Nat.mul_le_mul_right W htile
  have hmul0 : t.val * W + W <= tiles * W := by
    simpa [Nat.succ_mul] using hmul
  have hmul' : W + t.val * W <= tiles * W := by omega
  have hmul'' : W + t.val * W <= W * tiles := by
    calc
      W + t.val * W <= tiles * W := hmul'
      _ = W * tiles := Nat.mul_comm tiles W
  have hroom : W <= W * tiles - t.val * W := by omega
  simp [clippedTileFlowBounds, hlast, W, Nat.min_eq_left hroom]
  intro i
  unfold clippedTileFlowBounds
  apply min_le_min_left
  exact Nat.sub_le_sub_right (hmono i) _

/-- Error assigned to one D2 receiver tag after clipping global rank ports to
a particular fixed-core tile. Empty clipped ports contribute zero. -/
def clippedTileGroupedCoreError {ports tiles : Nat} {J : Type*}
    [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (H : Fin tiles -> Nat) (tag : Fin ports -> J) (j : J) : Rat :=
  abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
      tag cell.2 = j).sum fun cell =>
    (prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) cell.1)
      (rowMajorFlowCutsM (m := m)
        (clippedTileFlowBounds m bounds t) cell.1 cell.2.val)
      (rowMajorFlowCutsM (m := m)
        (clippedTileFlowBounds m bounds t) cell.1 (cell.2.val + 1)) : Rat) -
    prefixIntervalMass (exactRankColumnHeight (H t) cell.1)
      (rowMajorFlowCutsM (m := m)
        (clippedTileFlowBounds m bounds t) cell.1 cell.2.val)
      (rowMajorFlowCutsM (m := m)
        (clippedTileFlowBounds m bounds t) cell.1 (cell.2.val + 1)))

/-- A single monotone global D2 rank partition, clipped across all fixed-core
tiles, incurs at most 448 grouped exact-rank error per tile. This is the
concrete tiled form of the fixed-core transfer: no independent per-tile
boundary or receiver map is assumed. -/
theorem clippedGlobalFlowPorts_core_error_le_448_per_tile
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat) (H : Fin tiles -> Nat)
    (tag : Fin ports -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, H t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun j : J =>
        clippedTileGroupedCoreError m bounds t sourceHeight H tag j) <=
      448 * tiles := by
  calc
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun j : J =>
        clippedTileGroupedCoreError m bounds t sourceHeight H tag j) <=
      Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
        apply Finset.sum_le_sum
        intro t ht
        have hlocal := clippedTileFlowBounds_valid m bounds t hfirst hlast hmono
        simpa [clippedTileGroupedCoreError] using
          rowMajorFlowCutsM_rebinned_core_error_le_448
            (clippedTileFlowBounds m bounds t) m (sourceHeight t) (H t)
            tag hports hm hlocal.1 hlocal.2.1 hlocal.2.2
            (hinput t) (hHsum t)
    _ = 448 * tiles := by norm_num [Rat.mul_comm]

end Chvatal.D2RowMajorFlowCuts
