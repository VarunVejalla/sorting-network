import D2ClippedFlowProfileTransfer
import D2OrdinaryRankRouting
import D2StaticWireSets

set_option maxHeartbeats 500000

namespace Chvatal.D2ClippedCellRankInterval

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2RowMajorFlowCuts
open Chvatal.D2OrdinaryRankRouting
open Chvatal.D2StaticWireSets

abbrev Col := Fin 64

/-- A nonempty interval obtained by clipping `[a,b)` to the tile
`[start,start+width)` contains only global coordinates in `[a,b)`. -/
theorem clipped_interval_subset_global
    (width start a b x : Nat)
    (hlo : min width (a - start) <= x)
    (hhi : x < min width (b - start)) :
    a <= start + x /\ start + x < b := by
  have hxWidth : x < width := lt_of_lt_of_le hhi (Nat.min_le_left _ _)
  have hxEnd : x < b - start := lt_of_lt_of_le hhi (Nat.min_le_right _ _)
  have hstart : a <= start + x := by
    by_cases has : a <= start
    · omega
    · have hsa : start < a := by omega
      by_cases hwidth : width <= a - start
      · have hxlo : width <= x := by
          simpa [Nat.min_eq_left hwidth] using hlo
        omega
      · have hsub : a - start <= width := by omega
        have hxlo : a - start <= x := by
          simpa [Nat.min_eq_right hsub] using hlo
        omega
  exact ⟨hstart, by omega⟩

/-- Clipping a global rank interval to one tile is exact: a local offset is
inside the clipped interval precisely when its translated global rank is in
the original interval. -/
theorem clipped_interval_global_iff
    (width start a b x : Nat) (hx : x < width) :
    (min width (a - start) <= x ∧ x < min width (b - start)) ↔
      (a <= start + x ∧ start + x < b) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    exact clipped_interval_subset_global width start a b x hlo hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_cases hstart : a <= start
      · simpa [Nat.sub_eq_zero_of_le hstart]
      · have hsub : a - start <= width := by omega
        rw [Nat.min_eq_right hsub]
        omega
    · by_cases hstart : b <= start
      · omega
      · by_cases hwidth : width <= b - start
        · rw [Nat.min_eq_left hwidth]
          exact hx
        · have hsub : b - start <= width := by omega
          rw [Nat.min_eq_right hsub]
          omega

/-- A row/column port cell of the clipped profile has all its flattened local
rank positions inside that port's global sender interval. The clipped cuts
therefore preserve the static sender's receiver label. -/
theorem clippedFlowProfile_cell_rank_in_port
    {ports tiles : Nat} (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports) (c : Col) (r : Nat)
    (hr : r < 4096)
    (hrowLo : clippedFlowProfileCuts 4096 bounds t c p.val <= r)
    (hrowHi : r < clippedFlowProfileCuts 4096 bounds t c (p.val + 1)) :
    bounds (Fin.castSucc p) <= t.val * 262144 + (64 * r + c.val) /\
      t.val * 262144 + (64 * r + c.val) < bounds (Fin.succ p) := by
  have hcutLo : rowCutAtRankM 4096
      (clippedTileFlowBounds 4096 bounds t (Fin.castSucc p)) c <= r := by
    simpa [clippedFlowProfileCuts, rowMajorFlowCutsM,
      Nat.min_eq_left (Nat.le_of_lt p.isLt)] using hrowLo
  have hcutHi : r < rowCutAtRankM 4096
      (clippedTileFlowBounds 4096 bounds t (Fin.succ p)) c := by
    simpa [clippedFlowProfileCuts, rowMajorFlowCutsM,
      Nat.min_eq_left (Nat.succ_le_of_lt p.isLt)] using hrowHi
  have hxLo : clippedTileFlowBounds 4096 bounds t (Fin.castSucc p) <=
      64 * r + c.val := by
    by_contra hn
    have hlt : 64 * r + c.val <
        clippedTileFlowBounds 4096 bounds t (Fin.castSucc p) := by omega
    have hcontr := (row_lt_rowCutAtRankM_iff (m := 4096)
      (x := clippedTileFlowBounds 4096 bounds t (Fin.castSucc p)) c hr).2 hlt
    omega
  have hxHi : 64 * r + c.val <
      clippedTileFlowBounds 4096 bounds t (Fin.succ p) :=
    (row_lt_rowCutAtRankM_iff (m := 4096)
      (x := clippedTileFlowBounds 4096 bounds t (Fin.succ p)) c hr).1 hcutHi
  have hclip := (clipped_interval_global_iff 262144
    (t.val * 262144) (bounds (Fin.castSucc p)) (bounds (Fin.succ p))
    (64 * r + c.val) (by have hc := c.isLt; omega)).1
    (And.intro (by simpa [clippedTileFlowBounds] using hxLo)
      (by simpa [clippedTileFlowBounds] using hxHi))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hclip

/-- Exact clipped-port membership criterion for a row/column profile cell.
This is the converse needed to turn the cell-level receiver-label statement
into an exact grouped-count identity. -/
theorem clippedFlowProfile_cell_rank_iff_port
    {ports tiles : Nat} (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports) (c : Col) (r : Nat)
    (hr : r < 4096) :
    (bounds (Fin.castSucc p) <= t.val * 262144 + (64 * r + c.val) /\
      t.val * 262144 + (64 * r + c.val) < bounds (Fin.succ p)) <->
    (clippedFlowProfileCuts 4096 bounds t c p.val <= r /\
      r < clippedFlowProfileCuts 4096 bounds t c (p.val + 1)) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hflat : 64 * r + c.val < 262144 := by
      have hc := c.isLt
      omega
    have hlocal := (clipped_interval_global_iff 262144
      (t.val * 262144) (bounds (Fin.castSucc p)) (bounds (Fin.succ p))
      (64 * r + c.val) hflat).2 ⟨hlo, hhi⟩
    have hloRaw : bounds (Fin.castSucc p) - t.val * 262144 <= 64 * r + c.val := by omega
    have hloClipped : clippedTileFlowBounds 4096 bounds t (Fin.castSucc p) <=
        64 * r + c.val := by
      exact le_trans (Nat.min_le_right _ _) hloRaw
    have hhiRaw : 64 * r + c.val < bounds (Fin.succ p) - t.val * 262144 := by omega
    have hhiClipped : 64 * r + c.val <
        clippedTileFlowBounds 4096 bounds t (Fin.succ p) := by
      simpa [clippedTileFlowBounds, Nat.lt_min] using And.intro hflat hhiRaw
    have hcutLo : rowCutAtRankM 4096
        (clippedTileFlowBounds 4096 bounds t (Fin.castSucc p)) c <= r := by
      by_contra hn
      have hrlt : r < rowCutAtRankM 4096
          (clippedTileFlowBounds 4096 bounds t (Fin.castSucc p)) c := by omega
      have hbad := (row_lt_rowCutAtRankM_iff (m := 4096)
        (x := clippedTileFlowBounds 4096 bounds t (Fin.castSucc p)) c hr).1 hrlt
      omega
    have hcutHi : r < rowCutAtRankM 4096
        (clippedTileFlowBounds 4096 bounds t (Fin.succ p)) c :=
      (row_lt_rowCutAtRankM_iff (m := 4096)
        (x := clippedTileFlowBounds 4096 bounds t (Fin.succ p)) c hr).2 hhiClipped
    constructor
    · simpa [clippedFlowProfileCuts, rowMajorFlowCutsM,
        Nat.min_eq_left (Nat.le_of_lt p.isLt)] using hcutLo
    · simpa [clippedFlowProfileCuts, rowMajorFlowCutsM,
        Nat.min_eq_left (Nat.succ_le_of_lt p.isLt)] using hcutHi
  · rintro ⟨hlo, hhi⟩
    exact clippedFlowProfile_cell_rank_in_port bounds t p c r hr hlo hhi

/-- Under the sender's usual rank-order placement, every wire represented by
a row of one clipped tile/column/child-port profile cell belongs to the
physical child destination set. This is the tag-uniformity statement for that
profile cell; only the rank-order placement and actual profile-count identity
remain to be instantiated by the schedule. -/
theorem clipped_profile_cell_wire_in_child_receiver
    {ports tiles n : Nat} (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports) (c : Col) (r : Nat)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (S : Finset (Fin n)) (w : Fin n)
    (hr : r < 4096)
    (hrowLo : clippedFlowProfileCuts 4096 bounds t c p.val <= r)
    (hrowHi : r < clippedFlowProfileCuts 4096 bounds t c (p.val + 1))
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1))
    (hw : w ∈ S)
    (hrank : Chvatal.rankIn S w = t.val * 262144 + (64 * r + c.val)) :
    w ∈ destinationPiece (ports := 8) S boundary left rightStart (some child) := by
  have hcoordinates := clippedFlowProfile_cell_rank_in_port bounds t p c r
    hr hrowLo hrowHi
  rw [hlo, hhi] at hcoordinates
  change w ∈ Chvatal.blockOf S
    (left + boundary child.val) (left + boundary (child.val + 1))
  apply Chvatal.mem_blockOf.mpr
  refine ⟨hw, ?_, ?_⟩
  · rw [hrank]
    exact hcoordinates.1
  · rw [hrank]
    exact hcoordinates.2

/- The rank-placement equation used above is supplied by the canonical
ordered embedding of a complete tile of sender ranks. Thus every profile
slot in a child port has an actual sender wire address with that receiver
label; no extra hypothesis about an arbitrary wire is needed. -/
theorem ordered_tile_profile_cell_wire_in_child_receiver
    {ports tiles n : Nat} (S : Finset (Fin n))
    (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports) (c : Col) (r : Nat)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (hr : r < 4096)
    (htile : (t.val + 1) * 262144 <= S.card)
    (hrowLo : clippedFlowProfileCuts 4096 bounds t c p.val <= r)
    (hrowHi : r < clippedFlowProfileCuts 4096 bounds t c (p.val + 1))
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1)) :
    S.orderEmbOfFin rfl
      (Fin.mk (t.val * 262144 + (64 * r + c.val)) (by
        have hc := c.isLt
        omega)) ∈
      destinationPiece (ports := 8) S boundary left rightStart (some child) := by
  let slot : Fin S.card := ⟨t.val * 262144 + (64 * r + c.val), by
    have hc := c.isLt
    omega⟩
  have hrank : Chvatal.rankIn S (S.orderEmbOfFin rfl slot) = slot.val :=
    Chvatal.D2StaticWireSets.rankIn_orderEmbOfFin S slot
  exact clipped_profile_cell_wire_in_child_receiver bounds t p c r child
    boundary left rightStart S (S.orderEmbOfFin rfl slot) hr hrowLo hrowHi
    hlo hhi (Finset.orderEmbOfFin_mem S rfl slot) (by simpa [slot] using hrank)

/-- Exact local tag identity for an ordered sender tile: its row/column slot
belongs to a child's physical destination exactly when the clipped profile
assigns that row to the corresponding port. -/
theorem ordered_tile_profile_cell_tag_iff
    {ports tiles n : Nat} (S : Finset (Fin n))
    (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports) (c : Col) (r : Nat)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (hr : r < 4096)
    (htile : (t.val + 1) * 262144 <= S.card)
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1)) :
    (clippedFlowProfileCuts 4096 bounds t c p.val <= r /\
      r < clippedFlowProfileCuts 4096 bounds t c (p.val + 1)) <->
    S.orderEmbOfFin rfl
      (Fin.mk (t.val * 262144 + (64 * r + c.val)) (by
        have hc := c.isLt
        omega)) ∈
      destinationPiece (ports := 8) S boundary left rightStart (some child) := by
  let slot : Fin S.card := ⟨t.val * 262144 + (64 * r + c.val), by
    have hc := c.isLt
    omega⟩
  have hrank : Chvatal.rankIn S (S.orderEmbOfFin rfl slot) = slot.val :=
    Chvatal.D2StaticWireSets.rankIn_orderEmbOfFin S slot
  constructor
  · intro hrow
    exact ordered_tile_profile_cell_wire_in_child_receiver S bounds t p c r
      child boundary left rightStart hr htile hrow.1 hrow.2 hlo hhi
  · intro hdest
    have hblock : S.orderEmbOfFin rfl slot ∈
        Chvatal.blockOf S (left + boundary child.val)
          (left + boundary (child.val + 1)) := by
      simpa [destinationPiece] using hdest
    have hbounds : bounds (Fin.castSucc p) <=
        Chvatal.rankIn S (S.orderEmbOfFin rfl slot) /\
      Chvatal.rankIn S (S.orderEmbOfFin rfl slot) < bounds (Fin.succ p) := by
      rw [hlo, hhi]
      exact (Chvatal.mem_blockOf.mp hblock).2
    have hglobal : bounds (Fin.castSucc p) <=
        t.val * 262144 + (64 * r + c.val) /\
      t.val * 262144 + (64 * r + c.val) < bounds (Fin.succ p) := by
      simpa [hrank, slot] using hbounds
    exact (clippedFlowProfile_cell_rank_iff_port bounds t p c r hr).1 hglobal

end Chvatal.D2ClippedCellRankInterval
