import D2ClippedFlowProfileTransfer
import D2OrdinaryRankRouting
import D2StaticWireSets
import D2PhysicalRankRouting
import D2ReflectedPhysicalPack
import D2LiftedShuffleBridge
import D2VariableTilePhysicalFlowTransfer

set_option maxHeartbeats 500000

namespace Chvatal.D2ClippedCellRankInterval

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2RowMajorFlowCuts
open Chvatal.D2OrdinaryRankRouting
open Chvatal.D2StaticWireSets
open Chvatal.D2PhysicalRankRouting
open Chvatal.D2RankProfileRouting
open Chvatal.D2RankAlignment
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2VariableTilePhysicalFlowTransfer
open Chvatal.D2Reserve

abbrev Col := Fin 64
abbrev Row := Fin 4096
abbrev Wire := Fin (4096 * 64)

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

/-- For one complete sender tile, the false count in a clipped column/port
profile equals the actual number of false output wires in that child's
physical destination. This is the count identity needed to instantiate the
ordinary-sender transition from the local profile theorem. -/
theorem ordered_tile_child_false_count_eq_profile
    {ports tiles n : Nat} (S : Finset (Fin n))
    (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (height : Col -> Nat) (out : Wire -> Bool)
    (htile : (t.val + 1) * 262144 <= S.card)
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1))
    (hprofile : forall r : Row, forall c : Col,
      out (Chvatal.matrixWire 4096 64 r c) = decide (height c <= r.val)) :
    (Finset.univ.sum fun c : Col =>
      prefixIntervalMass (height c)
        (clippedFlowProfileCuts 4096 bounds t c p.val)
        (clippedFlowProfileCuts 4096 bounds t c (p.val + 1))) =
    (Finset.univ.sum fun b : Wire =>
      if S.orderEmbOfFin rfl
          (Fin.mk (t.val * 262144 + b.val) (by
            have hb := b.isLt
            omega)) ∈ destinationPiece (ports := 8) S boundary left rightStart
            (some child) ∧ out b = false then 1 else 0) := by
  let address : Wire -> Fin n := fun b =>
    S.orderEmbOfFin rfl (Fin.mk (t.val * 262144 + b.val) (by
      have hb := b.isLt
      omega))
  let lo : Col -> Nat := fun c => clippedFlowProfileCuts 4096 bounds t c p.val
  let hi : Col -> Nat := fun c => clippedFlowProfileCuts 4096 bounds t c (p.val + 1)
  let rowCount : Col -> Nat := fun c =>
    Finset.univ.sum fun r : Row =>
      if lo c <= r.val ∧ r.val < hi c ∧ r.val < height c then 1 else 0
  have hslot :
      (Finset.univ.sum fun b : Wire =>
        if address b ∈ destinationPiece (ports := 8) S boundary left rightStart
            (some child) ∧ out b = false then 1 else 0) =
      Finset.univ.sum fun c : Col => Finset.univ.sum fun r : Row =>
        if lo c <= r.val /\ r.val < hi c /\ r.val < height c then 1 else 0 := by
    rw [Chvatal.sum_matrixWire (by omega)]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro r hr
    have haddr : address (Chvatal.matrixWire 4096 64 r c) =
        S.orderEmbOfFin rfl (Fin.mk
          (t.val * 262144 + (64 * r.val + c.val)) (by
            have hcr : 64 * r.val + c.val < 262144 := by
              have hc' := c.isLt
              omega
            omega)) := by
      apply congrArg (S.orderEmbOfFin rfl)
      apply Fin.ext
      simp [address, Chvatal.matrixWire]
      omega
    have htag := ordered_tile_profile_cell_tag_iff S bounds t p c r.val
      child boundary left rightStart r.isLt htile hlo hhi
    have hclass : address (Chvatal.matrixWire 4096 64 r c) ∈
        destinationPiece (ports := 8) S boundary left rightStart (some child) <->
        lo c <= r.val /\ r.val < hi c := by
      rw [haddr]
      simpa [lo, hi] using htag.symm
    have hfalse : out (Chvatal.matrixWire 4096 64 r c) = false <->
        r.val < height c := by
      rw [hprofile r c]
      simp
    simp only [hclass, hfalse]
    simp [and_assoc]
  have hrow (c : Col) :
      (Finset.univ.sum fun r : Row =>
        if lo c <= r.val /\ r.val < hi c /\ r.val < height c then 1 else 0) =
      prefixIntervalMass (height c) (lo c) (hi c) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : Nat => if lo c <= r /\ r < hi c /\ r < height c then 1 else 0)
      4096]
    have hhiBound : hi c <= 4096 := by
      dsimp [hi, clippedFlowProfileCuts, rowMajorFlowCutsM, rowCutAtRankM]
      exact Nat.min_le_left _ _
    exact Chvatal.D2PhysicalRankRouting.rowMajorPortCount_eq_prefixIntervalMass
      4096 (height c) (lo c) (hi c) hhiBound
  calc
    _ = Finset.univ.sum fun c : Col => rowCount c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (hrow c).symm
    _ = Finset.univ.sum fun c : Col =>
          Finset.univ.sum fun r : Row =>
            if lo c <= r.val /\ r.val < hi c /\ r.val < height c then 1 else 0 := by
      rfl
    _ = Finset.univ.sum fun b : Wire =>
          if address b ∈ destinationPiece (ports := 8) S boundary left rightStart
              (some child) ∧ out b = false then 1 else 0 := hslot.symm

/-- Instantiate the exact tile-count identity on the actual reflected physical
core for an arbitrary Boolean sender input. The core's checked column
monotonicity makes its output a false-prefix profile with heights equal to
the actual per-column false counts, so no output-profile hypothesis is
needed. -/
theorem reflected_core_ordered_tile_child_false_count_eq_profile
    {ports tiles n : Nat} (S : Finset (Fin n))
    (bounds : Fin (ports + 1) -> Nat)
    (t : Fin tiles) (p : Fin ports)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (input : Wire -> Bool)
    (htile : (t.val + 1) * 262144 <= S.card)
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1)) :
    (Finset.univ.sum fun c : Col =>
      prefixIntervalMass
        (matrixColumnFalseCount c
          ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
            reflectedSigma35 reflectedSigma25).exec input))
        (clippedFlowProfileCuts 4096 bounds t c p.val)
        (clippedFlowProfileCuts 4096 bounds t c (p.val + 1))) =
    (Finset.univ.sum fun b : Wire =>
      if S.orderEmbOfFin rfl
          (Fin.mk (t.val * 262144 + b.val) (by
            have hb := b.isLt
            omega)) ∈ destinationPiece (ports := 8) S boundary left rightStart
            (some child) ∧
          (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
            reflectedSigma35 reflectedSigma25).exec input b = false then 1 else 0) := by
  let output := (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    reflectedSigma35 reflectedSigma25).exec input
  have hmono : ColumnMonotoneInput 4096 64 (by omega) output := by
    intro c r s hrs
    exact reflectedPhysicalPackTwoGrid_columnMonotone input
      (fun c => matrixColumnTrueCount c input) (by intro c; rfl)
      (by intro c; exact matrixColumnTrueCount_le c input) c hrs
  have hprefix := columnMonotone_eq_lowPrefixBool output hmono
  have hprofile (r : Row) (c : Col) :
      output (Chvatal.matrixWire 4096 64 r c) =
        decide (matrixColumnFalseCount c output <= r.val) := by
    have h := congrFun hprefix (Chvatal.matrixWire 4096 64 r c)
    change output (Chvatal.matrixWire 4096 64 r c) =
      decide (matrixColumnFalseCount
        (Chvatal.matrixCol 4096 64 (by omega)
          (Chvatal.matrixWire 4096 64 r c)) output <=
        (Chvatal.matrixRow 4096 64 (by omega)
          (Chvatal.matrixWire 4096 64 r c)).val) at h
    rcases Chvatal.matrixWire_row_col (by omega) r c with ⟨hr, hc⟩
    rw [hr, hc] at h
    exact h
  exact ordered_tile_child_false_count_eq_profile
    S bounds t p child boundary left rightStart
    (fun c => matrixColumnFalseCount c output) output htile hlo hhi hprofile

/-- Sum the actual reflected-core tile identities over a sender's complete
rank tiles. This leaves the final ragged rank suffix out explicitly, so the
ordinary-sender bridge can handle it with a separate partial-tile lemma. -/
theorem reflected_core_complete_tiles_child_false_count_eq_profile
    {ports tiles n : Nat} (S : Finset (Fin n))
    (bounds : Fin (ports + 1) -> Nat) (p : Fin ports)
    (child : Fin 8) (boundary : Nat -> Nat) (left rightStart : Nat)
    (input : Fin tiles -> Wire -> Bool)
    (hcomplete : forall t : Fin tiles,
      (t.val + 1) * 262144 <= S.card)
    (hlo : bounds (Fin.castSucc p) = left + boundary child.val)
    (hhi : bounds (Fin.succ p) = left + boundary (child.val + 1)) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun c : Col =>
        prefixIntervalMass
          (matrixColumnFalseCount c
            ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              reflectedSigma35 reflectedSigma25).exec (input t)))
          (clippedFlowProfileCuts 4096 bounds t c p.val)
          (clippedFlowProfileCuts 4096 bounds t c (p.val + 1))) =
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun b : Wire =>
        if S.orderEmbOfFin rfl
            (Fin.mk (t.val * 262144 + b.val) (by
              have hb := b.isLt
              have ht := hcomplete t
              omega)) ∈ destinationPiece (ports := 8) S boundary left rightStart
              (some child) ∧
            (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              reflectedSigma35 reflectedSigma25).exec (input t) b = false
        then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro t ht
  exact reflected_core_ordered_tile_child_false_count_eq_profile
    S bounds t p child boundary left rightStart (input t) (hcomplete t) hlo hhi

/-- Specialize the complete-tile identity to one of the eight child ports of
an ordinary D2 sender. The cumulative cuts are the flow's actual sender-port
boundaries, and the destination tag is the matching child rank interval. -/
theorem reflected_core_ordinary_child_tile_false_count_eq_profile
    {tiles n : Nat} (S : Finset (Fin n))
    (quota : Nat) (widths : Fin 8 -> Nat) (child : Fin 8)
    (t : Fin tiles) (input : Wire -> Bool)
    (hconserve : quota + d2FlowTotal widths = S.card)
    (hcomplete : (t.val + 1) * 262144 <= S.card) :
    (Finset.univ.sum fun c : Col =>
      prefixIntervalMass
        (matrixColumnFalseCount c
          ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
            reflectedSigma35 reflectedSigma25).exec input))
        (clippedFlowProfileCuts 4096
          (fun i : Fin 11 => d2SenderPortBoundaryNat quota S.card widths i.val)
          t c (child.val + 1))
        (clippedFlowProfileCuts 4096
          (fun i : Fin 11 => d2SenderPortBoundaryNat quota S.card widths i.val)
          t c (child.val + 2))) =
    (Finset.univ.sum fun b : Wire =>
      if S.orderEmbOfFin rfl
          (Fin.mk (t.val * 262144 + b.val) (by
            have hb := b.isLt
            omega)) ∈ destinationPiece (ports := 8) S
              (d2FlowRankBoundary widths) (quota / 2)
              (S.card - quota / 2) (some child) ∧
          (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
            reflectedSigma35 reflectedSigma25).exec input b = false
      then 1 else 0) := by
  let bounds : Fin 11 -> Nat := fun i =>
    d2SenderPortBoundaryNat quota S.card widths i.val
  let port : Fin 10 := ⟨child.val + 1, by omega⟩
  have hlo : bounds (Fin.castSucc port) =
      quota / 2 + d2FlowRankBoundary widths child.val := by
    simp [bounds, port, d2SenderPortBoundaryNat]
    omega
  have hhi : bounds (Fin.succ port) =
      quota / 2 + d2FlowRankBoundary widths (child.val + 1) := by
    simp [bounds, port, d2SenderPortBoundaryNat]
    omega
  exact reflected_core_ordered_tile_child_false_count_eq_profile
    S bounds t port child (d2FlowRankBoundary widths) (quota / 2)
    (S.card - quota / 2) input hcomplete hlo hhi

/-- Aggregate the ordinary-child identity over all complete tiles of one
ordinary sender. The tile inputs may vary arbitrarily; each is routed through
the same reflected core and canonical sender-rank address map. -/
theorem reflected_core_ordinary_child_complete_tiles_false_count_eq_profile
    {tiles n : Nat} (S : Finset (Fin n))
    (quota : Nat) (widths : Fin 8 -> Nat) (child : Fin 8)
    (input : Fin tiles -> Wire -> Bool)
    (hconserve : quota + d2FlowTotal widths = S.card)
    (hcomplete : forall t : Fin tiles,
      (t.val + 1) * 262144 <= S.card) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun c : Col =>
        prefixIntervalMass
          (matrixColumnFalseCount c
            ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              reflectedSigma35 reflectedSigma25).exec (input t)))
          (clippedFlowProfileCuts 4096
            (fun i : Fin 11 => d2SenderPortBoundaryNat quota S.card widths i.val)
            t c (child.val + 1))
          (clippedFlowProfileCuts 4096
            (fun i : Fin 11 => d2SenderPortBoundaryNat quota S.card widths i.val)
            t c (child.val + 2))) =
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun b : Wire =>
        if S.orderEmbOfFin rfl
            (Fin.mk (t.val * 262144 + b.val) (by
              have hb := b.isLt
              have ht := hcomplete t
              omega)) ∈ destinationPiece (ports := 8) S
                (d2FlowRankBoundary widths) (quota / 2)
                (S.card - quota / 2) (some child) ∧
            (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              reflectedSigma35 reflectedSigma25).exec (input t) b = false
        then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro t ht
  exact reflected_core_ordinary_child_tile_false_count_eq_profile
    S quota widths child t (input t) hconserve (hcomplete t)

end Chvatal.D2ClippedCellRankInterval
