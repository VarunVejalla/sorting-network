import D2FalseProfileTransfer
import D2ClippedFlowProfileTransfer
import D2RowMajorFlowCuts

open scoped BigOperators

namespace Chvatal.D2FalseClippedTransfer

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2FalseProfileTransfer
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2RankAlignment
open Chvatal.D2RowMajorFlowCuts

abbrev Col := Fin 64
abbrev Row := Fin 4096
abbrev Wire := Fin (4096 * 64)

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable def reflectedCoreFalseProfile (v : Wire -> Bool) (c : Col) : Nat :=
  matrixColumnFalseCount c
    ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
      Chvatal.D2ReflectedPhysicalPack.reflectedSigma35
      Chvatal.D2ReflectedPhysicalPack.reflectedSigma25).exec v)

/-- On full-height source tiles, the false-profile port provider applies to
the actual per-tile cuts induced by a clipped global rank partition. It gives
the local L1 premise required by the arbitrary-profile receiver grouping
theorem, with no assumptions on how those cells will later be tagged. -/
theorem clipped_fullheight_false_core_profile_error_le_448
    {ports tiles : Nat} (bounds : Fin (ports + 1) -> Nat)
    (input : Fin tiles -> Wire -> Bool)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass : Fin tiles -> Nat)
    (hports : 0 < ports)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * 4096) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hcount : forall t c,
      Chvatal.matrixColumnTrueCount c (input t) = sourceHeight t c)
    (hinput : forall t c, sourceHeight t c <= 4096)
    (hMass : forall t,
      tileMass t = (Finset.univ.filter fun w : Wire => input t w = false).card) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        countDistance
          (clippedFlowProfileActualCountOfProfile 4096 bounds
            (fun t c => reflectedCoreFalseProfile (input t) c) t cell)
          (clippedFlowProfileRankCount 4096 bounds tileMass t cell)) <=
      448 * tiles := by
  have hvalid (t : Fin tiles) := by
    have hclip := clippedTileFlowBounds_valid 4096 bounds t hfirst hlast hmono
    exact rowMajorFlowCutsM_valid (clippedTileFlowBounds 4096 bounds t)
      hclip.1 hclip.2.1 hclip.2.2
  have hlocal (t : Fin tiles) :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        countDistance
          (clippedFlowProfileActualCountOfProfile 4096 bounds
            (fun t c => reflectedCoreFalseProfile (input t) c) t cell)
          (clippedFlowProfileRankCount 4096 bounds tileMass t cell)) <= 448 := by
    let cuts : Col -> Nat -> Nat := clippedFlowProfileCuts 4096 bounds t
    have hRat := reflected_core_false_exact_rank_port_error_le_448_of_input_mass
      (input t) (sourceHeight t) (fun c => hcount t c) (fun c => hinput t c)
      (tileMass t) ports cuts (hMass t)
      (fun c => (hvalid t).1 c)
      (fun c => by simpa [cuts] using (hvalid t).2.1 c)
      (by
        intro c i hi
        exact (hvalid t).2.2 c i hi)
    have hcast :
        ((Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance
            (clippedFlowProfileActualCountOfProfile 4096 bounds
              (fun t c => reflectedCoreFalseProfile (input t) c) t cell)
            (clippedFlowProfileRankCount 4096 bounds tileMass t cell) : Nat) : Rat) =
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            abs ((clippedFlowProfileActualCountOfProfile 4096 bounds
                (fun t c => reflectedCoreFalseProfile (input t) c) t cell : Rat) -
              (clippedFlowProfileRankCount 4096 bounds tileMass t cell : Rat)) := by
      simp only [Nat.cast_sum, countDistance_rat_eq_abs_for_profiles]
    have hbound :
        ((Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance
            (clippedFlowProfileActualCountOfProfile 4096 bounds
              (fun t c => reflectedCoreFalseProfile (input t) c) t cell)
            (clippedFlowProfileRankCount 4096 bounds tileMass t cell) : Nat) : Rat) <= 448 := by
      rw [hcast]
      simpa [cuts, clippedFlowProfileActualCountOfProfile,
        clippedFlowProfileRankCount, reflectedCoreFalseProfile] using hRat
    exact_mod_cast hbound
  calc
    _ <= Finset.univ.sum fun _ : Fin tiles => (448 : Nat) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hlocal t
    _ = 448 * tiles := by simp [Nat.mul_comm]

/-- Compose the clipped false-profile provider with the existing arbitrary
receiver-tag theorem. This closes the analytic transfer for full-height tiles;
only identifying the supplied tags and parent masses with an actual D2 run is
left to the schedule bridge. -/
theorem clipped_fullheight_false_core_grouped_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (bounds : Fin (ports + 1) -> Nat)
    (input : Fin tiles -> Wire -> Bool)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * 4096) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hcount : forall t c,
      Chvatal.matrixColumnTrueCount c (input t) = sourceHeight t c)
    (hinput : forall t c, sourceHeight t c <= 4096)
    (hMass : forall t,
      tileMass t = (Finset.univ.filter fun w : Wire => input t w = false).card)
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (clippedFlowGroupedActualOfProfile 4096 bounds
          (fun t c => reflectedCoreFalseProfile (input t) c) tag j)
        (clippedFlowGroupedRank 4096 bounds idealTileMass tag j)) <=
      parentError + 448 * tiles := by
  exact clipped_global_profile_error_le_parent_add_448_of_actual_profile
    4096 bounds (fun t c => reflectedCoreFalseProfile (input t) c)
    tileMass idealTileMass tag parentError hports (by omega)
    hfirst hlast hmono hH hI
    (clipped_fullheight_false_core_profile_error_le_448 bounds input
      sourceHeight tileMass hports hfirst hlast hmono hcount hinput hMass)
    hMacroParent

end Chvatal.D2FalseClippedTransfer
