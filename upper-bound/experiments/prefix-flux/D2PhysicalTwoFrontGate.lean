import D2AllStageTwoFrontGate
import D2FalseClippedTransfer

open scoped BigOperators

namespace Chvatal.D2PhysicalTwoFrontGate

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2FalseClippedTransfer
open Chvatal.D2RankAlignment
open Chvatal.D2Reserve

abbrev Col := Fin 64
abbrev Wire := Fin (4096 * 64)

/-- Compose the checked full-height physical false-profile transfer with the
all-stage two-front reserve. The remaining sender-specific geometric
obligation is `hideal`: grouped ideal profile mass must be dominated by the
corresponding single-prefix flow rank interval. Parent tile-mass discrepancy
plus the 448-per-source-tile core error then bounds actual overrun above every
next-child reserve. -/
theorem d2_physical_grouped_overrun_le_parent_add_448
    {h i t tiles : Nat}
    (hd : 7 <= (h + 1) + i) (ht : 0 < t)
    (path : D2FlowPath i)
    (ha : d2FlowCandidateActive ((h + 1) + i) t i = true)
    (hr : d2FlowCandidateRole ((h + 1) + i) t i = .topRise ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .mid ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .botDesc)
    (G low high : Nat) (children : Fin 8 → D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun ((h + 1) + i)
        (d2FlowTreeInitial 8192 ((h + 1) + i)) t) path =
        .node G low high children)
    (bounds : Fin 9 → Nat)
    (input : Fin tiles → Wire → Bool)
    (sourceHeight : Fin tiles → Col → Nat)
    (tileMass idealTileMass : Fin tiles → Nat)
    (tag : Fin tiles → Prod Col (Fin 8) → Fin 8)
    (parentError : Nat)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last 8) = (64 * 4096) * tiles)
    (hmono : ∀ p : Fin 8,
      bounds (Fin.castSucc p) ≤ bounds (Fin.succ p))
    (hcount : ∀ tile c,
      Chvatal.matrixColumnTrueCount c (input tile) = sourceHeight tile c)
    (hinput : ∀ tile c, sourceHeight tile c ≤ 4096)
    (hMass : ∀ tile,
      tileMass tile = (Finset.univ.filter fun w : Wire =>
        input tile w = false).card)
    (hH : ∀ tile, tileMass tile ≤ 262144)
    (hI : ∀ tile, idealTileMass tile ≤ 262144)
    (hMacroParent : (Finset.univ.sum fun tile : Fin tiles =>
      countDistance (tileMass tile) (idealTileMass tile)) ≤ parentError)
    (actual ideal : Fin 8 → Nat)
    (hactual : ∀ j, actual j =
      clippedFlowGroupedActualOfProfile 4096 bounds
        (fun tile c => reflectedCoreFalseProfile (input tile) c) tag j)
    (hidealGroup : ∀ j, ideal j =
      clippedFlowGroupedRank 4096 bounds idealTileMass tag j)
    (hideal : ∀ j : Fin 8, ideal j ≤ prefixIntervalMass G
      (d2FlowRankBoundary
        (fun k => d2FlowTreeRootDeficit (children k)) j.val)
      (d2FlowRankBoundary
        (fun k => d2FlowTreeRootDeficit (children k)) (j.val + 1))) :
    (Finset.univ.sum fun j : Fin 8 => actual j -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive ((h + 1) + i) t)
            (d2FlowCandidateRole ((h + 1) + i) t)
            (d2FlowCandidateQuota ((h + 1) + i) t)
            (h + 1) i (.node G low high children)) j)) <=
      parentError + 448 * tiles := by
  have htransfer : (Finset.univ.sum fun j : Fin 8 =>
      countDistance (actual j) (ideal j)) <= parentError + 448 * tiles := by
    have hphysical := clipped_fullheight_false_core_grouped_error_le_parent_add_448
      (ports := 8) (tiles := tiles) (J := Fin 8) bounds input sourceHeight
      tileMass idealTileMass tag parentError (by omega) hfirst hlast hmono
      hcount hinput hMass hH hI hMacroParent
    simpa [hactual, hidealGroup] using hphysical
  exact d2FlowCandidateRun_active_ordinary_mass_overrun_le_transfer_atPath
    hd ht path ha hr G low high children hnode actual ideal
    (parentError + 448 * tiles) htransfer hideal

end Chvatal.D2PhysicalTwoFrontGate
