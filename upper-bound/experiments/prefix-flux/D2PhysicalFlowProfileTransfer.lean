import D2ClippedFlowProfileTransfer
import D2PhysicalProfileMass
import D2ReflectedPhysicalPack

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Chvatal.D2PhysicalFlowProfileTransfer

open Chvatal.D2RankAlignment
open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2PhysicalProfileMass
open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2BandRepair4096Network
open Chvatal.D2RowMajorFlowCuts

abbrev Col := Fin 64

noncomputable def physicalFlowProfileActualCount {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat) (t : Fin tiles)
    (cell : Prod Col (Fin ports)) : Nat :=
  prefixIntervalMass
    (physicalTwoGridRepairHeight (sourceHeight t) reflectedCombinedSigma cell.1)
    (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
    (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1))

noncomputable def physicalFlowGroupedActual {ports tiles : Nat} {J : Type*}
    [DecidableEq J] (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x => physicalFlowProfileActualCount m bounds sourceHeight x.1 x.2

private theorem countDistance_rat_eq_abs (a b : Nat) :
    (countDistance a b : Rat) = abs ((a : Rat) - (b : Rat)) := by
  by_cases hab : a <= b
  · unfold countDistance
    rw [Nat.sub_eq_zero_of_le hab]
    have hsub : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) := Nat.cast_sub hab
    push_cast
    rw [hsub]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    ring
  · have hba : b <= a := Nat.le_of_not_ge hab
    unfold countDistance
    rw [Nat.sub_eq_zero_of_le hba]
    have hsub : ((a - b : Nat) : Rat) = (a : Rat) - (b : Rat) := Nat.cast_sub hba
    push_cast
    rw [hsub]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    ring

theorem clipped_physical_core_profile_error_le_448_per_tile
    {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass : Fin tiles -> Nat)
    (hports : 0 < ports)
    (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs ((physicalFlowProfileActualCount m bounds sourceHeight t cell : Rat) -
          (clippedFlowProfileRankCount m bounds tileMass t cell : Rat))) <=
      448 * tiles := by
  have hvalid (t : Fin tiles) := by
    have hclip := clippedTileFlowBounds_valid m bounds t hfirst hlast hmono
    exact rowMajorFlowCutsM_valid
      (clippedTileFlowBounds m bounds t) hclip.1 hclip.2.1 hclip.2.2
  calc
    _ <= Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
      apply Finset.sum_le_sum
      intro t ht
      let cuts : Col -> Nat -> Nat := fun c i =>
        clippedFlowProfileCuts m bounds t c i
      have hphysMass : tileMass t = Finset.univ.sum fun c : Col =>
          physicalTwoGridRepairHeight (sourceHeight t) reflectedCombinedSigma c := by
        rw [physical_profile_sum_eq_semantic_sum (sourceHeight t)
          (fun c => le_trans (hinput t c) hm) reflectedCombinedSigma]
        exact hHsum t
      have hlocal := physical_profile_partial_rows_rebinned_l1_le_448
        (sourceHeight t) reflectedCombinedSigma m ports (tileMass t) cuts
        hm hports (hinput t) hphysMass
        (hvalid t).1 (hvalid t).2.1 (fun c i hi => (hvalid t).2.2 c i hi)
        (by
          intro c i hi
          unfold cuts clippedFlowProfileCuts rowMajorFlowCutsM rowCutAtRankM
          omega)
      simpa [physicalFlowProfileActualCount, clippedFlowProfileRankCount,
        cuts, Chvatal.D2ReflectedPhysicalPack.reflectedCombinedSigma] using hlocal
    _ = 448 * tiles := by norm_num [Rat.mul_comm]

/-- The spatial profile recurrence remains valid for the actual physical
post-permutation profile: parent mismatch is charged once, and each input
tile contributes at most 448 fresh exact-rank error. -/
theorem clipped_global_physical_profile_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports)
    (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (physicalFlowGroupedActual m bounds sourceHeight tag j)
        (clippedFlowGroupedRank m bounds idealTileMass tag j)) <=
      parentError + 448 * tiles := by
  let actual : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    physicalFlowProfileActualCount m bounds sourceHeight x.1 x.2
  let reference : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds tileMass x.1 x.2
  let ideal : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds idealTileMass x.1 x.2
  let transfer : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    countDistance (actual x) (reference x)
  let group : Prod (Fin tiles) (Prod Col (Fin ports)) -> J := fun x => tag x.1 x.2
  have hlocalRat := clipped_physical_core_profile_error_le_448_per_tile
    m bounds sourceHeight tileMass hports hm hfirst hlast hmono hinput hHsum
  have hlocalRat' :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          abs ((actual (t, cell) : Rat) - (reference (t, cell) : Rat))) <=
        448 * tiles := by
    simpa [actual, reference, physicalFlowProfileActualCount,
      clippedFlowProfileRankCount] using hlocalRat
  have hlocalCast :
      ((Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance (actual (t, cell)) (reference (t, cell)) : Nat) : Rat) =
        Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            abs ((actual (t, cell) : Rat) - (reference (t, cell) : Rat)) := by
    simp only [Nat.cast_sum, countDistance_rat_eq_abs]
  have hlocalNat :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance (actual (t, cell)) (reference (t, cell))) <= 448 * tiles := by
    have hbound :
        ((Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            countDistance (actual (t, cell)) (reference (t, cell)) : Nat) : Rat) <=
          (448 * tiles : Nat) := by
      rw [hlocalCast]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlocalRat'
    exact_mod_cast hbound
  have hparentNested :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun c : Col =>
          Finset.univ.sum fun p : Fin ports =>
            countDistance (reference (t, (c, p))) (ideal (t, (c, p)))) <= parentError := by
    calc
      _ <= Finset.univ.sum fun t : Fin tiles =>
          countDistance (tileMass t) (idealTileMass t) := by
        apply Finset.sum_le_sum
        intro t ht
        have htile := clippedFlowProfile_parent_error_per_tile
          m bounds t (tileMass t) (idealTileMass t) hm hfirst hlast hmono
          (hH t) (hI t)
        simpa [reference, ideal, clippedFlowProfileRankCount] using htile
      _ <= parentError := hMacroParent
  have hParentProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
        countDistance (reference x) (ideal x)) <= parentError := by
    calc
      _ = Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            countDistance (reference (t, cell)) (ideal (t, cell)) := by
        rw [Fintype.sum_prod_type'
          (fun t cell => countDistance (reference (t, cell)) (ideal (t, cell)))]
      _ = Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun c : Col =>
            Finset.univ.sum fun p : Fin ports =>
              countDistance (reference (t, (c, p))) (ideal (t, (c, p))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Fintype.sum_prod_type'
          (fun c p => countDistance (reference (t, (c, p))) (ideal (t, (c, p))))]
      _ <= parentError := by simpa [reference, ideal] using hparentNested
  have hTransferProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) => transfer x) <=
        448 * tiles := by
    rw [Fintype.sum_prod_type' (fun t cell => transfer (t, cell))]
    simpa [transfer, actual, reference] using hlocalNat
  have hUpper : forall x : Prod (Fin tiles) (Prod Col (Fin ports)),
      actual x <= reference x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  have hLower : forall x : Prod (Fin tiles) (Prod Col (Fin ports)),
      reference x <= actual x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  calc
    _ <= parentError + Finset.univ.sum fun x :
        Prod (Fin tiles) (Prod Col (Fin ports)) => transfer x := by
      exact grouped_child_rank_error_le_parent_add_transfer
        group actual reference ideal transfer parentError hUpper hLower hParentProduct
    _ <= parentError + 448 * tiles := by omega

/-- The physical-profile recurrence closes the same 512-per-output-tile
budget when the schedule doubles its tile count. -/
theorem clipped_global_physical_profile_error_le_next_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (hports : 0 < ports)
    (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= 512 * tiles) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (physicalFlowGroupedActual m bounds sourceHeight tag j)
        (clippedFlowGroupedRank m bounds idealTileMass tag j)) <=
      512 * outputTiles := by
  have hstep := clipped_global_physical_profile_error_le_parent_add_448
    m bounds sourceHeight tileMass idealTileMass tag (512 * tiles)
    hports hm hfirst hlast hmono hH hI hinput hHsum hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 512 * tiles + 448 * tiles := hstep
    _ <= 512 * tiles + 512 * tiles := by omega
    _ = 512 * (2 * tiles) := by ring

end Chvatal.D2PhysicalFlowProfileTransfer
