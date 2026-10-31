import D2PhysicalProfileRangeTransfer
import D2ClippedFlowProfileTransfer

open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace Chvatal.D2PhysicalProfileGlobalTransfer

open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2PhysicalProfileRangeTransfer
open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2RowMajorFlowCuts
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2RankAlignment

abbrev Col := Fin 64
abbrev Wire := Fin (4096 * 64)

/-- The fixed physical four-sort output profile, exposed to the clipped-flow
transfer as a tile-indexed family. -/
noncomputable def physicalCoreOutputProfile {tiles : Nat}
    (inputs : Fin tiles → Wire → Bool) : Fin tiles → Col → Nat :=
  fun t c => matrixColumnTrueCount c
    ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
      reflectedSigma35 reflectedSigma25).exec (inputs t))

def physicalCoreInputMass {tiles : Nat}
    (inputs : Fin tiles → Wire → Bool) : Fin tiles → Nat :=
  fun t => (Finset.univ.filter fun w : Wire => inputs t w = true).card

/-- On a full 4096-row tile, the physical core's actual clipped receiver cells
have total l1 error at most 448 against the exact global-rank cells. The
global rank cuts may be arbitrary monotone ports; the physical provider is
reused without unfolding its comparator net in the profile transfer. -/
theorem physicalCore_clipped_cells_error_le_448
    {ports tiles : Nat}
    (inputs : Fin tiles → Wire → Bool)
    (bounds : Fin (ports + 1) → Nat)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * 4096) * tiles)
    (hmono : ∀ i : Fin ports, bounds (Fin.castSucc i) ≤ bounds (Fin.succ i)) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        countDistance
          (clippedFlowProfileActualCountOfProfile 4096 bounds
            (physicalCoreOutputProfile inputs) t cell)
          (clippedFlowProfileRankCount 4096 bounds
            (physicalCoreInputMass inputs) t cell)) ≤ 448 * tiles := by
  have hvalid (t : Fin tiles) := by
    have hclip := clippedTileFlowBounds_valid 4096 bounds t hfirst hlast hmono
    exact rowMajorFlowCutsM_valid (clippedTileFlowBounds 4096 bounds t)
      hclip.1 hclip.2.1 hclip.2.2
  have htile (t : Fin tiles) :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          countDistance
            (prefixIntervalMass
              (physicalCoreOutputProfile inputs t c)
              (clippedFlowProfileCuts 4096 bounds t c p.val)
              (clippedFlowProfileCuts 4096 bounds t c (p.val + 1)))
            (prefixIntervalMass
              (exactRankColumnHeight (physicalCoreInputMass inputs t) c)
              (clippedFlowProfileCuts 4096 bounds t c p.val)
              (clippedFlowProfileCuts 4096 bounds t c (p.val + 1)))) ≤ 448 := by
    let cuts : Col → Nat → Nat := clippedFlowProfileCuts 4096 bounds t
    let actual : Col → Nat := physicalCoreOutputProfile inputs t
    let ideal : Col → Nat := fun c => exactRankColumnHeight (physicalCoreInputMass inputs t) c
    have hlocal :
        (Finset.univ.sum fun c : Col => countDistance (actual c) (ideal c)) ≤ 448 := by
      simpa [actual, ideal, physicalCoreOutputProfile, physicalCoreInputMass] using
        physical_output_exact_rank_l1_le_448 (inputs t)
    have hpart := profile_port_cells_distance_le actual ideal ports cuts
      (by
        intro c
        have hz := (hvalid t).1 c
        simpa [cuts, clippedFlowProfileCuts] using hz)
      (by
        intro c
        have he := (hvalid t).2.1 c
        simpa [cuts, clippedFlowProfileCuts] using he)
      (by
        intro c i hi
        have hm := (hvalid t).2.2 c i hi
        simpa [cuts, clippedFlowProfileCuts] using hm)
      hlocal
    simpa [cuts, actual, ideal, clippedFlowProfileCuts] using hpart
  calc
    _ = Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun c : Col =>
            Finset.univ.sum fun p : Fin ports =>
              countDistance
                (prefixIntervalMass
                  (physicalCoreOutputProfile inputs t c)
                  (clippedFlowProfileCuts 4096 bounds t c p.val)
                  (clippedFlowProfileCuts 4096 bounds t c (p.val + 1)))
                (prefixIntervalMass
                  (exactRankColumnHeight (physicalCoreInputMass inputs t) c)
                  (clippedFlowProfileCuts 4096 bounds t c p.val)
                  (clippedFlowProfileCuts 4096 bounds t c (p.val + 1))) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Fintype.sum_prod_type'
            (fun c p => countDistance
              (clippedFlowProfileActualCountOfProfile 4096 bounds
                (physicalCoreOutputProfile inputs) t (c, p))
              (clippedFlowProfileRankCount 4096 bounds
                (physicalCoreInputMass inputs) t (c, p)))]
          rfl
    _ ≤ Finset.univ.sum fun _ : Fin tiles => (448 : Nat) := by
          apply Finset.sum_le_sum
          intro t ht
          exact htile t
    _ = 448 * tiles := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      omega

/-- The fixed physical core's local 448 provider composes with the general
clipped-flow transfer: arbitrary receiver tags cost only the incoming tile
mass error plus 448 per complete core tile. -/
theorem physicalCore_grouped_profile_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (inputs : Fin tiles → Wire → Bool)
    (bounds : Fin (ports + 1) → Nat)
    (idealTileMass : Fin tiles → Nat)
    (tag : Fin tiles → Prod Col (Fin ports) → J)
    (parentError : Nat)
    (hports : 0 < ports)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * 4096) * tiles)
    (hmono : ∀ i : Fin ports, bounds (Fin.castSucc i) ≤ bounds (Fin.succ i))
    (hI : ∀ t, idealTileMass t ≤ 262144)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (physicalCoreInputMass inputs t) (idealTileMass t)) ≤ parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (clippedFlowGroupedActualOfProfile 4096 bounds
          (physicalCoreOutputProfile inputs) tag j)
        (clippedFlowGroupedRank 4096 bounds idealTileMass tag j)) ≤
      parentError + 448 * tiles := by
  apply clipped_global_profile_error_le_parent_add_448_of_actual_profile
    (m := 4096) (bounds := bounds)
    (actualProfile := physicalCoreOutputProfile inputs)
    (tileMass := physicalCoreInputMass inputs)
    (idealTileMass := idealTileMass) (tag := tag) (parentError := parentError)
    hports (by omega) hfirst hlast hmono
    (by
      intro t
      dsimp [physicalCoreInputMass]
      calc
        _ ≤ (Finset.univ : Finset Wire).card := Finset.card_filter_le _ _
        _ = 262144 := by simp [Wire])
    hI
    (physicalCore_clipped_cells_error_le_448 inputs bounds hfirst hlast hmono)
    hMacroParent

/-- Group counts from independently cut physical columns into arbitrary
receivers. This is the schedule-facing form: each sender and each of its 64
columns may have its own monotone port boundaries. -/
noncomputable def physicalCoreVariableGroupedActual
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (inputs : Fin tiles → Wire → Bool)
    (cuts : Fin tiles → Col → Nat → Nat)
    (tag : Fin tiles → Prod Col (Fin ports) → J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      prefixIntervalMass (physicalCoreOutputProfile inputs x.1 x.2.1)
        (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))

/-- Exact rank reference for the same per-column port tags. -/
def physicalCoreVariableGroupedIdeal
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (idealTileMass : Fin tiles → Nat)
    (cuts : Fin tiles → Col → Nat → Nat)
    (tag : Fin tiles → Prod Col (Fin ports) → J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      prefixIntervalMass
        (exactRankColumnHeight (idealTileMass x.1) x.2.1)
        (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))

/-- Actual physical-core output profiles transfer to arbitrary receiver tags
with independent sender/column cuts. The only fresh cost is 448 per tile;
parent mass mismatch is charged once across the whole stage. -/
theorem physicalCore_variable_column_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (inputs : Fin tiles → Wire → Bool)
    (idealTileMass : Fin tiles → Nat)
    (cuts : Fin tiles → Col → Nat → Nat)
    (tag : Fin tiles → Prod Col (Fin ports) → J)
    (parentError : Nat)
    (hI : ∀ t, idealTileMass t ≤ 262144)
    (hzero : ∀ t c, cuts t c 0 = 0)
    (hend : ∀ t c, cuts t c ports = 4096)
    (hmono : ∀ t c i, i < ports → cuts t c i ≤ cuts t c (i + 1))
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (physicalCoreInputMass inputs t) (idealTileMass t)) ≤ parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (physicalCoreVariableGroupedActual inputs cuts tag j)
        (physicalCoreVariableGroupedIdeal idealTileMass cuts tag j)) ≤
      parentError + 448 * tiles := by
  let I := Prod (Fin tiles) (Prod Col (Fin ports))
  let actual : I → Nat := fun x =>
    prefixIntervalMass (physicalCoreOutputProfile inputs x.1 x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let reference : I → Nat := fun x =>
    prefixIntervalMass
      (exactRankColumnHeight (physicalCoreInputMass inputs x.1) x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let ideal : I → Nat := fun x =>
    prefixIntervalMass (exactRankColumnHeight (idealTileMass x.1) x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let transfer : I → Nat := fun x => countDistance (actual x) (reference x)
  let group : I → J := fun x => tag x.1 x.2
  have hlocal (t : Fin tiles) :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          countDistance (actual (t, (c, p))) (reference (t, (c, p)))) ≤ 448 := by
    let actualCol : Col → Nat := physicalCoreOutputProfile inputs t
    let idealCol : Col → Nat := fun c =>
      exactRankColumnHeight (physicalCoreInputMass inputs t) c
    have hmass := physical_output_exact_rank_l1_le_448 (inputs t)
    have hmass' :
        (Finset.univ.sum fun c : Col => countDistance (actualCol c) (idealCol c)) ≤ 448 := by
      simpa [actualCol, idealCol, physicalCoreOutputProfile,
        physicalCoreInputMass] using hmass
    have hpart := profile_port_cells_distance_le actualCol idealCol ports
      (cuts t) (hzero t) (hend t) (fun c i hi => hmono t c i hi) hmass'
    simpa [I, actual, reference, actualCol, idealCol] using hpart
  have hTransfer : (Finset.univ.sum fun x : I => transfer x) ≤ 448 * tiles := by
    rw [Fintype.sum_prod_type' (fun t cell => transfer (t, cell))]
    calc
      _ ≤ Finset.univ.sum fun _ : Fin tiles => (448 : Nat) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Fintype.sum_prod_type' (fun c p => transfer (t, (c, p)))]
        exact hlocal t
      _ = 448 * tiles := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Nat.nsmul_eq_mul]
        ring
  have hParentTile (t : Fin tiles) :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          countDistance (reference (t, (c, p))) (ideal (t, (c, p)))) ≤
        countDistance (physicalCoreInputMass inputs t) (idealTileMass t) := by
    simpa [reference, ideal] using
      exactRankColumnPorts_distance_le_mass
        (physicalCoreInputMass inputs t) (idealTileMass t) 4096 ports (cuts t)
        (by
          dsimp [physicalCoreInputMass]
          calc
            _ ≤ (Finset.univ : Finset Wire).card := Finset.card_filter_le _ _
            _ = 262144 := by simp [Wire])
        (hI t) (hzero t) (hend t) (fun c i hi => hmono t c i hi)
  have hParent :
      (Finset.univ.sum fun x : I => countDistance (reference x) (ideal x)) ≤ parentError := by
    rw [Fintype.sum_prod_type' (fun t cell =>
      countDistance (reference (t, cell)) (ideal (t, cell)))]
    calc
      _ ≤ Finset.univ.sum fun t : Fin tiles =>
            countDistance (physicalCoreInputMass inputs t) (idealTileMass t) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Fintype.sum_prod_type' (fun c p =>
          countDistance (reference (t, (c, p))) (ideal (t, (c, p))))]
        exact hParentTile t
      _ ≤ parentError := hMacroParent
  have hUpper : ∀ x : I, actual x ≤ reference x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  have hLower : ∀ x : I, reference x ≤ actual x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  calc
    _ ≤ parentError + Finset.univ.sum fun x : I => transfer x := by
      have hgrouped := grouped_child_rank_error_le_parent_add_transfer
        group actual reference ideal transfer parentError hUpper hLower hParent
      change (Finset.univ.sum fun j : J =>
        countDistance
          ((Finset.univ.filter fun x : I => group x = j).sum actual)
          ((Finset.univ.filter fun x : I => group x = j).sum ideal)) ≤ _
      exact hgrouped
    _ ≤ parentError + 448 * tiles := Nat.add_le_add_left hTransfer _

end Chvatal.D2PhysicalProfileGlobalTransfer
