import D2RowMajorFlowCuts

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

open scoped BigOperators
open Chvatal.D2RowMajorFlowCuts
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2RankAlignment

namespace Chvatal.D2ClippedFlowProfileTransfer

abbrev Col := Fin 64

theorem exactRankColumnHeight_eq_offset (H : Nat) (c : Col) :
    exactRankColumnHeight H c = (H + 63 - c.val) / 64 := by
  unfold exactRankColumnHeight
  have hc : c.val < 64 := c.isLt
  have hr : H % 64 < 64 := Nat.mod_lt H (by omega)
  have hdecomp : H = 64 * (H / 64) + H % 64 := by omega
  by_cases hcr : c.val < H % 64
  · simp [hcr]
    omega
  · simp [hcr]
    omega

/-- The exact rank profile distributes the first `H` positions among the
64 columns with exactly `H` total mass. -/
theorem exactRankColumnHeight_sum (H : Nat) (hH : H <= 64 * 4096) :
    (Finset.univ.sum fun c : Col => exactRankColumnHeight H c) = H := by
  let q := H / 64
  let r := H % 64
  have hr : r < 64 := by dsimp [r]; exact Nat.mod_lt _ (by omega)
  have hcount : (Finset.univ.sum fun c : Col =>
      if c.val < r then 1 else 0) = r := by
    have hcard : (Finset.univ.filter fun c : Col => c.val < r).card = r := by
      rw [show (Finset.univ.filter fun c : Col => c.val < r) =
        Finset.Iio (Fin.mk r hr) by
          ext c
          simp [Finset.mem_Iio, Fin.lt_def]]
      simp
    simpa using hcard
  calc
    (Finset.univ.sum fun c : Col => exactRankColumnHeight H c) =
        64 * q + r := by
      simp [exactRankColumnHeight, q, r, Finset.sum_add_distrib, hcount]
    _ = H := by dsimp [q, r]; omega

/-- Two exact row-major rank prefixes induce nested column profiles, so the
l1 distance between those profiles is exactly the difference in their total
masses. -/
theorem exactRankColumnHeight_l1_distance (H K : Nat)
    (hH : H <= 64 * 4096) (hK : K <= 64 * 4096) :
    (Finset.univ.sum fun c : Col =>
      countDistance (exactRankColumnHeight H c) (exactRankColumnHeight K c)) =
        countDistance H K := by
  by_cases hHK : H <= K
  · have hprofile (c : Col) : exactRankColumnHeight H c <=
        exactRankColumnHeight K c := by
      rw [exactRankColumnHeight_eq_offset, exactRankColumnHeight_eq_offset]
      apply Nat.div_le_div_right
      omega
    have hsumH := exactRankColumnHeight_sum H hH
    have hsumK := exactRankColumnHeight_sum K hK
    have hdiff : (Finset.univ.sum fun c : Col =>
        exactRankColumnHeight K c - exactRankColumnHeight H c) = K - H := by
      rw [Finset.sum_tsub_distrib Finset.univ (by
        intro c hc
        exact hprofile c)]
      rw [hsumK, hsumH]
    calc
      _ = Finset.univ.sum fun c : Col =>
          exactRankColumnHeight K c - exactRankColumnHeight H c := by
        apply Finset.sum_congr rfl
        intro c hc
        unfold countDistance
        rw [Nat.sub_eq_zero_of_le (hprofile c)]
        simp
      _ = K - H := hdiff
      _ = countDistance H K := by
        unfold countDistance
        rw [Nat.sub_eq_zero_of_le hHK]
        simp
  · have hKH : K <= H := by omega
    have hprofile (c : Col) : exactRankColumnHeight K c <=
        exactRankColumnHeight H c := by
      rw [exactRankColumnHeight_eq_offset, exactRankColumnHeight_eq_offset]
      apply Nat.div_le_div_right
      omega
    have hsumH := exactRankColumnHeight_sum H hH
    have hsumK := exactRankColumnHeight_sum K hK
    have hdiff : (Finset.univ.sum fun c : Col =>
        exactRankColumnHeight H c - exactRankColumnHeight K c) = H - K := by
      rw [Finset.sum_tsub_distrib Finset.univ (by
        intro c hc
        exact hprofile c)]
      rw [hsumH, hsumK]
    calc
      _ = Finset.univ.sum fun c : Col =>
          exactRankColumnHeight H c - exactRankColumnHeight K c := by
        apply Finset.sum_congr rfl
        intro c hc
        unfold countDistance
        rw [Nat.sub_eq_zero_of_le (hprofile c)]
        simp
      _ = H - K := hdiff
      _ = countDistance H K := by
        unfold countDistance
        have hnot : Not (H <= K) := hHK
        omega

/-- Splitting each exact-rank column profile into arbitrary monotone row
ports cannot increase its l1 discrepancy beyond the original tile-mass
discrepancy. This is the parent-error transfer for the full spatial profile. -/
theorem exactRankColumnPorts_distance_le_mass
    (H K m ports : Nat) (cuts : Col -> Nat -> Nat)
    (hH : H <= 64 * 4096) (hK : K <= 64 * 4096)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = m)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1)) :
    (Finset.univ.sum fun c : Col =>
      Finset.univ.sum fun p : Fin ports =>
        countDistance
          (prefixIntervalMass (exactRankColumnHeight H c)
            (cuts c p.val) (cuts c (p.val + 1)))
          (prefixIntervalMass (exactRankColumnHeight K c)
            (cuts c p.val) (cuts c (p.val + 1)))) <= countDistance H K := by
  have hcolumn (c : Col) :
      (Finset.univ.sum fun p : Fin ports =>
        countDistance
          (prefixIntervalMass (exactRankColumnHeight H c)
            (cuts c p.val) (cuts c (p.val + 1)))
          (prefixIntervalMass (exactRankColumnHeight K c)
            (cuts c p.val) (cuts c (p.val + 1)))) <=
        countDistance (exactRankColumnHeight H c) (exactRankColumnHeight K c) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      countDistance
        (prefixIntervalMass (exactRankColumnHeight H c)
          (cuts c i) (cuts c (i + 1)))
        (prefixIntervalMass (exactRankColumnHeight K c)
          (cuts c i) (cuts c (i + 1))))]
    exact prefixIntervalMass_partition_distance
      (exactRankColumnHeight H c) (exactRankColumnHeight K c)
      (cuts c) ports m (hzero c) (hend c)
      (fun i hi => hmono c i hi)
  calc
    _ <= Finset.univ.sum fun c : Col =>
        countDistance (exactRankColumnHeight H c) (exactRankColumnHeight K c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcolumn c
    _ = countDistance H K := exactRankColumnHeight_l1_distance H K hH hK

theorem sum_abs_identity_fibers {I : Type*} [Fintype I] [DecidableEq I]
    (error : I -> Rat) :
    (Finset.univ.sum fun j : I =>
      abs ((Finset.univ.filter fun i : I => i = j).sum error)) =
        Finset.univ.sum fun i : I => abs (error i) := by
  have hfiber (j : I) :
      Finset.univ.filter (fun i : I => i = j) = {j} := by
    ext i
    simp
  calc
    _ = Finset.univ.sum fun j : I => abs (error j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hfiber j]
      simp
    _ = Finset.univ.sum fun i : I => abs (error i) := rfl

def clippedFlowProfileCuts {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (c : Col) (i : Nat) : Nat :=
  rowMajorFlowCutsM (m := m) (clippedTileFlowBounds m bounds t) c i

def clippedFlowProfileActualCount {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat) (t : Fin tiles)
    (cell : Prod Col (Fin ports)) : Nat :=
  prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) cell.1)
    (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
    (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1))

/-- Actual receiver-cell counts for an arbitrary physical output column
profile. This separates the global clipping/rebatching argument from the
particular local network used to generate the profile. -/
def clippedFlowProfileActualCountOfProfile {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (actualProfile : Fin tiles -> Col -> Nat) (t : Fin tiles)
    (cell : Prod Col (Fin ports)) : Nat :=
  prefixIntervalMass (actualProfile t cell.1)
    (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
    (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1))

def clippedFlowProfileRankCount {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (tileMass : Fin tiles -> Nat) (t : Fin tiles)
    (cell : Prod Col (Fin ports)) : Nat :=
  prefixIntervalMass (exactRankColumnHeight (tileMass t) cell.1)
    (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
    (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1))

/-- The parent-mass discrepancy for one tile controls the full refined
column/port reference profile after global boundaries are clipped to it. -/
theorem clippedFlowProfile_parent_error_per_tile
    {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat) (t : Fin tiles)
    (H K : Nat) (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hH : H <= 262144) (hK : K <= 262144) :
    (Finset.univ.sum fun c : Col =>
      Finset.univ.sum fun p : Fin ports =>
        countDistance
          (prefixIntervalMass (exactRankColumnHeight H c)
            (clippedFlowProfileCuts m bounds t c p.val)
            (clippedFlowProfileCuts m bounds t c (p.val + 1)))
          (prefixIntervalMass (exactRankColumnHeight K c)
            (clippedFlowProfileCuts m bounds t c p.val)
            (clippedFlowProfileCuts m bounds t c (p.val + 1)))) <=
      countDistance H K := by
  have hclip := clippedTileFlowBounds_valid m bounds t hfirst hlast hmono
  have hcuts := rowMajorFlowCutsM_valid
    (clippedTileFlowBounds m bounds t) hclip.1 hclip.2.1 hclip.2.2
  have hresult := exactRankColumnPorts_distance_le_mass
    H K m ports (clippedFlowProfileCuts m bounds t)
    hH hK (fun c => hcuts.1 c) (fun c => hcuts.2.1 c)
    (fun c i hi => hcuts.2.2 c i hi)
  exact hresult

def clippedFlowGroupedActual {ports tiles : Nat} {J : Type*}
    [DecidableEq J] (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      clippedFlowProfileActualCount m bounds sourceHeight x.1 x.2

def clippedFlowGroupedActualOfProfile {ports tiles : Nat} {J : Type*}
    [DecidableEq J] (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (actualProfile : Fin tiles -> Col -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      clippedFlowProfileActualCountOfProfile m bounds actualProfile x.1 x.2

def clippedFlowGroupedRank {ports tiles : Nat} {J : Type*}
    [DecidableEq J] (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      clippedFlowProfileRankCount m bounds idealTileMass x.1 x.2

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

theorem countDistance_rat_eq_abs_for_profiles (a b : Nat) :
    (countDistance a b : Rat) = abs ((a : Rat) - (b : Rat)) :=
  countDistance_rat_eq_abs a b

/-- Clipping one global rank partition into partial tiles preserves the local
448 error bound on the entire 64-column profile, not only on the tile total. -/
theorem clipped_global_core_profile_error_le_448_per_tile
    {ports tiles : Nat} (m : Nat)
    (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass : Fin tiles -> Nat)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c) :
    (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs ((prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) cell.1)
          (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
          (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1)) : Rat) -
        prefixIntervalMass (exactRankColumnHeight (tileMass t) cell.1)
          (clippedFlowProfileCuts m bounds t cell.1 cell.2.val)
          (clippedFlowProfileCuts m bounds t cell.1 (cell.2.val + 1)))) <=
        448 * tiles := by
  have hvalid (t : Fin tiles) := by
    have hclip := clippedTileFlowBounds_valid m bounds t hfirst hlast hmono
    exact rowMajorFlowCutsM_valid (clippedTileFlowBounds m bounds t)
      hclip.1 hclip.2.1 hclip.2.2
  calc
    _ <= Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
      apply Finset.sum_le_sum
      intro t ht
      let cuts : Col -> Nat -> Nat := clippedFlowProfileCuts m bounds t
      have hlocal := fullHeightTwoShuffle_partial_rows_rebinned_l1_le_448
        (sourceHeight t) cuts ports m (tileMass t) id hports hm
        (fun c => (hvalid t).1 c)
        (fun c => (hvalid t).2.1 c)
        (fun c i hi => (hvalid t).2.2 c i hi)
        (hinput t) (hHsum t)
      have hidentity := sum_abs_identity_fibers
        (fun cell : Prod Col (Fin ports) =>
          (prefixIntervalMass (fullHeightTwoShuffle (sourceHeight t) cell.1)
            (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
          prefixIntervalMass (exactRankColumnHeight (tileMass t) cell.1)
            (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)))
      have hlocal' :
          (Finset.univ.sum fun j : Prod Col (Fin ports) =>
            abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
              cell = j).sum fun cell =>
                (prefixIntervalMass
                    (fullHeightTwoShuffle (sourceHeight t) cell.1)
                    (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
                  prefixIntervalMass (exactRankColumnHeight (tileMass t) cell.1)
                    (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)))) <= 448 := by
        exact hlocal
      exact hidentity.symm.trans_le hlocal'
    _ = 448 * tiles := by norm_num [Rat.mul_comm]

/-- Full spatial rank-profile transfer for a clipped global partition. The
parent mass mismatch is charged once, each partial fixed-core tile contributes
448 fresh error, and arbitrary tile/column/port cells may be grouped into the
actual next receiver labels. -/
theorem clipped_global_profile_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports) (hm : m <= 4096)
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
        (clippedFlowGroupedActual m bounds sourceHeight tag j)
        (clippedFlowGroupedRank m bounds idealTileMass tag j)) <=
      parentError + 448 * tiles := by
  let actual : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileActualCount m bounds sourceHeight x.1 x.2
  let reference : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds tileMass x.1 x.2
  let ideal : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds idealTileMass x.1 x.2
  let transfer : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    countDistance (actual x) (reference x)
  let group : Prod (Fin tiles) (Prod Col (Fin ports)) -> J := fun x => tag x.1 x.2
  have hlocalRat := clipped_global_core_profile_error_le_448_per_tile
    m bounds sourceHeight tileMass hports hm hfirst hlast hmono hinput hHsum
  have hlocalRat' :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          abs ((actual (t, cell) : Rat) - (reference (t, cell) : Rat))) <=
        448 * tiles := by
    simpa [actual, reference, clippedFlowProfileActualCount,
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
      _ <= parentError := by
        simpa [reference, ideal] using hparentNested
  have hTransferProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
        transfer x) <= 448 * tiles := by
    rw [Fintype.sum_prod_type'
      (fun t cell => transfer (t, cell))]
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

/-- Physical-profile form of the clipped global transfer. A local network may
produce any column-count profile, provided its clipped per-cell error against
the exact tile-rank profile sums to at most 448. Arbitrary receiver tags can
then group the cells while charging parent tile-mass mismatch only once. -/
theorem clipped_global_profile_error_le_parent_add_448_of_actual_profile
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (actualProfile : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports) (hm : m <= 4096)
    (hfirst : bounds 0 = 0)
    (hlast : bounds (Fin.last ports) = (64 * m) * tiles)
    (hmono : forall i : Fin ports,
      bounds (Fin.castSucc i) <= bounds (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hlocal : (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        countDistance
          (clippedFlowProfileActualCountOfProfile m bounds actualProfile t cell)
          (clippedFlowProfileRankCount m bounds tileMass t cell)) <= 448 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (clippedFlowGroupedActualOfProfile m bounds actualProfile tag j)
        (clippedFlowGroupedRank m bounds idealTileMass tag j)) <=
      parentError + 448 * tiles := by
  let actual : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileActualCountOfProfile m bounds actualProfile x.1 x.2
  let reference : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds tileMass x.1 x.2
  let ideal : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    clippedFlowProfileRankCount m bounds idealTileMass x.1 x.2
  let transfer : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    countDistance (actual x) (reference x)
  let group : Prod (Fin tiles) (Prod Col (Fin ports)) -> J := fun x => tag x.1 x.2
  have hlocalNat : (Finset.univ.sum fun t : Fin tiles =>
      Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        countDistance (actual (t, cell)) (reference (t, cell))) <= 448 * tiles := by
    simpa [actual, reference] using hlocal
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
      _ <= parentError := hparentNested
  have hTransferProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
        transfer x) <= 448 * tiles := by
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

/-- The full spatial profile recurrence preserves the `512` error allowance
per tile when the next profile has twice as many tiles. -/
theorem clipped_global_profile_error_le_next_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat) (bounds : Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (hports : 0 < ports) (hm : m <= 4096)
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
        (clippedFlowGroupedActual m bounds sourceHeight tag j)
        (clippedFlowGroupedRank m bounds idealTileMass tag j)) <=
      512 * outputTiles := by
  have hstep := clipped_global_profile_error_le_parent_add_448
    m bounds sourceHeight tileMass idealTileMass tag (512 * tiles)
    hports hm hfirst hlast hmono hH hI hinput hHsum hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 512 * tiles + 448 * tiles := hstep
    _ <= 512 * tiles + 512 * tiles := by omega
    _ = 512 * (2 * tiles) := by ring

end Chvatal.D2ClippedFlowProfileTransfer
