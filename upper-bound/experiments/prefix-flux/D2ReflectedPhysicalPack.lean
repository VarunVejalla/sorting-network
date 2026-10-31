import D2PhysicalPackTwoGrid
import D2Slope35Physical4096

open Chvatal.D2Slope35Physical4096
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2BandRepair4096Network
open Chvatal.D2RankAlignment
open Chvatal.D2Slope25Physical

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Chvatal.D2ReflectedPhysicalPack

abbrev Wire := Fin (4096 * 64)
abbrev Col := Fin 64
abbrev Row := Fin 4096

def reverseRowsPerm : Equiv.Perm Wire :=
  (matrixWireEquiv (by omega)).symm.trans
    ((Equiv.prodCongr reverseRowEquiv (Equiv.refl Col)).trans
      (matrixWireEquiv (by omega)))

theorem reverseRowsPerm_matrixWire (r : Row) (c : Col) :
    reverseRowsPerm (matrixWire 4096 64 r c) =
      matrixWire 4096 64 (reverseRowEquiv r) c := by
  simp [reverseRowsPerm, matrixWireEquiv, matrixWire_row_col]

def reverseRowScramble (sigma : Chvatal.Scramble 4096 64) :
    Chvatal.Scramble 4096 64 :=
  fun r => sigma (reverseRowEquiv r)

def reverseAffine25 (r : Row) : Equiv.Perm Col :=
  lift35Equiv.symm.trans (affine25 (reverseRowEquiv r))

def reflectedSigma35 : Chvatal.Scramble 4096 64 :=
  reverseRowScramble scramble35

def reflectedSigma25 : Chvatal.Scramble 4096 64 :=
  reverseAffine25

theorem matrixColumnTrueCount_reverseRows (v : Wire -> Bool) (d : Col) :
    matrixColumnTrueCount d (Function.comp v reverseRowsPerm) =
      matrixColumnTrueCount d v := by
  classical
  unfold matrixColumnTrueCount
  change (Finset.univ.filter fun r : Row =>
      v (reverseRowsPerm (matrixWire 4096 64 r d)) = true).card = _
  refine Finset.card_bij (fun r _ => reverseRowEquiv r) ?_ ?_ ?_
  case refine_1 =>
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change v (reverseRowsPerm (matrixWire 4096 64 r d)) = true at hr
    rw [reverseRowsPerm_matrixWire] at hr
    exact hr
  case refine_2 =>
    intro a ha b hb hab
    exact reverseRowEquiv.injective hab
  case refine_3 =>
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine Exists.intro (reverseRowEquiv r) ?_
    constructor
    case h =>
      exact reverseRowEquiv.left_inv r
    case w =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [reverseRowsPerm_matrixWire]
      have hrev : reverseRowEquiv (reverseRowEquiv r) = r :=
        reverseRowEquiv.left_inv r
      rw [hrev]
      exact hr

theorem bottomUnaryProfile_trueCount (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    matrixColumnTrueCount d (bottomUnaryProfile h) = h d := by
  classical
  unfold Chvatal.matrixColumnTrueCount
  have hfun : (fun r : Row =>
      bottomUnaryProfile h (matrixWire 4096 64 r d) = true) =
      (fun r : Row => 4096 - h d <= r.val) := by
    funext r
    simp [bottomUnaryProfile, matrixWire_row_col]
  have hset : (Finset.univ.filter fun r : Row =>
      bottomUnaryProfile h (matrixWire 4096 64 r d) = true) =
      (Finset.univ.filter fun r : Row => 4096 - h d <= r.val) := by
    ext r
    simp [hfun]
  rw [hset]
  by_cases hz : h d = 0
  case pos =>
    have hEmpty : (Finset.univ.filter fun r : Row => 4096 - h d <= r.val) = (∅ : Finset Row) := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [hz, Nat.sub_zero] at hr
      exact Nat.not_le_of_gt r.isLt hr
    rw [hEmpty]
    simp [hz]
  case neg =>
    have hpos : 0 < h d := Nat.pos_of_ne_zero hz
    have hlo : 4096 - h d < 4096 := by omega
    have hfilter : (Finset.univ.filter fun r : Row => 4096 - h d <= r.val) =
        Finset.Ici (Fin.mk (4096 - h d) hlo) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ici, Fin.le_iff_val_le_val]
    rw [hfilter]
    have hhd := hbound d
    simp
    omega

theorem reflectedSigma35Input_eq (h : Col -> Nat) :
    Function.comp (bottomUnaryProfile h)
        (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma35).symm =
      Function.comp (scrambledTopPrefix h) reverseRowsPerm := by
  funext w
  let r := matrixRow 4096 64 (by omega) w
  let d := matrixCol 4096 64 (by omega) w
  have hw : w = matrixWire 4096 64 r d :=
    (matrixWire_matrixRow_col (by omega) w).symm
  rw [hw]
  unfold scrambledTopPrefix
  simp only [Function.comp_apply]
  rw [reverseRowsPerm_matrixWire]
  rw [rowScrambleWirePerm_symm_apply, rowScrambleWirePerm_symm_apply]
  simp [topPrefix, bottomUnaryProfile, reflectedSigma35, reverseRowScramble,
    scramble35, matrixWire_row_col]
  have hr := r.isLt
  have hrev : (reverseRowEquiv r).val = 4095 - r.val := by
    simp [reverseRowEquiv]
  omega

theorem reflectedSigma25Input_eq (h : Col -> Nat) :
    Function.comp (bottomUnaryProfile h)
        (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma25).symm =
      Function.comp (scrambledTopPrefix25 (reindexed35Height h)) reverseRowsPerm := by
  funext w
  let r := matrixRow 4096 64 (by omega) w
  let d := matrixCol 4096 64 (by omega) w
  have hw : w = matrixWire 4096 64 r d :=
    (matrixWire_matrixRow_col (by omega) w).symm
  rw [hw]
  unfold scrambledTopPrefix25
  simp only [Function.comp_apply]
  rw [reverseRowsPerm_matrixWire]
  rw [rowScrambleWirePerm_symm_apply, rowScrambleWirePerm_symm_apply]
  simp [topPrefix, bottomUnaryProfile, reflectedSigma25, reverseAffine25,
    reindexed35Height, matrixWire_row_col, affine25, lift35Equiv]
  have hr := r.isLt
  have hrev : (reverseRowEquiv r).val = 4095 - r.val := by
    simp [reverseRowEquiv]
  omega

theorem reflectedSigma35Sort_counts (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    matrixColumnTrueCount d
      (Function.comp (bottomUnaryProfile h)
        (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma35).symm) =
      slope35PhysicalOutputHeight h d := by
  rw [reflectedSigma35Input_eq, matrixColumnTrueCount_reverseRows]
  exact column_count_eq_physical_output_height h hbound d

theorem reflectedSigma25Sort_counts (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    matrixColumnTrueCount d
      (Function.comp (bottomUnaryProfile h)
        (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma25).symm) =
      slope25PhysicalOutputHeight (reindexed35Height h) d := by
  rw [reflectedSigma25Input_eq, matrixColumnTrueCount_reverseRows]
  have hbound' : forall c, reindexed35Height h c <= 4096 := by
    intro c
    exact hbound (liftSlope35Destination c)
  exact column_count25_eq_physical_output_height
    (reindexed35Height h) hbound' d

theorem reflectedThreeSortProfile (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) :
    Chvatal.semanticExec2 (by omega) reflectedSigma35 reflectedSigma25 v =
      bottomUnaryProfile
        (slope25PhysicalOutputHeight
          (reindexed35Height (slope35PhysicalOutputHeight h))) := by
  have hsort1 :
      (columnSortNetwork 4096 64 (by omega)).exec
        (Function.comp (bottomUnaryProfile h)
          (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma35).symm) =
      bottomUnaryProfile (slope35PhysicalOutputHeight h) := by
    apply columnSort_exec_eq_bottomUnaryProfile
    exact reflectedSigma35Sort_counts h hbound
  have hbound1 : forall c, slope35PhysicalOutputHeight h c <= 4096 := by
    intro c
    calc
      slope35PhysicalOutputHeight h c =
          matrixColumnTrueCount c (scrambledTopPrefix h) :=
        (column_count_eq_physical_output_height h hbound c).symm
      _ <= 4096 := matrixColumnTrueCount_le c _
  have hsort2 :
      (columnSortNetwork 4096 64 (by omega)).exec
        (Function.comp (bottomUnaryProfile (slope35PhysicalOutputHeight h))
          (rowScrambleWirePerm 4096 64 (by omega) reflectedSigma25).symm) =
      bottomUnaryProfile
        (slope25PhysicalOutputHeight
          (reindexed35Height (slope35PhysicalOutputHeight h))) := by
    apply columnSort_exec_eq_bottomUnaryProfile
    intro d
    exact reflectedSigma25Sort_counts (slope35PhysicalOutputHeight h) hbound1 d
  unfold Chvatal.semanticExec2 Chvatal.semanticExec
  rw [columnSort_exec_eq_bottomUnaryProfile v h hcount, hsort1, hsort2]

def reflectedCombinedSigma : Chvatal.Scramble 4096 64 :=
  fun r => reflectedSigma25 r * reflectedSigma35 r

theorem reflectedRowScrambleWirePerm2_eq :
    Chvatal.rowScrambleWirePerm2 4096 64 (by omega)
        reflectedSigma35 reflectedSigma25 =
      Chvatal.rowScrambleWirePerm 4096 64 (by omega) reflectedCombinedSigma := by
  apply Equiv.ext
  intro w
  let r := matrixRow 4096 64 (by omega) w
  let d := matrixCol 4096 64 (by omega) w
  have hw : w = matrixWire 4096 64 r d :=
    (matrixWire_matrixRow_col (by omega) w).symm
  rw [hw]
  unfold Chvatal.rowScrambleWirePerm2
  rw [Equiv.Perm.mul_apply]
  rw [Chvatal.rowScrambleWirePerm_apply, Chvatal.rowScrambleWirePerm_apply,
    Chvatal.rowScrambleWirePerm_apply]
  rfl

theorem reflectedPhysicalPack2Exec (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) :
    (Chvatal.physicalPack2Net 4096 64 (by omega)
      reflectedSigma35 reflectedSigma25).exec v =
      Function.comp (bottomUnaryProfile (fullHeightTwoShuffle h))
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) reflectedCombinedSigma) := by
  rw [Chvatal.physicalPack2Net_exec, reflectedThreeSortProfile v h hcount hbound,
    reflectedRowScrambleWirePerm2_eq]
  rfl

/-- The physical two-shuffle core's output profile is determined directly by
an arbitrary Boolean input: its source heights are the actual per-column
counts. This removes the external profile-realization premise when the core
is instantiated on a concrete D2 sender. -/
theorem reflectedPhysicalPack2Exec_of_input (v : Wire -> Bool) :
    (Chvatal.physicalPack2Net 4096 64 (by omega)
      reflectedSigma35 reflectedSigma25).exec v =
      Function.comp
        (bottomUnaryProfile
          (fullHeightTwoShuffle (fun c => matrixColumnTrueCount c v)))
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega)
          reflectedCombinedSigma) := by
  apply reflectedPhysicalPack2Exec
    v (fun c => matrixColumnTrueCount c v)
  · intro c
    rfl
  · intro c
    exact matrixColumnTrueCount_le c v

theorem fullHeightAfterRowPermutation_eq_comp (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col) :
    fullHeightAfterRowPermutation h perm =
      Function.comp (bottomUnaryProfile (fullHeightTwoShuffle h))
        (rowScrambleWirePerm 4096 64 (by omega) perm) := by
  funext w
  let r := matrixRow 4096 64 (by omega) w
  let d := matrixCol 4096 64 (by omega) w
  have hw : w = matrixWire 4096 64 r d :=
    (matrixWire_matrixRow_col (by omega) w).symm
  rw [hw]
  simp only [fullHeightAfterRowPermutation, Function.comp_apply]
  rw [rowScrambleWirePerm_symm_apply, rowScrambleWirePerm_apply]
  simp

theorem reflectedPhysicalPackTwoGridInput (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) :
    (Chvatal.physicalPack2Net 4096 64 (by omega)
      reflectedSigma35 reflectedSigma25).exec v =
      fullHeightAfterRowPermutation h reflectedCombinedSigma := by
  rw [reflectedPhysicalPack2Exec v h hcount hbound,
    fullHeightAfterRowPermutation_eq_comp]

theorem reflectedPhysicalPackTwoGrid_exec (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) :
    (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
      reflectedSigma35 reflectedSigma25).exec v =
      Chvatal.D2BandRepair4096Network.twoGridRepair.exec
        (fullHeightAfterRowPermutation h reflectedCombinedSigma) := by
  unfold Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
  unfold ComparatorNetwork.append
  rw [ComparatorNetwork.exec_append, reflectedPhysicalPackTwoGridInput v h hcount hbound]

theorem reflectedPhysicalPackTwoGrid_columnMonotone (v : Wire -> Bool)
    (h : Col -> Nat) (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) (c : Col) :
    Monotone (fun r : Row =>
      (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
        reflectedSigma35 reflectedSigma25).exec v (matrixWire 4096 64 r c)) := by
  rw [reflectedPhysicalPackTwoGrid_exec v h hcount hbound]
  exact physical_twoGridRepair_restores_columnMonotone h hbound
    reflectedCombinedSigma c

theorem reflectedPhysicalPackTwoGrid_common_band (v : Wire -> Bool)
    (h : Col -> Nat) (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) :
    exists a b, 64 * (b - a) <= 832 /\ a <= b /\
      64 * a <= 4096 * 64 /\ 64 * b <= 4096 * 64 /\
      (forall w : Wire, w.val < 64 * a ->
        (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v w = false) /\
      (forall w : Wire, 64 * b <= w.val ->
        (Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v w = true) := by
  rw [reflectedPhysicalPackTwoGrid_exec v h hcount hbound]
  exact physical_twoGridRepair_common_wire_band h hbound reflectedCombinedSigma

/-- The physical common-band output has column counts in an interval of at
most 13 rows. This remains true after the row-dependent physical permutation,
and is the range input needed for a physical exact-rank profile bound. -/
theorem reflectedPhysicalPackTwoGrid_columnCount_range_le_13
    (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096) (c d : Col) :
    matrixColumnTrueCount c
        ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v) <=
      matrixColumnTrueCount d
        ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v) + 13 := by
  let net := Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    reflectedSigma35 reflectedSigma25
  let out := net.exec v
  obtain ⟨a, b, hwidth, hab, ha, hb, hbelow, habove⟩ :=
    reflectedPhysicalPackTwoGrid_common_band v h hcount hbound
  have hrows : b - a <= 13 := by omega
  have haBound : a <= 4096 := by omega
  have hbBound : b <= 4096 := by omega
  have hcm : Chvatal.ColumnMonotoneInput 4096 64 (by omega) out := by
    intro j r s hrs
    change out (Chvatal.matrixWire 4096 64 r j) <=
      out (Chvatal.matrixWire 4096 64 s j)
    exact (reflectedPhysicalPackTwoGrid_columnMonotone
      v h hcount hbound j) hrs
  have hcountLower (j : Col) : 4096 - b <= matrixColumnTrueCount j out := by
    by_cases hbTop : b < 4096
    · let r : Row := ⟨b, hbTop⟩
      have hwire : (Chvatal.matrixWire 4096 64 r j).val >= 64 * b := by
        change 64 * b <= r.val * 64 + j.val
        simp [r]
        omega
      have hone := habove (Chvatal.matrixWire 4096 64 r j) hwire
      have hone' : out (Chvatal.matrixWire 4096 64 r j) = true := by
        simpa [out, net] using hone
      have hiff := Chvatal.colMono_true_iff (by omega) hcm r j
      rw [hone'] at hiff
      have hval : 4096 - r.val <= matrixColumnTrueCount j out := hiff.mp rfl
      omega
    · have : b = 4096 := by omega
      simp [this]
  have hcountUpper (j : Col) : matrixColumnTrueCount j out <= 4096 - a := by
    by_cases haPos : 0 < a
    · let r : Row := ⟨a - 1, by omega⟩
      have hwire : (Chvatal.matrixWire 4096 64 r j).val < 64 * a := by
        change r.val * 64 + j.val < 64 * a
        simp [r]
        omega
      have hzero := hbelow (Chvatal.matrixWire 4096 64 r j) hwire
      have hzero' : out (Chvatal.matrixWire 4096 64 r j) = false := by
        simpa [out, net] using hzero
      have hiff := Chvatal.colMono_true_iff (by omega) hcm r j
      rw [hzero'] at hiff
      have hnot : ¬ (4096 - r.val <= matrixColumnTrueCount j out) := by
        intro hh
        cases hiff.mpr hh
      simp [r] at hnot
      omega
    · have : a = 0 := by omega
      simp [this]
      exact matrixColumnTrueCount_le j out
  have hcUpper := hcountUpper c
  have hdLower := hcountLower d
  change matrixColumnTrueCount c out <= matrixColumnTrueCount d out + 13
  omega

/-- A zero-sum signed profile on 64 cells whose pairwise range is at most 14
has l1 norm at most 448. The proof bounds its second moment by Popoviciu's
interval estimate and then applies Cauchy-Schwarz. -/
theorem sum_abs_int_le_448_of_zero_sum_range14
    (f : Col -> Int)
    (hsum : (Finset.univ.sum fun c : Col => f c) = 0)
    (hrange : forall c d : Col, f c <= f d + 14) :
    (Finset.univ.sum fun c : Col => |f c|) <= 448 := by
  obtain ⟨cmin, hcmin, hmin⟩ := Finset.exists_min_image
    Finset.univ f (show Finset.univ.Nonempty from ⟨0, by simp⟩)
  obtain ⟨cmax, hcmax, hmax⟩ := Finset.exists_max_image
    Finset.univ f (show Finset.univ.Nonempty from ⟨0, by simp⟩)
  let a : Int := f cmin
  let b : Int := f cmax
  have ha : forall c : Col, a <= f c := by
    intro c
    exact hmin c (Finset.mem_univ c)
  have hb : forall c : Col, f c <= b := by
    intro c
    exact hmax c (Finset.mem_univ c)
  have hab : b - a <= 14 := by
    change f cmax - f cmin <= 14
    have := hrange cmax cmin
    omega
  have hsa : a <= 0 := by
    by_contra hnot
    have hapos : 0 < a := by omega
    have hsumLower : Finset.univ.sum (fun c : Col => a) <=
        Finset.univ.sum (fun c : Col => f c) :=
      Finset.sum_le_sum fun c hc => ha c
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Int.nsmul_eq_mul] at hsumLower
    rw [hsum] at hsumLower
    change (64 : Int) * a <= 0 at hsumLower
    nlinarith
  have hsb : 0 <= b := by
    by_contra hnot
    have hbneg : b < 0 := by omega
    have hsumUpper : Finset.univ.sum (fun c : Col => f c) <=
        Finset.univ.sum (fun c : Col => b) :=
      Finset.sum_le_sum fun c hc => hb c
    rw [hsum] at hsumUpper
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Int.nsmul_eq_mul] at hsumUpper
    change 0 <= (64 : Int) * b at hsumUpper
    nlinarith
  have hsquare : (Finset.univ.sum fun c : Col => (f c) ^ 2) <= 3136 := by
    have hpoint (c : Col) : (f c) ^ 2 <= (a + b) * f c - a * b := by
      have hprod : 0 <= (f c - a) * (b - f c) :=
        mul_nonneg (sub_nonneg.mpr (ha c)) (sub_nonneg.mpr (hb c))
      nlinarith
    have hsumPoint := Finset.sum_le_sum (s := Finset.univ)
      fun c hc => hpoint c
    have hformula : (Finset.univ.sum fun c : Col =>
        ((a + b) * f c - a * b)) = -(64 : Int) * a * b := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      simp only [mul_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Int.nsmul_eq_mul]
      ring
    rw [hformula] at hsumPoint
    have habNonneg : 0 <= b - a := by omega
    nlinarith [sq_nonneg (a + b), sq_nonneg (b - a)]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun c : Col => |f c|) (fun _ : Col => (1 : Int))
  have habsNonneg : 0 <= Finset.univ.sum (fun c : Col => |f c|) :=
    Finset.sum_nonneg fun c hc => abs_nonneg _
  have hnormsq : (Finset.univ.sum fun c : Col => |f c|) ^ 2 <= 448 ^ 2 := by
    have hsumAbsSq : (Finset.univ.sum fun c : Col => |f c| ^ 2) =
        Finset.univ.sum fun c : Col => (f c) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      exact sq_abs _
    have hcauchy' : (Finset.univ.sum fun c : Col => |f c|) ^ 2 <=
        (Finset.univ.sum fun c : Col => (f c) ^ 2) * 64 := by
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Int.nsmul_eq_mul] using hcauchy
    calc
      _ <= (Finset.univ.sum fun c : Col => (f c) ^ 2) * 64 := hcauchy'
      _ <= 3136 * 64 := by nlinarith
      _ = 448 ^ 2 := by norm_num
  nlinarith

end Chvatal.D2ReflectedPhysicalPack

