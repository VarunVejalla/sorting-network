import D2Slope25LiftProvider
import AKS.Chvatal.MatrixBridge
import AKS.Chvatal.SortedColumnDecode

open Chvatal
open Chvatal.D2RankAlignment
open Chvatal.D2Slope25Physical

set_option maxRecDepth 8192

namespace Chvatal.D2Slope35Physical4096

abbrev Col := Fin 64
abbrev Row := Fin 4096

def shift35 (r : Row) : Equiv.Perm Col where
  toFun c := Fin.mk ((c.val + 35 * r.val) % 64) (Nat.mod_lt _ (by omega))
  invFun c := Fin.mk ((c.val + 64 - (35 * r.val) % 64) % 64) (Nat.mod_lt _ (by omega))
  left_inv c := by
    apply Fin.ext
    dsimp
    omega
  right_inv c := by
    apply Fin.ext
    dsimp
    omega

def scramble35 : Scramble 4096 64 := shift35

def topPrefix (h : Col -> Nat) (w : Fin (4096 * 64)) : Bool :=
  decide ((matrixRow 4096 64 (by omega) w).val <
    h (matrixCol 4096 64 (by omega) w))

def scrambledTopPrefix (h : Col -> Nat) : Fin (4096 * 64) -> Bool :=
  Function.comp (topPrefix h) (rowScrambleWirePerm 4096 64 (by omega) scramble35).symm

theorem scrambledTopPrefix_matrixWire (h : Col -> Nat) (r : Row) (d : Col) :
    scrambledTopPrefix h (matrixWire 4096 64 r d) =
      decide (r.val < h ((shift35 r).symm d)) := by
  change topPrefix h
    ((rowScrambleWirePerm 4096 64 (by omega) scramble35).symm (matrixWire 4096 64 r d)) = _
  rw [rowScrambleWirePerm_symm_apply]
  simp [topPrefix, matrixWire_row_col, scramble35]

theorem column_count_eq_row_sum (h : Col -> Nat) (d : Col) :
    matrixColumnTrueCount d (scrambledTopPrefix h) =
      (Finset.univ.filter fun r : Row =>
        r.val < h ((shift35 r).symm d)).card := by
  unfold matrixColumnTrueCount
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [scrambledTopPrefix_matrixWire]
  simp

theorem residue_hits_eq_finRows (h : Col -> Nat) (hbound : forall c, h c <= 4096)
    (d c : Col) :
    residueHits64 (h c) (slope35RowAt d c).val =
      (Finset.univ.filter fun r : Row =>
        And (r.val < h c) (shift35 r c = d)).card := by
  classical
  unfold residueHits64
  refine Finset.card_bij (fun i hi => Fin.mk i (by
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact lt_of_lt_of_le hi.1 (hbound c))) ?_ ?_ ?_
  case refine_1 =>
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro hi.1 (by
      have heq := (slope35_row_destination_iff_residue c d i).mpr hi.2
      apply Fin.ext
      dsimp [shift35]
      exact heq)
  case refine_2 =>
    intro i hi j hj hij
    exact congrArg Fin.val hij
  case refine_3 =>
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    have hmod : r.val % 64 = (slope35RowAt d c).val :=
      (slope35_row_destination_iff_residue c d r.val).mp (by
        have heq := congrArg Fin.val hr.2
        simpa [shift35] using heq)
    have hmem : Membership.mem ((Finset.range (h c)).filter
        (fun i => i % 64 = (slope35RowAt d c).val)) r.val :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hr.1) hmod)
    have heq : Fin.mk r.val (by omega : r.val < 4096) = r := by
      apply Fin.ext
      rfl
    exact Exists.intro r.val (Exists.intro hmem heq)


lemma univ_filter_card_eq_sum (p : Row -> Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      Finset.univ.sum (fun r : Row => if p r then 1 else 0) := by
  rw [Finset.card_filter]

lemma source_indicator_sum (h : Col -> Nat) (r : Row) (d : Col) :
    (Finset.univ.sum fun c : Col =>
      if And (r.val < h c) (shift35 r c = d) then 1 else 0) =
      if r.val < h ((shift35 r).symm d) then 1 else 0 := by
  classical
  let c0 := (shift35 r).symm d
  calc
    (Finset.univ.sum fun c : Col =>
        if And (r.val < h c) (shift35 r c = d) then 1 else 0) =
      (if And (r.val < h c0) (shift35 r c0 = d) then 1 else 0) :=
        Finset.sum_eq_single c0
          (by
            intro c hc hne
            have hfalse : Not (And (r.val < h c) (shift35 r c = d)) := by
              intro hp
              apply hne
              apply (shift35 r).injective
              simpa [c0] using hp.2
            simp [hfalse])
          (by simp)
    _ = (if r.val < h ((shift35 r).symm d) then 1 else 0) := by
      simp [c0, Equiv.apply_symm_apply]

theorem row_sum_eq_physical_height (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    (Finset.univ.filter fun r : Row =>
      r.val < h ((shift35 r).symm d)).card =
        slope35PhysicalOutputHeight h d := by
  classical
  rw [slope35PhysicalOutputHeight_eq_residue]
  simp_rw [residue_hits_eq_finRows h hbound]
  simp_rw [univ_filter_card_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact (source_indicator_sum h r d).symm


theorem column_count_eq_physical_output_height (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    matrixColumnTrueCount d (scrambledTopPrefix h) =
      slope35PhysicalOutputHeight h d := by
  rw [column_count_eq_row_sum]
  exact row_sum_eq_physical_height h hbound d

def bottomUnaryProfile (h : Col -> Nat) (w : Fin (4096 * 64)) : Bool :=
  decide (4096 - h (matrixCol 4096 64 (by omega) w) <=
    (matrixRow 4096 64 (by omega) w).val)

theorem columnSort_exec_eq_bottomUnaryProfile
    (v : Fin (4096 * 64) -> Bool) (h : Col -> Nat)
    (hcount : forall c, matrixColumnTrueCount c v = h c) :
    (columnSortNetwork 4096 64 (by omega)).exec v = bottomUnaryProfile h := by
  funext w
  let r := matrixRow 4096 64 (by omega) w
  let c := matrixCol 4096 64 (by omega) w
  have hcm : ColumnMonotoneInput 4096 64 (by omega)
      ((columnSortNetwork 4096 64 (by omega)).exec v) :=
    columnSortNetwork_columnMonotone (by omega) v
  have hcounts (j : Col) :
      matrixColumnTrueCount j ((columnSortNetwork 4096 64 (by omega)).exec v) = h j := by
    calc
      matrixColumnTrueCount j ((columnSortNetwork 4096 64 (by omega)).exec v) =
          matrixColumnTrueCount j v :=
        matrixColumnTrueCount_exec_eq (by omega) j _
          (columnSortNetwork_columnLocal 4096 64 (by omega)) v
      _ = h j := hcount j
  have hiff := colMono_true_iff (by omega) hcm r c
  rw [hcounts c] at hiff
  have hheight : h c <= 4096 := by
    calc
      h c = matrixColumnTrueCount c v := (hcount c).symm
      _ <= 4096 := matrixColumnTrueCount_le c v
  have hpred : Iff (4096 - r.val <= h c) (4096 - h c <= r.val) := by omega
  have hpoint : (columnSortNetwork 4096 64 (by omega)).exec v
      (matrixWire 4096 64 r c) = decide (4096 - h c <= r.val) := by
    change (columnSortNetwork 4096 64 (by omega)).exec v
      (matrixWire 4096 64 r c) = decide (4096 - h c <= r.val)
    by_cases hle : 4096 - h c <= r.val
    case pos =>
      have hout := hiff.mpr (hpred.mpr hle)
      rw [decide_eq_true hle]
      exact hout
    case neg =>
      have hout : (columnSortNetwork 4096 64 (by omega)).exec v
          (matrixWire 4096 64 r c) = false := by
        cases hout : (columnSortNetwork 4096 64 (by omega)).exec v
            (matrixWire 4096 64 r c) with
        | false => rfl
        | true => exact (hle (hpred.mp (hiff.mp hout))).elim
      rw [decide_eq_false hle]
      exact hout
  have hw : w = matrixWire 4096 64 r c :=
    (matrixWire_matrixRow_col (by omega) w).symm
  calc
    (columnSortNetwork 4096 64 (by omega)).exec v w =
        (columnSortNetwork 4096 64 (by omega)).exec v (matrixWire 4096 64 r c) :=
      congrArg ((columnSortNetwork 4096 64 (by omega)).exec v) hw
    _ = bottomUnaryProfile h (matrixWire 4096 64 r c) := by
      simpa [bottomUnaryProfile, matrixWire_row_col] using hpoint
    _ = bottomUnaryProfile h w := congrArg (bottomUnaryProfile h) hw.symm

theorem slope35SortPhysical_eq_bottomUnaryProfile (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    (columnSortNetwork 4096 64 (by omega)).exec (scrambledTopPrefix h) =
      bottomUnaryProfile (slope35PhysicalOutputHeight h) := by
  apply columnSort_exec_eq_bottomUnaryProfile
  intro d
  exact column_count_eq_physical_output_height h hbound d

def affine25 (r : Row) : Equiv.Perm Col where
  toFun c := Fin.mk ((35 * c.val + 25 * r.val) % 64) (Nat.mod_lt _ (by omega))
  invFun d := Fin.mk ((11 * ((d.val + 64 - (25 * r.val) % 64) % 64)) % 64)
    (Nat.mod_lt _ (by omega))
  left_inv c := by
    apply Fin.ext
    dsimp
    omega
  right_inv d := by
    apply Fin.ext
    dsimp
    omega

def scrambledTopPrefix25 (h : Col -> Nat) : Fin (4096 * 64) -> Bool :=
  Function.comp (topPrefix h) (rowScrambleWirePerm 4096 64 (by omega)
    (fun r => affine25 r)).symm

theorem scrambledTopPrefix25_matrixWire (h : Col -> Nat) (r : Row) (d : Col) :
    scrambledTopPrefix25 h (matrixWire 4096 64 r d) =
      decide (r.val < h ((affine25 r).symm d)) := by
  change topPrefix h
    ((rowScrambleWirePerm 4096 64 (by omega) (fun r => affine25 r)).symm
      (matrixWire 4096 64 r d)) = _
  rw [rowScrambleWirePerm_symm_apply]
  simp [topPrefix, matrixWire_row_col]

theorem column_count25_eq_row_sum (h : Col -> Nat) (d : Col) :
    matrixColumnTrueCount d (scrambledTopPrefix25 h) =
      (Finset.univ.filter fun r : Row =>
        r.val < h ((affine25 r).symm d)).card := by
  unfold matrixColumnTrueCount
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [scrambledTopPrefix25_matrixWire]
  simp

theorem residue_hits25_eq_finRows (h : Col -> Nat) (hbound : forall c, h c <= 4096)
    (d c : Col) :
    residueHits64 (h c) (slope25RowAt d c).val =
      (Finset.univ.filter fun r : Row =>
        And (r.val < h c) (affine25 r c = d)).card := by
  classical
  unfold residueHits64
  refine Finset.card_bij (fun i hi => Fin.mk i (by
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact lt_of_lt_of_le hi.1 (hbound c))) ?_ ?_ ?_
  case refine_1 =>
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro hi.1 (by
      have heq := (slope25_row_destination_iff_residue c d i).mpr hi.2
      apply Fin.ext
      dsimp [affine25]
      exact heq)
  case refine_2 =>
    intro i hi j hj hij
    exact congrArg Fin.val hij
  case refine_3 =>
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    have hmod : r.val % 64 = (slope25RowAt d c).val :=
      (slope25_row_destination_iff_residue c d r.val).mp (by
        have heq := congrArg Fin.val hr.2
        simpa [affine25] using heq)
    have hmem : Membership.mem ((Finset.range (h c)).filter
        (fun i => i % 64 = (slope25RowAt d c).val)) r.val :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hr.1) hmod)
    have heq : Fin.mk r.val (by omega : r.val < 4096) = r := by
      apply Fin.ext
      rfl
    exact Exists.intro r.val (Exists.intro hmem heq)

lemma source_indicator_sum25 (h : Col -> Nat) (r : Row) (d : Col) :
    (Finset.univ.sum fun c : Col =>
      if And (r.val < h c) (affine25 r c = d) then 1 else 0) =
      if r.val < h ((affine25 r).symm d) then 1 else 0 := by
  classical
  let c0 := (affine25 r).symm d
  calc
    (Finset.univ.sum fun c : Col =>
        if And (r.val < h c) (affine25 r c = d) then 1 else 0) =
      (if And (r.val < h c0) (affine25 r c0 = d) then 1 else 0) :=
        Finset.sum_eq_single c0
          (by
            intro c hc hne
            have hfalse : Not (And (r.val < h c) (affine25 r c = d)) := by
              intro hp
              apply hne
              apply (affine25 r).injective
              simpa [c0] using hp.2
            simp [hfalse])
          (by simp)
    _ = (if r.val < h ((affine25 r).symm d) then 1 else 0) := by
      simp [c0, Equiv.apply_symm_apply]

theorem row_sum25_eq_physical_height (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    (Finset.univ.filter fun r : Row =>
      r.val < h ((affine25 r).symm d)).card =
        slope25PhysicalOutputHeight h d := by
  classical
  rw [slope25PhysicalOutputHeight_eq_residue]
  simp_rw [residue_hits25_eq_finRows h hbound]
  simp_rw [univ_filter_card_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact (source_indicator_sum25 h r d).symm

theorem column_count25_eq_physical_output_height (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (d : Col) :
    matrixColumnTrueCount d (scrambledTopPrefix25 h) =
      slope25PhysicalOutputHeight h d := by
  rw [column_count25_eq_row_sum]
  exact row_sum25_eq_physical_height h hbound d

def reindexed35Height (h : Col -> Nat) : Col -> Nat :=
  fun c => h (liftSlope35Destination c)

def reverseRowEquiv : Equiv.Perm Row where
  toFun r := Fin.mk (4095 - r.val) (by omega)
  invFun r := Fin.mk (4095 - r.val) (by omega)
  left_inv r := by
    apply Fin.ext
    change 4095 - (4095 - r.val) = r.val
    exact Nat.sub_sub_self (by omega)
  right_inv r := by
    apply Fin.ext
    change 4095 - (4095 - r.val) = r.val
    exact Nat.sub_sub_self (by omega)

def lift35Equiv : Equiv.Perm Col where
  toFun := liftSlope35Destination
  invFun c := Fin.mk ((11 * c.val) % 64) (Nat.mod_lt _ (by omega))
  left_inv c := by
    apply Fin.ext
    dsimp [liftSlope35Destination]
    omega
  right_inv c := by
    apply Fin.ext
    dsimp [liftSlope35Destination]
    omega

def reorientWirePerm : Equiv.Perm (Fin (4096 * 64)) :=
  (matrixWireEquiv (by omega)).symm.trans
    ((Equiv.prodCongr reverseRowEquiv lift35Equiv).trans
      (matrixWireEquiv (by omega)))

theorem reorientWirePerm_matrixWire (r : Row) (c : Col) :
    reorientWirePerm (matrixWire 4096 64 r c) =
      matrixWire 4096 64 (reverseRowEquiv r) (liftSlope35Destination c) := by
  simp [reorientWirePerm, matrixWireEquiv, matrixWire_row_col]
  rfl

/-- The profile reorientation reverses the row order within every column.
Thus a vertical comparator cannot be transported through this map using the
order-preserving `relabelNet` interface without also changing comparator
direction. -/
theorem reorientWirePerm_reverses_column_rows (r s : Row) (c : Col)
    (hrs : r.val < s.val) :
    (matrixRow 4096 64 (by omega)
      (reorientWirePerm (matrixWire 4096 64 s c))).val <
    (matrixRow 4096 64 (by omega)
      (reorientWirePerm (matrixWire 4096 64 r c))).val := by
  rw [reorientWirePerm_matrixWire, reorientWirePerm_matrixWire]
  simp only [matrixWire_row_col]
  simp [reverseRowEquiv]
  omega

theorem topPrefix_reindexed_eq_reorientedBottomUnary (h : Col -> Nat) :
    topPrefix (reindexed35Height h) = Function.comp (bottomUnaryProfile h) reorientWirePerm := by
  funext w
  let r := matrixRow 4096 64 (by omega) w
  let c := matrixCol 4096 64 (by omega) w
  have hw : w = matrixWire 4096 64 r c :=
    (matrixWire_matrixRow_col (by omega) w).symm
  calc
    topPrefix (reindexed35Height h) w =
        topPrefix (reindexed35Height h) (matrixWire 4096 64 r c) :=
      congrArg (topPrefix (reindexed35Height h)) hw
    _ = bottomUnaryProfile h
        (reorientWirePerm (matrixWire 4096 64 r c)) := by
      rw [reorientWirePerm_matrixWire]
      simp only [topPrefix, bottomUnaryProfile, matrixWire_row_col,
        reindexed35Height, reverseRowEquiv]
      by_cases hp : r.val < h (liftSlope35Destination c)
      case pos =>
        have hineq : 4096 - h (liftSlope35Destination c) <= 4095 - r.val := by omega
        simp [hp, hineq]
      case neg =>
        have hineq : Not (4096 - h (liftSlope35Destination c) <= 4095 - r.val) := by omega
        simp [hp, hineq]
    _ = bottomUnaryProfile h (reorientWirePerm w) :=
      congrArg (bottomUnaryProfile h) (congrArg reorientWirePerm hw.symm)

theorem slope25SortPhysical_eq_fullHeightTwoShuffle (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    (columnSortNetwork 4096 64 (by omega)).exec
      (scrambledTopPrefix25 (reindexed35Height (slope35PhysicalOutputHeight h))) =
        bottomUnaryProfile (fullHeightTwoShuffle h) := by
  apply columnSort_exec_eq_bottomUnaryProfile
  intro d
  exact column_count25_eq_physical_output_height
    (reindexed35Height (slope35PhysicalOutputHeight h))
    (by
      intro c
      calc
        slope35PhysicalOutputHeight h (liftSlope35Destination c) =
            matrixColumnTrueCount (liftSlope35Destination c) (scrambledTopPrefix h) :=
          (column_count_eq_physical_output_height h hbound
            (liftSlope35Destination c)).symm
        _ <= 4096 := matrixColumnTrueCount_le _ _)
    d


def physicalTwoShuffleInput (h : Col -> Nat) : Fin (4096 * 64) -> Bool :=
  Function.comp
    (Function.comp (bottomUnaryProfile (slope35PhysicalOutputHeight h)) reorientWirePerm)
    (rowScrambleWirePerm 4096 64 (by omega) (fun r => affine25 r)).symm

theorem physicalTwoShuffleInput_eq_scrambledTopPrefix25 (h : Col -> Nat) :
    physicalTwoShuffleInput h =
      scrambledTopPrefix25 (reindexed35Height (slope35PhysicalOutputHeight h)) := by
  unfold physicalTwoShuffleInput scrambledTopPrefix25
  exact congrArg (fun f : Fin (4096 * 64) -> Bool =>
      Function.comp f
        (rowScrambleWirePerm 4096 64 (by omega) (fun r => affine25 r)).symm)
    (topPrefix_reindexed_eq_reorientedBottomUnary (slope35PhysicalOutputHeight h)).symm

theorem fullHeightTwoShuffle_physical (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    (columnSortNetwork 4096 64 (by omega)).exec (physicalTwoShuffleInput h) =
      bottomUnaryProfile (fullHeightTwoShuffle h) := by
  rw [physicalTwoShuffleInput_eq_scrambledTopPrefix25]
  exact slope25SortPhysical_eq_fullHeightTwoShuffle h hbound

end Chvatal.D2Slope35Physical4096
