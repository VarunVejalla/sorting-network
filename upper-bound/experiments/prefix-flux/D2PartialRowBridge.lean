import D2LiftedShuffleBridge
import AKS.Chvatal.Bulk2Bridge
import AKS.Chvatal.PhysicalPack2

open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Chvatal.D2PartialRowBridge

open Chvatal.D2LiftedShuffleBridge

abbrev Col := Fin 64

def strideScrambleM (m stride : Nat) : Chvatal.Scramble m 64 :=
  fun r => shift64 (stride * r.val)

def lowPrefixBoolM {m : Nat} (h : Col -> Nat) (w : Fin (m * 64)) : Bool :=
  decide (h (Chvatal.matrixCol m 64 (by omega) w) <=
    (Chvatal.matrixRow m 64 (by omega) w).val)

def matrixColumnFalseCountM {m : Nat} (d : Col)
    (v : Fin (m * 64) -> Bool) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
    v (Chvatal.matrixWire m 64 r d) = false).card

def rowShiftLoadByRowsM (m stride : Nat) (h : Col -> Nat) (d : Col) : Nat :=
  Finset.univ.sum fun r : Fin m =>
    if r.val < h ((shift64 (stride * r.val)).symm d) then 1 else 0

theorem rowShiftLoadByRowsM_eq_full
    (m stride : Nat) (hm : m <= 4096) (h : Col -> Nat)
    (hh : forall c, h c <= m) (d : Col) :
    rowShiftLoadByRowsM m stride h d =
      Chvatal.D2LiftedShuffleBridge.rowShiftLoadByRows stride h d := by
  classical
  let predM : Fin m -> Prop := fun r =>
    r.val < h ((shift64 (stride * r.val)).symm d)
  let predN : Fin 4096 -> Prop := fun r =>
    r.val < h ((shift64 (stride * r.val)).symm d)
  unfold rowShiftLoadByRowsM Chvatal.D2LiftedShuffleBridge.rowShiftLoadByRows
  rw [Finset.sum_boole, Finset.sum_boole]
  change (Finset.univ.filter predM).card = (Finset.univ.filter predN).card
  apply Finset.card_bij (fun r _ => Fin.mk r.val (by omega))
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simpa [predM, predN] using hr
  intro a ha b hb hab
  exact Fin.ext (congrArg (fun x : Fin 4096 => x.val) hab)
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  let q : Fin m := Fin.mk r.val (lt_of_lt_of_le hr (hh ((shift64 (stride * r.val)).symm d)))
  have hmem : q ∈ Finset.univ.filter predM :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) (by simpa [predM, q] using hr))
  have heq : Fin.mk q.val (by omega) = r := by
    apply Fin.ext
    rfl
  exact Exists.intro q (Exists.intro hmem heq)
theorem rowShiftLoadByRowsM_le (m stride : Nat) (h : Col -> Nat) (d : Col) :
    rowShiftLoadByRowsM m stride h d <= m := by
  classical
  unfold rowShiftLoadByRowsM
  calc
    (Finset.univ.sum fun r : Fin m =>
      if r.val < h ((shift64 (stride * r.val)).symm d) then 1 else 0) <=
      Finset.univ.sum (fun _ : Fin m => 1) := by
        apply Finset.sum_le_sum
        intro r hr
        split_ifs <;> omega
    _ = m := by simp
theorem lowPrefixBoolM_columnMonotone {m : Nat} (h : Col -> Nat) :
    Chvatal.ColumnMonotoneInput m 64 (by omega) (lowPrefixBoolM h) := by
  intro j r s hrs
  have hrsval : r.val <= s.val := Fin.le_iff_val_le_val.mp hrs
  by_cases hr : h j <= r.val
  case pos =>
    have hs : h j <= s.val := le_trans hr hrsval
    simp [lowPrefixBoolM, Chvatal.matrixWire_row_col, hr, hs]
  case neg =>
    simp [lowPrefixBoolM, Chvatal.matrixWire_row_col, hr]

theorem matrixColumnFalseCountM_eq_sub_trueCount {m : Nat} (d : Col)
    (v : Fin (m * 64) -> Bool) :
    matrixColumnFalseCountM d v + Chvatal.matrixColumnTrueCount d v = m := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m)))
    (p := fun r => v (Chvatal.matrixWire m 64 r d) = false)
  have hnotfalse : (Finset.univ.filter fun r : Fin m =>
      not (v (Chvatal.matrixWire m 64 r d) = false)) =
    (Finset.univ.filter fun r : Fin m =>
      v (Chvatal.matrixWire m 64 r d) = true) := by
    ext r
    cases v (Chvatal.matrixWire m 64 r d) <;> simp
  have hpart2 :
      matrixColumnFalseCountM d v + Chvatal.matrixColumnTrueCount d v = m := by
    unfold matrixColumnFalseCountM Chvatal.matrixColumnTrueCount
    simpa [hnotfalse, Finset.card_univ, Fintype.card_fin] using hpart
  exact hpart2

theorem rowShuffle_prefix_falseCountM {m : Nat}
    (stride : Nat) (h : Col -> Nat) (d : Col) :
    matrixColumnFalseCountM d
      (fun w => lowPrefixBoolM h
        ((Chvatal.rowScrambleWirePerm m 64 (by omega) (strideScrambleM m stride)).symm w)) =
      rowShiftLoadByRowsM m stride h d := by
  classical
  let sigma := strideScrambleM m stride
  have hset : (Finset.univ.filter fun r : Fin m =>
      (fun w => lowPrefixBoolM h
        ((Chvatal.rowScrambleWirePerm m 64 (by omega) sigma).symm w))
          (Chvatal.matrixWire m 64 r d) = false) =
      Finset.univ.filter fun r : Fin m =>
        r.val < h ((sigma r).symm d) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Chvatal.rowScrambleWirePerm_symm_apply]
    simp [lowPrefixBoolM, Chvatal.matrixWire_row_col, sigma, strideScrambleM,
      shift64]
  rw [matrixColumnFalseCountM, hset]
  unfold rowShiftLoadByRowsM
  rw [Finset.card_filter]
  rfl

theorem semanticExec_stride_falseCountM {m : Nat}
    (stride : Nat) (h : Col -> Nat) (d : Col) :
    matrixColumnFalseCountM d
      (Chvatal.semanticExec (by omega) (strideScrambleM m stride) (lowPrefixBoolM h)) =
      rowShiftLoadByRowsM m stride h d := by
  classical
  have hmono := lowPrefixBoolM_columnMonotone (m := m) h
  have hfix := Chvatal.columnSort_exec_of_columnMonotone (by omega)
    (lowPrefixBoolM h) hmono
  unfold Chvatal.semanticExec
  rw [hfix]
  let shuffled := fun w => lowPrefixBoolM h
    ((Chvatal.rowScrambleWirePerm m 64 (by omega) (strideScrambleM m stride)).symm w)
  have htrue : Chvatal.matrixColumnTrueCount d
      ((Chvatal.columnSortNetwork m 64 (by omega)).exec shuffled) =
      Chvatal.matrixColumnTrueCount d shuffled :=
    Chvatal.matrixColumnTrueCount_exec_eq (by omega) d _
      (Chvatal.columnSortNetwork_columnLocal m 64 (by omega)) shuffled
  have hfalseSorted := matrixColumnFalseCountM_eq_sub_trueCount d
    ((Chvatal.columnSortNetwork m 64 (by omega)).exec shuffled)
  have hfalseRaw := matrixColumnFalseCountM_eq_sub_trueCount d shuffled
  have hsame : matrixColumnFalseCountM d
      ((Chvatal.columnSortNetwork m 64 (by omega)).exec shuffled) =
      matrixColumnFalseCountM d shuffled := by omega
  change matrixColumnFalseCountM d ((Chvatal.columnSortNetwork m 64 (by omega)).exec shuffled) = _
  rw [hsame]
  exact rowShuffle_prefix_falseCountM stride h d
theorem semanticExec_stride_eq_prefixM {m : Nat}
    (stride : Nat) (h : Col -> Nat) :
    Chvatal.semanticExec (by omega) (strideScrambleM m stride) (lowPrefixBoolM h) =
      lowPrefixBoolM (fun d => rowShiftLoadByRowsM m stride h d) := by
  classical
  let out := Chvatal.semanticExec (by omega) (strideScrambleM m stride) (lowPrefixBoolM h)
  let hout : Col -> Nat := fun d => rowShiftLoadByRowsM m stride h d
  have hmono : Chvatal.ColumnMonotoneInput m 64 (by omega) out := by
    exact Chvatal.columnSortNetwork_columnMonotone (by omega) _
  have hfalse (d : Col) : matrixColumnFalseCountM d out = hout d := by
    simpa [out, hout] using semanticExec_stride_falseCountM stride h d
  have hbound (d : Col) : hout d <= m := by
    rw [← hfalse d]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have htrue (d : Col) : Chvatal.matrixColumnTrueCount d out = m - hout d := by
    have hsum := matrixColumnFalseCountM_eq_sub_trueCount d out
    rw [hfalse d] at hsum
    have hle := hbound d
    omega
  funext w
  let r := Chvatal.matrixRow m 64 (by omega) w
  let c := Chvatal.matrixCol m 64 (by omega) w
  have hiff := Chvatal.colMono_true_iff (by omega) hmono r c
  have hiff' : Iff (out (Chvatal.matrixWire m 64 r c) = true) (hout c <= r.val) := by
    rw [htrue c] at hiff
    have harith : Iff (m - r.val <= m - hout c) (hout c <= r.val) := by omega
    exact hiff.trans harith
  have hiffW : Iff (out w = true) (hout c <= r.val) := by
    rw [← Chvatal.matrixWire_matrixRow_col (by omega) w]
    exact hiff'
  cases hw : out w
  case false =>
    have hnot : Not (hout c <= r.val) := by
      intro hp
      have hval := hiffW.mpr hp
      simp [hw] at hval
    change out w = decide (hout (Chvatal.matrixCol m 64 (by omega) w) <=
      (Chvatal.matrixRow m 64 (by omega) w).val)
    rw [hw]
    have hnotW : Not (hout (Chvatal.matrixCol m 64 (by omega) w) <=
        (Chvatal.matrixRow m 64 (by omega) w).val) := by
      simpa [r, c] using hnot
    simp [hnotW]
  case true =>
    have hp : hout c <= r.val := hiffW.mp hw
    change out w = decide (hout (Chvatal.matrixCol m 64 (by omega) w) <=
      (Chvatal.matrixRow m 64 (by omega) w).val)
    rw [hw]
    have hpW : hout (Chvatal.matrixCol m 64 (by omega) w) <=
        (Chvatal.matrixRow m 64 (by omega) w).val := by
      simpa [r, c] using hp
    simp [hpW]
theorem semanticExec2_two_stride_eq_prefixM {m : Nat}
    (h : Col -> Nat) :
    Chvatal.semanticExec2 (by omega) (strideScrambleM m 35) (strideScrambleM m 25)
        (lowPrefixBoolM h) =
      lowPrefixBoolM (fun d =>
        rowShiftLoadByRowsM m 25 (fun c => rowShiftLoadByRowsM m 35 h c) d) := by
  classical
  let h1 : Col -> Nat := fun c => rowShiftLoadByRowsM m 35 h c
  rw [Chvatal.semanticExec2_eq_comp (by omega)]
  rw [semanticExec_stride_eq_prefixM 35 h]
  simpa [h1] using semanticExec_stride_eq_prefixM 25 h1

end Chvatal.D2PartialRowBridge
