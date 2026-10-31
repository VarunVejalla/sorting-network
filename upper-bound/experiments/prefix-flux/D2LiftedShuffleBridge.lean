import D2Slope25Lift
import D2Slope25MarginTail
import AKS.Chvatal.Bulk2Bridge
import AKS.Chvatal.SortedColumnDecode

open scoped BigOperators
open Chvatal.D2RankAlignment
open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25MarginTail

set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Chvatal.D2LiftedShuffleBridge

abbrev Col := Fin 64
abbrev Row := Fin 4096

/-- Generic Boolean matrix counting identity; kept polymorphic in both
dimensions to avoid reducing the concrete 4096-by-64 finite type. -/
private theorem matrixFalseTotal_eq_columnFalseCounts {m n : Nat} (hn : 0 < n)
    (v : Fin (m * n) -> Bool) :
    (Finset.univ.filter fun w : Fin (m * n) => v w = false).card =
      Finset.univ.sum fun c : Fin n =>
        (Finset.univ.filter fun r : Fin m => v (Chvatal.matrixWire m n r c) = false).card := by
  classical
  rw [Finset.card_filter, Chvatal.sum_matrixWire hn]
  apply Finset.sum_congr rfl
  intro c hc
  symm
  rw [Finset.card_filter]

/-- Monotone threshold maps commute through the semantic two-round network.
First establish it for one column-sort/scramble/column-sort block with an
abstract comparator network, so the large bitonic network never unfolds. -/
private theorem sortScrambleSort_comp_monotone {n : Nat} {α β : Type}
    [LinearOrder α] [LinearOrder β] (net : ComparatorNetwork n)
    (ρ : Equiv.Perm (Fin n)) (f : α -> β) (hf : Monotone f)
    (v : Fin n -> α) :
    f ∘ net.exec (net.exec v ∘ ρ.symm) =
      net.exec (net.exec (f ∘ v) ∘ ρ.symm) := by
  calc
    f ∘ net.exec (net.exec v ∘ ρ.symm) =
        net.exec (f ∘ (net.exec v ∘ ρ.symm)) := net.exec_comp_monotone hf _
    _ = net.exec ((f ∘ net.exec v) ∘ ρ.symm) := by rfl
    _ = net.exec (net.exec (f ∘ v) ∘ ρ.symm) := by
      exact congrArg (fun u => net.exec (u ∘ ρ.symm))
        (net.exec_comp_monotone hf v)

theorem semanticExec2_comp_monotone {α β : Type} [LinearOrder α] [LinearOrder β]
    (hn : 0 < 64) (σ₁ σ₂ : Chvatal.Scramble 4096 64) (f : α -> β)
    (hf : Monotone f) (v : Fin (4096 * 64) -> α) :
    f ∘ Chvatal.semanticExec2 hn σ₁ σ₂ v =
      Chvatal.semanticExec2 hn σ₁ σ₂ (f ∘ v) := by
  have hcomp := Chvatal.semanticExec2_eq_comp hn σ₁ σ₂ v
  have hcomp' := Chvatal.semanticExec2_eq_comp hn σ₁ σ₂ (f ∘ v)
  have h1 := sortScrambleSort_comp_monotone
    (Chvatal.columnSortNetwork 4096 64 hn)
    (Chvatal.rowScrambleWirePerm 4096 64 hn σ₁) f hf v
  have h2 := sortScrambleSort_comp_monotone
    (Chvatal.columnSortNetwork 4096 64 hn)
    (Chvatal.rowScrambleWirePerm 4096 64 hn σ₂) f hf
    (Chvatal.semanticExec hn σ₁ v)
  calc
    f ∘ Chvatal.semanticExec2 hn σ₁ σ₂ v =
        f ∘ Chvatal.semanticExec hn σ₂ (Chvatal.semanticExec hn σ₁ v) :=
      congrArg (fun u => f ∘ u) hcomp
    _ = Chvatal.semanticExec hn σ₂ (f ∘ Chvatal.semanticExec hn σ₁ v) := h2
    _ = Chvatal.semanticExec hn σ₂ (Chvatal.semanticExec hn σ₁ (f ∘ v)) :=
      congrArg (Chvatal.semanticExec hn σ₂) h1
    _ = Chvatal.semanticExec2 hn σ₁ σ₂ (f ∘ v) := hcomp'.symm

def shift64 (s : Nat) : Equiv.Perm Col where
  toFun c := ⟨(c.val + s) % 64, Nat.mod_lt _ (by omega)⟩
  invFun c := ⟨(c.val + 64 - s % 64) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv c := by
    apply Fin.ext
    dsimp
    omega
  right_inv c := by
    apply Fin.ext
    dsimp
    omega

/-- Column relabeling by multiplication by 35 modulo 64. -/
def mul35Equiv : Equiv.Perm Col where
  toFun c := ⟨(35 * c.val) % 64, Nat.mod_lt _ (by omega)⟩
  invFun c := ⟨(11 * c.val) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv c := by
    apply Fin.ext
    dsimp
    omega
  right_inv c := by
    apply Fin.ext
    dsimp
    omega

/-- Height profile after a row-preserving cyclic shift by `stride * row`.
Each source column contributes its occupied top-prefix rows sent to `d`. -/
def rowShiftLoad (stride : Nat) (h : Col -> Nat) (d : Col) : Nat :=
  Finset.univ.sum fun c : Col =>
    ((Finset.range (h c)).filter fun row =>
      (c.val + stride * row) % 64 = d.val).card

def rowShiftLoadByRows (stride : Nat) (h : Col -> Nat) (d : Col) : Nat :=
  Finset.univ.sum fun r : Row =>
    if r.val < h ((shift64 (stride * r.val)).symm d) then 1 else 0

def strideScramble (stride : Nat) : Chvatal.Scramble 4096 64 :=
  fun r => shift64 (stride * r.val)

def lowPrefixBool (h : Col -> Nat) (w : Fin (4096 * 64)) : Bool :=
  decide (h (Chvatal.matrixCol 4096 64 (by omega) w) <=
    (Chvatal.matrixRow 4096 64 (by omega) w).val)

def matrixColumnFalseCount (d : Col) (v : Fin (4096 * 64) -> Bool) : Nat :=
  (Finset.univ.filter fun r : Row =>
    v (Chvatal.matrixWire 4096 64 r d) = false).card

theorem lowPrefixBool_columnMonotone (h : Col -> Nat) :
    Chvatal.ColumnMonotoneInput 4096 64 (by omega) (lowPrefixBool h) := by
  intro j r s hrs
  have hrsval : r.val <= s.val := Fin.le_iff_val_le_val.mp hrs
  by_cases hr : h j <= r.val
  · have hs : h j <= s.val := le_trans hr hrsval
    simp [lowPrefixBool, Chvatal.matrixWire_row_col, hr, hs]
  · simp [lowPrefixBool, Chvatal.matrixWire_row_col, hr]

theorem matrixColumnFalseCount_eq_sub_trueCount
    (d : Col) (v : Fin (4096 * 64) -> Bool) :
    matrixColumnFalseCount d v +
      Chvatal.matrixColumnTrueCount d v = 4096 := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Row))
    (p := fun r => v (Chvatal.matrixWire 4096 64 r d) = false)
  have hnotfalse : (Finset.univ.filter fun r : Row =>
      ¬ v (Chvatal.matrixWire 4096 64 r d) = false) =
    (Finset.univ.filter fun r : Row =>
      v (Chvatal.matrixWire 4096 64 r d) = true) := by
    ext r
    cases v (Chvatal.matrixWire 4096 64 r d) <;> simp
  rw [hnotfalse] at hpart
  simp only [Finset.card_univ, Fintype.card_fin] at hpart
  unfold matrixColumnFalseCount Chvatal.matrixColumnTrueCount
  omega

theorem matrixFalseTotal_eq_sumColumns (v : Fin (4096 * 64) -> Bool) :
    (Finset.univ.filter fun w : Fin (4096 * 64) => v w = false).card =
      Finset.univ.sum fun c : Col => matrixColumnFalseCount c v := by
  simpa [matrixColumnFalseCount] using
    (matrixFalseTotal_eq_columnFalseCounts (m := 4096) (n := 64) (by omega) v)

theorem rowShuffle_prefix_falseCount
    (stride : Nat) (h : Col -> Nat) (hh : forall c, h c <= 4096) (d : Col) :
    matrixColumnFalseCount d
      (lowPrefixBool h ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble stride)).symm) =
      rowShiftLoadByRows stride h d := by
  classical
  let σ := strideScramble stride
  have hset : (Finset.univ.filter fun r : Row =>
      (lowPrefixBool h ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) σ).symm)
          (Chvatal.matrixWire 4096 64 r d) = false) =
      Finset.univ.filter fun r : Row =>
        r.val < h ((σ r).symm d) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change lowPrefixBool h
      ((Chvatal.rowScrambleWirePerm 4096 64 (by omega) σ).symm
        (Chvatal.matrixWire 4096 64 r d)) = false ↔ _
    rw [Chvatal.rowScrambleWirePerm_symm_apply]
    simp [lowPrefixBool, Chvatal.matrixWire_row_col,
      σ, strideScramble, shift64, Nat.not_le]
  rw [matrixColumnFalseCount, hset]
  unfold rowShiftLoadByRows
  rw [Finset.card_filter]
  rfl

/-- Sorting the columns before and after one lifted row shuffle realizes the
same false-prefix height transition as the exact D2 load formula. -/
theorem semanticExec_stride_falseCount
    (stride : Nat) (h : Col -> Nat) (hh : forall c, h c <= 4096) (d : Col) :
    matrixColumnFalseCount d
      (Chvatal.semanticExec (by omega) (strideScramble stride) (lowPrefixBool h)) =
      rowShiftLoadByRows stride h d := by
  classical
  have hmono := lowPrefixBool_columnMonotone h
  have hfix := Chvatal.columnSort_exec_of_columnMonotone (by omega)
    (lowPrefixBool h) hmono
  unfold Chvatal.semanticExec
  rw [hfix]
  let shuffled := lowPrefixBool h ∘
    (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble stride)).symm
  have htrue : Chvatal.matrixColumnTrueCount d
      ((Chvatal.columnSortNetwork 4096 64 (by omega)).exec shuffled) =
      Chvatal.matrixColumnTrueCount d shuffled :=
    Chvatal.matrixColumnTrueCount_exec_eq (by omega) d _
      (Chvatal.columnSortNetwork_columnLocal 4096 64 (by omega)) shuffled
  have hfalseSorted := matrixColumnFalseCount_eq_sub_trueCount d
    ((Chvatal.columnSortNetwork 4096 64 (by omega)).exec shuffled)
  have hfalseRaw := matrixColumnFalseCount_eq_sub_trueCount d shuffled
  have hsame : matrixColumnFalseCount d
      ((Chvatal.columnSortNetwork 4096 64 (by omega)).exec shuffled) =
      matrixColumnFalseCount d shuffled := by omega
  rw [show (lowPrefixBool h ∘
      (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble stride)).symm) =
      shuffled by rfl]
  rw [hsame]
  exact rowShuffle_prefix_falseCount stride h hh d

/-- The output of one sort-shuffle-sort stage is again a column-prefix
matrix, with exactly the lifted row-shift profile as its false-prefix height. -/
theorem semanticExec_stride_eq_prefix
    (stride : Nat) (h : Col -> Nat) (hh : forall c, h c <= 4096) :
    Chvatal.semanticExec (by omega) (strideScramble stride) (lowPrefixBool h) =
      lowPrefixBool (fun d => rowShiftLoadByRows stride h d) := by
  classical
  let out := Chvatal.semanticExec (by omega) (strideScramble stride) (lowPrefixBool h)
  let hout : Col -> Nat := fun d => rowShiftLoadByRows stride h d
  have hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) out := by
    exact Chvatal.columnSortNetwork_columnMonotone (by omega) _
  have hfalse (d : Col) : matrixColumnFalseCount d out = hout d := by
    simpa [out, hout] using semanticExec_stride_falseCount stride h hh d
  have hbound (d : Col) : hout d <= 4096 := by
    rw [← hfalse d]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have htrue (d : Col) : Chvatal.matrixColumnTrueCount d out = 4096 - hout d := by
    have hsum := matrixColumnFalseCount_eq_sub_trueCount d out
    rw [hfalse d] at hsum
    have hle := hbound d
    omega
  funext w
  let r := Chvatal.matrixRow 4096 64 (by omega) w
  let c := Chvatal.matrixCol 4096 64 (by omega) w
  have hiff := Chvatal.colMono_true_iff (by omega) hmono r c
  have hiff' : out (Chvatal.matrixWire 4096 64 r c) = true ↔ hout c <= r.val := by
    rw [htrue c] at hiff
    have harith : (4096 - r.val <= 4096 - hout c) ↔ hout c <= r.val := by omega
    exact hiff.trans harith
  have hiffW : out w = true ↔ hout c <= r.val := by
    rw [← Chvatal.matrixWire_matrixRow_col (by omega) w]
    exact hiff'
  cases hw : out w
  · have hnot : ¬ hout c <= r.val := by
      intro hp
      have := hiffW.mpr hp
      simp [hw] at this
    change out w = decide (hout (Chvatal.matrixCol 4096 64 (by omega) w) <=
      (Chvatal.matrixRow 4096 64 (by omega) w).val)
    rw [hw]
    have hnotW : ¬ hout (Chvatal.matrixCol 4096 64 (by omega) w) <=
        (Chvatal.matrixRow 4096 64 (by omega) w).val := by
      simpa [r, c] using hnot
    simp [hnotW]
  · have hp : hout c <= r.val := hiffW.mp hw
    change out w = decide (hout (Chvatal.matrixCol 4096 64 (by omega) w) <=
      (Chvatal.matrixRow 4096 64 (by omega) w).val)
    rw [hw]
    have hpW : hout (Chvatal.matrixCol 4096 64 (by omega) w) <=
        (Chvatal.matrixRow 4096 64 (by omega) w).val := by
      simpa [r, c] using hp
    simp [hpW]

/-- The actual two-scramble network realizes the composed lifted profile.
This identifies the candidate two-shuffle Boolean stage with the network's
semantic execution, rather than only with a row-count calculation. -/
theorem semanticExec2_two_stride_eq_prefix
    (h : Col -> Nat) (hh : forall c, h c <= 4096) :
    Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25)
        (lowPrefixBool h) =
      lowPrefixBool (fun d =>
        rowShiftLoadByRows 25 (fun c => rowShiftLoadByRows 35 h c) d) := by
  classical
  let h1 : Col -> Nat := fun c => rowShiftLoadByRows 35 h c
  have hh1 (c : Col) : h1 c <= 4096 := by
    change rowShiftLoadByRows 35 h c <= 4096
    have heq := semanticExec_stride_falseCount 35 h hh c
    rw [← heq]
    exact (Finset.card_filter_le _ _).trans (by simp)
  rw [Chvatal.semanticExec2_eq_comp (by omega)]
  change Chvatal.semanticExec (by omega) (strideScramble 25)
      (Chvatal.semanticExec (by omega) (strideScramble 35) (lowPrefixBool h)) = _
  rw [semanticExec_stride_eq_prefix 35 h hh]
  simpa [h1] using semanticExec_stride_eq_prefix 25 h1 hh1

/-- Every column-monotone Boolean matrix is the prefix encoding of its
per-column false counts. This removes the explicit-profile precondition from
the two-shuffle adapter. -/
theorem columnMonotone_eq_lowPrefixBool
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    v = lowPrefixBool (fun c => matrixColumnFalseCount c v) := by
  classical
  funext w
  let r := Chvatal.matrixRow 4096 64 (by omega) w
  let c := Chvatal.matrixCol 4096 64 (by omega) w
  have hfalse (d : Col) :
      matrixColumnFalseCount d v + Chvatal.matrixColumnTrueCount d v = 4096 :=
    matrixColumnFalseCount_eq_sub_trueCount d v
  have hiff := Chvatal.colMono_true_iff (by omega) hmono r c
  have hiffW : v w = true <-> matrixColumnFalseCount c v <= r.val := by
    rw [<- Chvatal.matrixWire_matrixRow_col (by omega) w]
    constructor
    · intro hv
      have hc := hiff.mp hv
      have hs := hfalse c
      omega
    · intro hp
      apply hiff.mpr
      have hs := hfalse c
      omega
  change v w = lowPrefixBool (fun d => matrixColumnFalseCount d v) w
  rw [Bool.eq_iff_iff]
  simpa [lowPrefixBool, r, c] using hiffW

private theorem card_range_filter_eq_fin_sum
    (h : Nat) (hh : h <= 4096) (P : Nat -> Prop) [DecidablePred P] :
    ((Finset.range h).filter P).card =
      Finset.univ.sum fun r : Row => if r.val < h /\ P r.val then 1 else 0 := by
  classical
  have hset : (Finset.range h).filter P =
      (Finset.range 4096).filter (fun x => x < h /\ P x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hP⟩
      exact ⟨by omega, hx, hP⟩
    · rintro ⟨_, hx, hP⟩
      exact ⟨hx, hP⟩
  rw [hset]
  let T := (Finset.range 4096).filter (fun x => x < h /\ P x)
  let U := Finset.univ.filter (fun r : Row => r.val < h /\ P r.val)
  have hcard : T.card = U.card := by
    apply Finset.card_bij (fun x hx => (⟨x, by
      have hx' := (Finset.mem_filter.mp hx).1
      simp only [Finset.mem_range] at hx'
      omega⟩ : Row))
    · intro x hx
      simp only [T, Finset.mem_filter, Finset.mem_range] at hx
      rcases hx with ⟨_, hx, hP⟩
      simpa [U] using (show x < h ∧ P x from ⟨hx, hP⟩)
    · intro x hx y hy heq
      exact congrArg Fin.val heq
    · intro r hr
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      refine ⟨r.val, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_range]
        exact ⟨r.isLt, hr.1, hr.2⟩
      · exact Fin.ext rfl
  rw [hcard]
  change (Finset.univ.filter (fun r : Row => r.val < h /\ P r.val)).card = _
  rw [Finset.card_filter]

private theorem rowPrefix_indicator_sum (h : Nat) (hh : h <= 4096) :
    (Finset.univ.sum fun r : Row => if r.val < h then 1 else 0) = h := by
  have hsum := card_range_filter_eq_fin_sum h hh (fun _ => True)
  have hsum' : ((Finset.range h).filter (fun _ => True)).card =
      Finset.univ.sum fun r : Row => if r.val < h then 1 else 0 := by
    simpa only [and_true] using hsum
  rw [← hsum']
  simp

/-- A row-preserving cyclic shuffle cannot move a key out of a common live
prefix of `m` rows: each output column receives at most one wire per row. -/
theorem rowShiftLoadByRows_le_of_height_le (stride : Nat) (h : Col -> Nat)
    (m : Nat) (hm : m <= 4096) (hh : forall c, h c <= m) (d : Col) :
    rowShiftLoadByRows stride h d <= m := by
  classical
  unfold rowShiftLoadByRows
  rw [Finset.sum_boole]
  have hsubset :
      (Finset.univ.filter fun r : Row =>
        r.val < h ((shift64 (stride * r.val)).symm d)) ⊆
      Finset.univ.filter fun r : Row => r.val < m := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact lt_of_lt_of_le hr (hh _)
  have hcard :
      (Finset.univ.filter fun r : Row => r.val < m).card = m := by
    have hsum := rowPrefix_indicator_sum m hm
    simpa only [Finset.sum_boole] using hsum
  exact (Finset.card_le_card hsubset).trans_eq hcard

/-- Each cyclic row shift preserves the total number of marked wires. -/
theorem rowShiftLoadByRows_total (stride : Nat) (h : Col -> Nat) :
    (hh : forall c, h c <= 4096) ->
    Finset.univ.sum (fun d : Col => rowShiftLoadByRows stride h d) =
      Finset.univ.sum h := by
  classical
  intro hh
  unfold rowShiftLoadByRows
  rw [Finset.sum_comm]
  calc
    (Finset.univ.sum fun r : Row =>
      Finset.univ.sum fun d : Col =>
        if r.val < h ((shift64 (stride * r.val)).symm d) then 1 else 0) =
      Finset.univ.sum fun r : Row =>
        Finset.univ.sum fun c : Col => if r.val < h c then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          let e := shift64 (stride * r.val)
          let F : Col -> Nat := fun c => if r.val < h c then 1 else 0
          calc
            (Finset.univ.sum fun d : Col =>
              if r.val < h (e.symm d) then 1 else 0) =
              Finset.univ.sum fun d : Col => F (e.symm d) := by
                apply Finset.sum_congr rfl
                intro d hd
                simp [F]
            _ = Finset.univ.sum fun c : Col => F c := Equiv.sum_comp e.symm F
    _ = Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun r : Row => if r.val < h c then 1 else 0 := Finset.sum_comm
    _ = Finset.univ.sum h := by
      apply Finset.sum_congr rfl
      intro c hc
      exact rowPrefix_indicator_sum (h c) (hh c)

theorem rowShiftLoad_eq_rowFormula
    (stride : Nat) (h : Col -> Nat) (hh : forall c, h c <= 4096) (d : Col) :
    rowShiftLoad stride h d = rowShiftLoadByRows stride h d := by
  classical
  unfold rowShiftLoad rowShiftLoadByRows
  calc
    (Finset.univ.sum fun c : Col =>
      ((Finset.range (h c)).filter fun row =>
        (c.val + stride * row) % 64 = d.val).card) =
      Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun r : Row =>
          if r.val < h c /\ (c.val + stride * r.val) % 64 = d.val then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact card_range_filter_eq_fin_sum (h c) (hh c)
          (fun row => (c.val + stride * row) % 64 = d.val)
    _ = Finset.univ.sum fun r : Row =>
        Finset.univ.sum fun c : Col =>
          if r.val < h c /\ (c.val + stride * r.val) % 64 = d.val then 1 else 0 :=
        Finset.sum_comm
    _ =
      Finset.univ.sum fun r : Row =>
        if r.val < h ((shift64 (stride * r.val)).symm d) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          let e := shift64 (stride * r.val)
          have heq (c : Col) : (c.val + stride * r.val) % 64 = d.val <-> e c = d := by
            dsimp [e, shift64]
            constructor
            · intro h
              exact Fin.ext h
            · intro h
              exact congrArg Fin.val h
          let F : Col -> Nat := fun j =>
            if r.val < h (e.symm j) /\ j = d then 1 else 0
          calc
            (Finset.univ.sum fun c : Col =>
              if r.val < h c /\ (c.val + stride * r.val) % 64 = d.val then 1 else 0) =
              Finset.univ.sum fun c : Col => F (e c) := by
                apply Finset.sum_congr rfl
                intro c hc
                simp [F, heq]
            _ = Finset.univ.sum fun c : Col => F c := Equiv.sum_comp e F
            _ = if r.val < h (e.symm d) then 1 else 0 := by
              by_cases hp : r.val < h (e.symm d)
              · have hset : Finset.univ.filter
                    (fun j : Col => r.val < h (e.symm j) /\ j = d) = {d} := by
                  ext j
                  simp [hp] <;> intro hjd <;> simpa [hjd] using hp
                dsimp [F]
                rw [Finset.sum_boole, hset]
                simp <;> omega
              · have hset : Finset.univ.filter
                    (fun j : Col => r.val < h (e.symm j) /\ j = d) = ∅ := by
                  ext j
                  simp [hp] <;> intro hP <;> intro hjd <;>
                    exact hp (by simpa [hjd] using hP)
                dsimp [F]
                rw [Finset.sum_boole, hset]
                simp <;> omega
    _ = _ := rfl

theorem slope35PhysicalOutputHeight_eq_rowShiftLoad
    (h : Col -> Nat) (d : Col) :
    slope35PhysicalOutputHeight h d = rowShiftLoad 35 h d := by
  rfl

/-- The second lifted slope formula is just a stride-25 row shift after
relabeling its source columns by the permutation `c ↦ 35*c mod 64`. -/
theorem slope25_relabel_eq_rowShiftLoad
    (h : Col -> Nat) (d : Col) :
    slope25PhysicalOutputHeight (fun c => h (mul35Equiv c)) d =
      rowShiftLoad 25 h d := by
  classical
  unfold slope25PhysicalOutputHeight rowShiftLoad
  let F : Col -> Nat := fun c =>
    ((Finset.range (h c)).filter fun row =>
      (c.val + 25 * row) % 64 = d.val).card
  calc
    (Finset.univ.sum fun c : Col =>
      ((Finset.range (h (mul35Equiv c))).filter fun row =>
        (35 * c.val + 25 * row) % 64 = d.val).card) =
      Finset.univ.sum fun c : Col => F (mul35Equiv c) := by
        apply Finset.sum_congr rfl
        intro c hc
        dsimp [F]
        congr 1
        ext row
        simp only [Finset.mem_filter, Finset.mem_range]
        have heq : (35 * c.val + 25 * row) % 64 =
            ((mul35Equiv c).val + 25 * row) % 64 := by
          rw [show (mul35Equiv c).val = (35 * c.val) % 64 by rfl]
          calc
            (35 * c.val + 25 * row) % 64 =
                ((35 * c.val) % 64 + (25 * row) % 64) % 64 := Nat.add_mod _ _ _
            _ = ((35 * c.val) % 64 + 25 * row) % 64 := by
              have hA : ((35 * c.val) % 64) % 64 = (35 * c.val) % 64 :=
                Nat.mod_mod _ _
              have hm := Nat.add_mod ((35 * c.val) % 64) (25 * row) 64
              rw [hA] at hm
              exact hm.symm
        constructor
        · intro hr
          exact ⟨hr.1, heq.symm.trans hr.2⟩
        · intro hr
          exact ⟨hr.1, heq.trans hr.2⟩
    _ = Finset.univ.sum fun c : Col => F c := Equiv.sum_comp mul35Equiv F

/-- The lifted two-shuffle profile is exactly the composition of stride-35
and stride-25 row-shift load transitions. -/
theorem fullHeightTwoShuffle_eq_two_rowShiftLoads
    (h : Col -> Nat) (d : Col) :
    fullHeightTwoShuffle h d = rowShiftLoad 25 (rowShiftLoad 35 h) d := by
  unfold fullHeightTwoShuffle
  have hlift : liftSlope35Destination = mul35Equiv := by
    funext c
    apply Fin.ext
    rfl
  rw [hlift, slope25_relabel_eq_rowShiftLoad]
  apply congrArg (fun h' : Col -> Nat => rowShiftLoad 25 h' d)
  funext c
  exact slope35PhysicalOutputHeight_eq_rowShiftLoad h c

/-- The two-shuffle core preserves a uniform partial row-height cap. This is
the padding fact needed to apply the fixed 4096-row core to a shorter final
tile without charging errors for its all-one padding rows. -/
theorem fullHeightTwoShuffle_le_of_height_le
    (h : Col -> Nat) (m : Nat) (hm : m <= 4096)
    (hh : forall c, h c <= m) (d : Col) :
    fullHeightTwoShuffle h d <= m := by
  have hboundInput (c : Col) : h c <= 4096 := (hh c).trans hm
  have hfirst (c : Col) : rowShiftLoad 35 h c <= m := by
    rw [rowShiftLoad_eq_rowFormula 35 h hboundInput c]
    exact rowShiftLoadByRows_le_of_height_le 35 h m hm hh c
  have hfirst4096 (c : Col) : rowShiftLoad 35 h c <= 4096 :=
    (hfirst c).trans hm
  let h1 : Col -> Nat := fun c => rowShiftLoadByRows 35 h c
  have hh1 (c : Col) : h1 c <= m :=
    rowShiftLoadByRows_le_of_height_le 35 h m hm hh c
  rw [fullHeightTwoShuffle_eq_two_rowShiftLoads]
  have hfirstEq : rowShiftLoad 35 h = h1 := by
    funext c
    exact rowShiftLoad_eq_rowFormula 35 h hboundInput c
  rw [hfirstEq]
  change rowShiftLoad 25 h1 d <= m
  rw [rowShiftLoad_eq_rowFormula 25 h1 (fun c => (hh1 c).trans hm) d]
  apply rowShiftLoadByRows_le_of_height_le 25 h1 m hm
  exact hh1

/-- The physical two-shuffle height profile preserves total marked mass. -/
theorem fullHeightTwoShuffle_total (h : Col -> Nat) (hh : forall c, h c <= 4096) :
    Finset.univ.sum (fun d : Col => fullHeightTwoShuffle h d) = Finset.univ.sum h := by
  classical
  let h1 : Col -> Nat := fun c => rowShiftLoadByRows 35 h c
  have hh1 (c : Col) : h1 c <= 4096 := by
    unfold h1 rowShiftLoadByRows
    calc
      (Finset.univ.sum fun r : Row =>
        if r.val < h ((shift64 (35 * r.val)).symm c) then 1 else 0) <=
        Finset.univ.sum fun _ : Row => 1 := by
          apply Finset.sum_le_sum
          intro r hr
          split_ifs <;> omega
      _ = 4096 := by simp [Finset.sum_const, Fintype.card_fin]
  have hinner (d : Col) :
      fullHeightTwoShuffle h d = rowShiftLoadByRows 25 h1 d := by
    rw [fullHeightTwoShuffle_eq_two_rowShiftLoads]
    calc
      rowShiftLoad 25 (rowShiftLoad 35 h) d = rowShiftLoad 25 h1 d := by
        exact congrArg (fun p : Col -> Nat => rowShiftLoad 25 p d)
          (by
            funext c
            exact rowShiftLoad_eq_rowFormula 35 h hh c)
      _ = rowShiftLoadByRows 25 h1 d := rowShiftLoad_eq_rowFormula 25 h1 hh1 d
  calc
    Finset.univ.sum (fun d : Col => fullHeightTwoShuffle h d) =
        Finset.univ.sum (fun d : Col => rowShiftLoadByRows 25 h1 d) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hinner d
    _ = Finset.univ.sum h1 := rowShiftLoadByRows_total 25 h1 hh1
    _ = Finset.univ.sum h := rowShiftLoadByRows_total 35 h hh

/-- The semantic two-stage output uses exactly the paper's finite lifted
two-shuffle height profile. -/
theorem semanticExec2_two_stride_eq_fullHeight
    (h : Col -> Nat) (hh : forall c, h c <= 4096) :
    Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25)
        (lowPrefixBool h) =
      lowPrefixBool (fun d => fullHeightTwoShuffle h d) := by
  classical
  let h1 : Col -> Nat := fun c => rowShiftLoadByRows 35 h c
  have hh1 (c : Col) : h1 c <= 4096 := by
    change rowShiftLoadByRows 35 h c <= 4096
    rw [← semanticExec_stride_falseCount 35 h hh c]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hin : h1 = rowShiftLoad 35 h := by
    funext c
    exact (rowShiftLoad_eq_rowFormula 35 h hh c).symm
  have hprofile :
      (fun d => rowShiftLoadByRows 25 h1 d) =
        (fun d => fullHeightTwoShuffle h d) := by
    funext d
    calc
      rowShiftLoadByRows 25 h1 d = rowShiftLoad 25 h1 d :=
        (rowShiftLoad_eq_rowFormula 25 h1 hh1 d).symm
      _ = fullHeightTwoShuffle h d := by
        rw [fullHeightTwoShuffle_eq_two_rowShiftLoads]
        exact congrArg (fun p : Col -> Nat => rowShiftLoad 25 p d) hin
  rw [semanticExec2_two_stride_eq_prefix h hh]
  exact congrArg lowPrefixBool hprofile

/-- The actual D2 two-shuffle transition applies to any already-sorted
columns, with its input profile extracted from the wire matrix. -/
theorem semanticExec2_two_stride_eq_fullHeight_of_columnMonotone
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v =
      lowPrefixBool (fun d => fullHeightTwoShuffle
        (fun c => matrixColumnFalseCount c v) d) := by
  classical
  let h : Col -> Nat := fun c => matrixColumnFalseCount c v
  have hh (c : Col) : h c <= 4096 := by
    change matrixColumnFalseCount c v <= 4096
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hrepr : v = lowPrefixBool h := by
    simpa [h] using columnMonotone_eq_lowPrefixBool v hmono
  calc
    Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v =
        Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25)
          (lowPrefixBool h) := congrArg _ hrepr
    _ = lowPrefixBool (fun d => fullHeightTwoShuffle h d) :=
      semanticExec2_two_stride_eq_fullHeight h hh

/-- The fixed two-shuffle macro maps the column-sorted Boolean state space
back into itself, with the exact output profile supplied above. -/
theorem semanticExec2_two_stride_preserves_columnMonotone
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    Chvatal.ColumnMonotoneInput 4096 64 (by omega)
      (Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v) := by
  rw [semanticExec2_two_stride_eq_fullHeight_of_columnMonotone v hmono]
  exact lowPrefixBool_columnMonotone _

private theorem lowPrefixBool_row_band
    (p : Col -> Nat) (mu : Rat)
    (hdev : forall c, mu - 52 <= (p c : Rat) /\ (p c : Rat) <= mu + 52) :
    (forall w, lowPrefixBool p w = false ->
      ((Chvatal.matrixRow 4096 64 (by omega) w).val : Rat) < mu + 52) /\
    (forall w, lowPrefixBool p w = true ->
      mu - 52 <= (Chvatal.matrixRow 4096 64 (by omega) w).val) := by
  constructor
  · intro w hw
    let r := Chvatal.matrixRow 4096 64 (by omega) w
    let c := Chvatal.matrixCol 4096 64 (by omega) w
    have hdec : decide (p c <= r.val) = false := by
      simpa only [lowPrefixBool] using hw
    have hltN : r.val < p c := Nat.lt_of_not_ge (of_decide_eq_false hdec)
    have hltR : (r.val : Rat) < (p c : Rat) := by exact_mod_cast hltN
    linarith [(hdev c).2]
  · intro w hw
    let r := Chvatal.matrixRow 4096 64 (by omega) w
    let c := Chvatal.matrixCol 4096 64 (by omega) w
    have hdec : decide (p c <= r.val) = true := by
      simpa only [lowPrefixBool] using hw
    have hleN : p c <= r.val := of_decide_eq_true hdec
    have hleR : (p c : Rat) <= r.val := by exact_mod_cast hleN
    linarith [(hdev c).1]

/-- The 52-row deviation theorem localizes every Boolean output of the
two-shuffle macro to a fixed band around the mean row of its global cut. -/
theorem semanticExec2_two_stride_row_band
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    let x : Col -> Rat := fun c =>
      fullHeightTwoShuffle (fun j => matrixColumnFalseCount j v) c
    let mu : Rat := (Finset.univ.sum fun c : Col => x c) / 64
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = false ->
      ((Chvatal.matrixRow 4096 64 (by omega) w).val : Rat) < mu + 52) /\
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = true ->
      mu - 52 <= (Chvatal.matrixRow 4096 64 (by omega) w).val) := by
  classical
  let p : Col -> Nat := fun c =>
    fullHeightTwoShuffle (fun j => matrixColumnFalseCount j v) c
  let x : Col -> Rat := fun c => p c
  let mu : Rat := (Finset.univ.sum fun c : Col => x c) / 64
  have hdev := fullHeightTwoShuffle_column_deviation_le_52
    (fun j => matrixColumnFalseCount j v)
  change forall c : Col, mu - 52 <= x c /\ x c <= mu + 52 at hdev
  have hband := lowPrefixBool_row_band p mu (by
    intro c
    exact hdev c)
  constructor
  · intro w hw
    have hw' : lowPrefixBool p w = false := by
      rw [<- semanticExec2_two_stride_eq_fullHeight_of_columnMonotone v hmono]
      exact hw
    exact hband.1 w hw'
  · intro w hw
    have hw' : lowPrefixBool p w = true := by
      rw [<- semanticExec2_two_stride_eq_fullHeight_of_columnMonotone v hmono]
      exact hw
    exact hband.2 w hw'

/-- In flattened row-major wire order, every false/true disagreement with
the globally sorted Boolean cut lies within 53 rows of that cut. -/
theorem semanticExec2_two_stride_flat_cut_band
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    let p : Col -> Nat := fun c =>
      fullHeightTwoShuffle (fun j => matrixColumnFalseCount j v) c
    let total : Rat := Finset.univ.sum fun c : Col => (p c : Rat)
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = false -> (w.val : Rat) < total + 3392) /\
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = true -> total <= (w.val : Rat) + 3392) := by
  classical
  let p : Col -> Nat := fun c =>
    fullHeightTwoShuffle (fun j => matrixColumnFalseCount j v) c
  let total : Rat := Finset.univ.sum fun c : Col => (p c : Rat)
  have hband := semanticExec2_two_stride_row_band v hmono
  have hmu : ((Finset.univ.sum fun c : Col => (p c : Rat)) / 64 : Rat) = total / 64 := by
    rfl
  constructor
  · intro w hw
    have hr := hband.1 w hw
    let r := Chvatal.matrixRow 4096 64 (by omega) w
    let c := Chvatal.matrixCol 4096 64 (by omega) w
    have hwireN : w.val = r.val * 64 + c.val := by
      calc
        w.val = 64 * (w.val / 64) + w.val % 64 := (Nat.div_add_mod _ _).symm
        _ = r.val * 64 + c.val := by simp [r, c, Chvatal.matrixRow_val,
          Chvatal.matrixCol_val, Nat.mul_comm]
    have hwire : (w.val : Rat) = (r.val : Rat) * 64 + c.val := by
      exact_mod_cast hwireN
    have hrMul : (r.val : Rat) * 64 < total + 3328 := by
      rw [<- hmu] at hr
      nlinarith
    have hc : (c.val : Rat) < 64 := by exact_mod_cast c.isLt
    rw [hwire]
    linarith
  · intro w hw
    have hr := hband.2 w hw
    let r := Chvatal.matrixRow 4096 64 (by omega) w
    let c := Chvatal.matrixCol 4096 64 (by omega) w
    have hwireN : w.val = r.val * 64 + c.val := by
      calc
        w.val = 64 * (w.val / 64) + w.val % 64 := (Nat.div_add_mod _ _).symm
        _ = r.val * 64 + c.val := by simp [r, c, Chvatal.matrixRow_val,
          Chvatal.matrixCol_val, Nat.mul_comm]
    have hwire : (w.val : Rat) = (r.val : Rat) * 64 + c.val := by
      exact_mod_cast hwireN
    have hrMul : total - 3328 <= (r.val : Rat) * 64 := by
      rw [<- hmu] at hr
      nlinarith
    have hc : 0 <= (c.val : Rat) := Nat.cast_nonneg _
    rw [hwire]
    linarith

/-- The Boolean cut in the flat-band theorem is exactly the input cut mass. -/
theorem semanticExec2_two_stride_flat_cut_band_input_total
    (v : Fin (4096 * 64) -> Bool)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v) :
    let sourceTotal : Rat :=
      ((Finset.univ.filter fun w : Fin (4096 * 64) => v w = false).card : Nat)
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = false -> (w.val : Rat) < sourceTotal + 3392) /\
    (forall w, Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v w = true -> sourceTotal <= (w.val : Rat) + 3392) := by
  classical
  let h : Col -> Nat := fun c => matrixColumnFalseCount c v
  let p : Col -> Nat := fun c => fullHeightTwoShuffle h c
  let sourceTotal : Rat :=
    ((Finset.univ.filter fun w : Fin (4096 * 64) => v w = false).card : Nat)
  have hh (c : Col) : h c <= 4096 := by
    change matrixColumnFalseCount c v <= 4096
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hprofile := fullHeightTwoShuffle_total h hh
  have hinput := matrixFalseTotal_eq_sumColumns v
  have htotal : (Finset.univ.sum fun c : Col => (p c : Rat)) = sourceTotal := by
    dsimp [sourceTotal, p, h]
    have hNat := hprofile.trans hinput.symm
    exact_mod_cast hNat
  obtain ⟨hLow, hHigh⟩ := semanticExec2_two_stride_flat_cut_band v hmono
  constructor
  · intro w hw
    have hb := hLow w hw
    rw [htotal] at hb
    exact hb
  · intro w hw
    have hb := hHigh w hw
    rw [htotal] at hb
    exact hb

def countValuesLT {α : Type} [LinearOrder α]
    (v : Fin (4096 * 64) -> α) (a : α) : Nat :=
  (Finset.univ.filter fun q => v q < a).card

def countValuesLE {α : Type} [LinearOrder α]
    (v : Fin (4096 * 64) -> α) (a : α) : Nat :=
  (Finset.univ.filter fun q => v q <= a).card

/-- On inputs already sorted within columns, the two-shuffle core places each
output value within 3392 wires of its global rank interval. The lower and
upper rank counts accommodate equal keys; with distinct keys this is the
usual pointwise displacement bound. -/
theorem semanticExec2_two_stride_rank_interval
    {α : Type} [LinearOrder α] (v : Fin (4096 * 64) -> α)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v)
    (w : Fin (4096 * 64)) :
    countValuesLT v (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w) <= w.val + 3392 /\
    w.val < countValuesLE v (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w) + 3392 := by
  classical
  let y := Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v
  let a := y w
  let fLo : α -> Bool := fun x => decide (a <= x)
  have hfLo : Monotone fLo := by
    intro x z hxz
    by_cases hx : a <= x
    · have hz : a <= z := le_trans hx hxz
      simp [fLo, hx, hz]
    · simp [fLo, hx]
  let vLo := fLo ∘ v
  have hmonoLo : Chvatal.ColumnMonotoneInput 4096 64 (by omega) vLo := by
    intro j r s hrs
    exact hfLo (hmono j hrs)
  have hcutLo := semanticExec2_two_stride_flat_cut_band_input_total vLo hmonoLo
  have hcommLo := semanticExec2_comp_monotone (by omega)
    (strideScramble 35) (strideScramble 25) fLo hfLo v
  have hbitLo : Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) vLo w = true := by
    have heq := congrFun hcommLo w
    change fLo (y w) = Chvatal.semanticExec2 (by omega)
      (strideScramble 35) (strideScramble 25) vLo w at heq
    have htriv : fLo (y w) = true := by simp [fLo, a]
    rw [htriv] at heq
    exact heq.symm
  have hsourceLo :
      (Finset.univ.filter fun q : Fin (4096 * 64) => vLo q = false).card =
        countValuesLT v a := by
    simp [vLo, fLo, countValuesLT, a, not_le]
  have hboundLo := hcutLo.2 w hbitLo
  change ((Finset.univ.filter fun q : Fin (4096 * 64) => vLo q = false).card : Rat) <=
    (w.val : Rat) + 3392 at hboundLo
  rw [hsourceLo] at hboundLo

  let fHi : α -> Bool := fun x => decide (a < x)
  have hfHi : Monotone fHi := by
    intro x z hxz
    by_cases hx : a < x
    · have hz : a < z := lt_of_lt_of_le hx hxz
      simp [fHi, hx, hz]
    · simp [fHi, hx]
  let vHi := fHi ∘ v
  have hmonoHi : Chvatal.ColumnMonotoneInput 4096 64 (by omega) vHi := by
    intro j r s hrs
    exact hfHi (hmono j hrs)
  have hcutHi := semanticExec2_two_stride_flat_cut_band_input_total vHi hmonoHi
  have hcommHi := semanticExec2_comp_monotone (by omega)
    (strideScramble 35) (strideScramble 25) fHi hfHi v
  have hbitHi : Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) vHi w = false := by
    have heq := congrFun hcommHi w
    change fHi (y w) = Chvatal.semanticExec2 (by omega)
      (strideScramble 35) (strideScramble 25) vHi w at heq
    have htriv : fHi (y w) = false := by simp [fHi, a]
    rw [htriv] at heq
    exact heq.symm
  have hsourceHi :
      (Finset.univ.filter fun q : Fin (4096 * 64) => vHi q = false).card =
        countValuesLE v a := by
    simp [vHi, fHi, countValuesLE, a, not_lt]
  have hboundHi := hcutHi.1 w hbitHi
  change (w.val : Rat) <
    (Finset.univ.filter fun q : Fin (4096 * 64) => vHi q = false).card + 3392 at hboundHi
  rw [hsourceHi] at hboundHi
  constructor
  · exact_mod_cast hboundLo
  · exact_mod_cast hboundHi

end Chvatal.D2LiftedShuffleBridge
