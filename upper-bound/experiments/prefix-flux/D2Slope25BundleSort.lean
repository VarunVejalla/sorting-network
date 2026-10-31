import D2Slope25Sparse40
import AKS.Chvatal.MatrixBridge
import AKS.Chvatal.PhysicalPack
import AKS.Chvatal.SeparatorDepth
import AKS.Chvatal.SortedColumnDecode
import D2Slope25Lift

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Chvatal.D2Slope25BundleSort

open Chvatal
open Chvatal.D2Slope25Sparse40

abbrev Col := Fin 64
abbrev Wire := Fin (64 * 64)

private theorem cols_pos : 0 < 64 := by omega

/-- A row's occupied columns are an initial interval of this width. -/
def rowPrefixTile (width : Col → Nat) (w : Wire) : Bool :=
  decide ((matrixCol 64 64 cols_pos w).val < width (matrixRow 64 64 cols_pos w))

/-- Cyclic translation on the 64 columns. -/
def cyclicShift64 (start : Nat) : Equiv.Perm Col where
  toFun c := ⟨(c.val + start) % 64, Nat.mod_lt _ (by omega)⟩
  invFun c := ⟨(c.val + 64 - start % 64) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv c := by
    apply Fin.ext
    simp only
    omega
  right_inv c := by
    apply Fin.ext
    simp only
    omega

/-- The round-1 cyclic row scramble used by `slope25Load`. -/
def slope25Scramble : Scramble 64 64 := fun r => cyclicShift64 (25 * r.val)

def slope39Scramble : Scramble 64 64 := fun r => cyclicShift64 (39 * r.val)

private theorem cyclicShift64_inv_lt_iff (start : Nat) (target : Col) (width : Nat) :
    ((cyclicShift64 start).symm target).val < width ↔
      forwardNeed target.val start ≤ width := by
  change (target + 64 - start % 64) % 64 < width ↔
    (target + 64 - start % 64) % 64 + 1 ≤ width
  omega

/-- After the actual wire permutation for the cyclic row scramble, row `r`
contributes a one to output column `target` exactly when counted by the
stride-25 load formula. -/
theorem slope25Scramble_rowPrefix_action (width : Col → Nat) (r target : Col) :
    (rowPrefixTile width ∘
      (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm)
        (matrixWire 64 64 r target) =
      decide (forwardNeed target.val (25 * r.val) ≤ width r) := by
  change rowPrefixTile width
      ((rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm
        (matrixWire 64 64 r target)) = _
  rw [rowScrambleWirePerm_symm_apply]
  simp only [rowPrefixTile, matrixWire_row_col]
  dsimp [slope25Scramble]
  have hiff := cyclicShift64_inv_lt_iff (25 * r.val) target (width r)
  by_cases h : ((cyclicShift64 (25 * r.val)).symm target).val < width r
  · have h' := hiff.mp h
    simp [h, h']
  · have h' : ¬ forwardNeed target.val (25 * r.val) ≤ width r :=
      fun h' => h (hiff.mpr h')
    simp [h, h']

/-- The stride-25 profile operator is the exact column-height output of the
physical row scramble on a row-prefix tile. -/
theorem slope25Scramble_columnCount (width : Col → Nat) (target : Col) :
    matrixColumnTrueCount target
        (rowPrefixTile width ∘
          (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm) =
      slope25Load width target := by
  unfold matrixColumnTrueCount slope25Load
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [slope25Scramble_rowPrefix_action]
  simp

def slope39Load (profile : Col → Nat) (target : Col) : Nat :=
  (Finset.univ.filter fun r : Col =>
    forwardNeed target.val (39 * r.val) ≤ profile r).card

theorem slope39Scramble_rowPrefix_action (width : Col → Nat) (r target : Col) :
    (rowPrefixTile width ∘
      (rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm)
        (matrixWire 64 64 r target) =
      decide (forwardNeed target.val (39 * r.val) ≤ width r) := by
  change rowPrefixTile width
      ((rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm
        (matrixWire 64 64 r target)) = _
  rw [rowScrambleWirePerm_symm_apply]
  simp only [rowPrefixTile, matrixWire_row_col]
  dsimp [slope39Scramble]
  have hiff := cyclicShift64_inv_lt_iff (39 * r.val) target (width r)
  by_cases h : ((cyclicShift64 (39 * r.val)).symm target).val < width r
  · have h' := hiff.mp h
    simp [h, h']
  · have h' : ¬ forwardNeed target.val (39 * r.val) ≤ width r :=
      fun h' => h (hiff.mpr h')
    simp [h, h']

theorem slope39Scramble_columnCount (width : Col → Nat) (target : Col) :
    matrixColumnTrueCount target
        (rowPrefixTile width ∘
          (rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm) =
      slope39Load width target := by
  unfold matrixColumnTrueCount slope39Load
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [slope39Scramble_rowPrefix_action]
  simp

/-- Transpose the row-major coordinates of a 64 by 64 tile. -/
def transposeWire (w : Wire) : Wire :=
  matrixWire 64 64 (matrixCol 64 64 cols_pos w) (matrixRow 64 64 cols_pos w)

theorem transposeWire_matrixWire (r c : Col) :
    transposeWire (matrixWire 64 64 r c) = matrixWire 64 64 c r := by
  simp [transposeWire, matrixWire_row_col]

def transposeWireEquiv : Equiv.Perm Wire where
  toFun := transposeWire
  invFun := transposeWire
  left_inv := by
    intro w
    rw [← matrixWire_matrixRow_col cols_pos w]
    rw [transposeWire_matrixWire, transposeWire_matrixWire,
      matrixWire_matrixRow_col]
  right_inv := by
    intro w
    rw [← matrixWire_matrixRow_col cols_pos w]
    rw [transposeWire_matrixWire, transposeWire_matrixWire,
      matrixWire_matrixRow_col]

theorem transposeWireEquiv_symm_matrixWire (r c : Col) :
    transposeWireEquiv.symm (matrixWire 64 64 r c) = matrixWire 64 64 c r := by
  have he : transposeWireEquiv (matrixWire 64 64 c r) = matrixWire 64 64 r c := by
    change transposeWire (matrixWire 64 64 c r) = matrixWire 64 64 r c
    exact transposeWire_matrixWire c r
  rw [← he]
  exact transposeWireEquiv.symm_apply_apply _

def reflectColumn64 (c : Col) : Col := ⟨63 - c.val, by omega⟩

def transposeReflectTile (v : Wire → Bool) (w : Wire) : Bool :=
  v (matrixWire 64 64 (reflectColumn64 (matrixCol 64 64 cols_pos w))
    (matrixRow 64 64 cols_pos w))

def rowBundleSortBase : ComparatorNetwork (64 * 64) :=
  columnSortNetwork 64 64 cols_pos

theorem transpose_column_comparators_ordered :
    ∀ c ∈ rowBundleSortBase.comparators,
      transposeWireEquiv c.i < transposeWireEquiv c.j := by
  intro c hc
  obtain ⟨j, r, s, hi, hj⟩ :=
    columnSortNetwork_columnLocal 64 64 cols_pos c hc
  have hrs : r.val < s.val := by
    apply (matrixWire_row_lt_iff cols_pos j).mp
    rw [← hi, ← hj]
    exact c.h
  rw [hi, hj]
  change transposeWire (matrixWire 64 64 r j) <
    transposeWire (matrixWire 64 64 s j)
  rw [transposeWire_matrixWire, transposeWire_matrixWire]
  apply Fin.mk_lt_mk.mpr
  omega

/-- A standard comparator network acting independently along every row. This
is the transpose relabeling of the existing, verified column sorter. -/
def rowBundleSortNet : ComparatorNetwork (64 * 64) :=
  relabelNet transposeWireEquiv rowBundleSortBase
    transpose_column_comparators_ordered

theorem rowBundleSortNet_depth_le_21 : rowBundleSortNet.depth ≤ 21 := by
  have hdepth := relabelNet_depth transposeWireEquiv rowBundleSortBase
    transpose_column_comparators_ordered
  have hbase := columnSortNetwork_depth_le_budget 64 64 cols_pos
  have hclog : Nat.clog 2 64 = 6 := by decide
  calc
    rowBundleSortNet.depth = rowBundleSortBase.depth := by
      exact hdepth
    _ ≤ bitonicDepthBudget (Nat.clog 2 64) := hbase
    _ = 6 * 7 / 2 := by rw [hclog, bitonicDepthBudget_eq]
    _ = 21 := by norm_num

/-- Wire-level action of the flattened row-parallel sorter, expressed as the
standard 64-wire bitonic network on each row. -/
theorem rowBundleSortNet_exec_matrixWire {α : Type*} [LinearOrder α]
    (v : Wire → α) (r c : Col) :
    rowBundleSortNet.exec v (matrixWire 64 64 r c) =
      (bitonicNetwork 64).exec (fun j : Col => v (matrixWire 64 64 r j)) c := by
  have hrel := relabelNet_exec transposeWireEquiv rowBundleSortBase
    transpose_column_comparators_ordered v
  have hpoint := congrFun hrel (matrixWire 64 64 r c)
  rw [rowBundleSortNet, hpoint, transposeWireEquiv_symm_matrixWire]
  have hcolumn := columnSortNetwork_exec_matrixWire cols_pos r
    (v := v ∘ transposeWireEquiv) c
  have hcolumnBase : rowBundleSortBase.exec (v ∘ transposeWireEquiv)
      (matrixWire 64 64 c r) =
      (bitonicNetwork 64).exec
        ((v ∘ transposeWireEquiv) ∘ columnWireEmbed 64 64 cols_pos r) c := hcolumn
  rw [hcolumnBase]
  have hvector :
      (v ∘ transposeWireEquiv) ∘ columnWireEmbed 64 64 cols_pos r =
        fun j : Col => v (matrixWire 64 64 r j) := by
    funext j
    change v (transposeWire (matrixWire 64 64 j r)) = _
    rw [transposeWire_matrixWire]
  rw [hvector]

/-- Unary-column encoding with ones in the first `height c` rows. -/
def unaryTile (height : Col → Nat) (w : Wire) : Bool :=
  decide ((matrixRow 64 64 cols_pos w).val < height (matrixCol 64 64 cols_pos w))

theorem rowBundleSortNet_exec_unary (height : Col → Nat) (r c : Col) :
    rowBundleSortNet.exec (unaryTile height) (matrixWire 64 64 r c) =
      decide (r.val < (bitonicNetwork 64).exec height c) := by
  rw [rowBundleSortNet_exec_matrixWire]
  have hrow :
      (fun j : Col => unaryTile height (matrixWire 64 64 r j)) =
        fun j : Col => decide (r.val < height j) := by
    funext j
    simp [unaryTile, matrixWire_row_col]
  rw [hrow]
  exact comparatorNetwork_exec_unaryThreshold (bitonicNetwork 64) height r c

/-- Unary-column encoding with ones in the last `height c` rows, matching the
output orientation of the standard ascending column sorter. -/
def unaryBottomTile (height : Col → Nat) (w : Wire) : Bool :=
  decide (64 - height (matrixCol 64 64 cols_pos w) ≤
    (matrixRow 64 64 cols_pos w).val)

/-- Transpose a bottom-suffix unary tile and reflect its columns. The result
is the row-prefix encoding of the same height vector. This is the orientation
change needed to reuse the stride profile recurrence on the next pass. -/
theorem transposeReflect_unaryBottom (height : Col → Nat)
    (hbound : ∀ c, height c ≤ 64) :
    transposeReflectTile (unaryBottomTile height) = rowPrefixTile height := by
  funext w
  rw [← matrixWire_matrixRow_col cols_pos w]
  simp only [transposeReflectTile, rowPrefixTile, unaryBottomTile,
    matrixWire_row_col]
  simp only [reflectColumn64]
  let r := matrixRow 64 64 cols_pos w
  let c := matrixCol 64 64 cols_pos w
  change decide (64 - height r ≤ 63 - c.val) = decide (c.val < height r)
  by_cases h : c.val < height r
  · have h' : 64 - height r ≤ 63 - c.val := by have hb := hbound r; omega
    simp [h, h']
  · have h' : ¬ 64 - height r ≤ 63 - c.val := by
      intro h'
      have hb := hbound r
      omega
    simp [h, h']

theorem comparatorNetwork_exec_unaryBottom
    (net : ComparatorNetwork 64) (height : Col → Nat) (row : Col) (column : Col) :
    net.exec (fun c : Col => decide (64 - height c ≤ row.val)) column =
      decide (64 - net.exec height column ≤ row.val) := by
  let threshold : Nat → Bool := fun x => decide (64 - x ≤ row.val)
  have hthreshold : Monotone threshold := by
    intro a b hab
    have hsub : 64 - b ≤ 64 - a := Nat.sub_le_sub_left hab 64
    by_cases ha : 64 - a ≤ row.val
    · have hb : 64 - b ≤ row.val := le_trans hsub ha
      have ha' : 64 ≤ row.val + a := by omega
      have hb' : 64 ≤ row.val + b := by omega
      have hta : threshold a = true := by simp [threshold, ha']
      have htb : threshold b = true := by simp [threshold, hb']
      rw [hta, htb]
    · have hta : threshold a = false := by
        have ha' : row.val + a < 64 := by omega
        simp [threshold, ha']
      rw [hta]
      simp
  have hcomm := ComparatorNetwork.exec_comp_monotone net hthreshold height
  have hpoint := congrFun hcomm column
  simpa [threshold, Function.comp] using hpoint.symm

theorem rowBundleSortNet_exec_unaryBottom (height : Col → Nat) (r c : Col) :
    rowBundleSortNet.exec (unaryBottomTile height) (matrixWire 64 64 r c) =
      decide (64 - (bitonicNetwork 64).exec height c ≤ r.val) := by
  rw [rowBundleSortNet_exec_matrixWire]
  have hrow :
      (fun j : Col => unaryBottomTile height (matrixWire 64 64 r j)) =
        fun j : Col => decide (64 - height j ≤ r.val) := by
    funext j
    simp [unaryBottomTile, matrixWire_row_col]
  rw [hrow]
  exact comparatorNetwork_exec_unaryBottom (bitonicNetwork 64) height r c

/-- The number of ones in each output bundle is exactly the scalar height
after the 64-wire sorter, with the same ascending comparator orientation. -/
theorem rowBundleSortNet_columnHeight (height : Col → Nat)
    (hbound : ∀ c, height c ≤ 64) (c : Col) :
    (Finset.univ.filter fun r : Col =>
      rowBundleSortNet.exec (unaryTile height) (matrixWire 64 64 r c) = true).card =
        (bitonicNetwork 64).exec height c := by
  have hsortedBound : (bitonicNetwork 64).exec height c ≤ 64 := by
    obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm
      (bitonicNetwork 64) height
    rw [hρ]
    exact hbound (ρ c)
  have hsets :
      (Finset.univ.filter fun r : Col =>
        rowBundleSortNet.exec (unaryTile height) (matrixWire 64 64 r c) = true) =
      Finset.univ.filter fun r : Col =>
        r.val < (bitonicNetwork 64).exec height c := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowBundleSortNet_exec_unary]
    simp
  rw [hsets]
  exact card_lt_fin _ hsortedBound

private theorem card_suffix_64 (k : Nat) (hk : k ≤ 64) :
    (Finset.univ.filter fun r : Col => 64 - k ≤ r.val).card = k := by
  have hlow :
      (Finset.univ.filter fun r : Col => r.val < 64 - k).card = 64 - k :=
    card_lt_fin (64 - k) (by omega)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Col))
    (p := fun r : Col => r.val < 64 - k)
  have huniv : (Finset.univ : Finset Col).card = 64 := by simp
  have hset :
      Finset.univ.filter (fun r : Col => ¬ r.val < 64 - k) =
        Finset.univ.filter (fun r : Col => 64 - k ≤ r.val) := by
    ext r
    simp
  rw [hset, huniv] at hpart
  omega

theorem matrixColumnTrueCount_unaryBottom (height : Col → Nat)
    (hbound : ∀ c, height c ≤ 64) (target : Col) :
    matrixColumnTrueCount target (unaryBottomTile height) = height target := by
  unfold matrixColumnTrueCount unaryBottomTile
  simp only [matrixWire_row_col]
  change (Finset.univ.filter fun r : Col =>
    decide (64 - height target ≤ r.val) = true).card = height target
  have hset :
      Finset.univ.filter (fun r : Col => decide (64 - height target ≤ r.val) = true) =
        Finset.univ.filter (fun r : Col => 64 - height target ≤ r.val) := by
    ext r
    simp
  rw [hset]
  exact card_suffix_64 (height target) (hbound target)

/-- For bottom-suffix unary columns, the bundled physical sorter outputs
bottom-suffix columns whose heights are exactly the standard ascending scalar
sort of the input heights. -/
theorem rowBundleSortNet_columnHeightBottom (height : Col → Nat)
    (hbound : ∀ c, height c ≤ 64) (c : Col) :
    (Finset.univ.filter fun r : Col =>
      rowBundleSortNet.exec (unaryBottomTile height) (matrixWire 64 64 r c) = true).card =
        (bitonicNetwork 64).exec height c := by
  have hsortedBound : (bitonicNetwork 64).exec height c ≤ 64 := by
    obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm
      (bitonicNetwork 64) height
    rw [hρ]
    exact hbound (ρ c)
  have hsets :
      (Finset.univ.filter fun r : Col =>
        rowBundleSortNet.exec (unaryBottomTile height) (matrixWire 64 64 r c) = true) =
      Finset.univ.filter fun r : Col =>
        64 - (bitonicNetwork 64).exec height c ≤ r.val := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowBundleSortNet_exec_unaryBottom]
    simp
  rw [hsets]
  exact card_suffix_64 _ hsortedBound

/-- A standard vertical column sort turns any Boolean matrix with the stated
column counts into the bottom-suffix unary encoding consumed by the row-bundle
sorter. -/
theorem columnSortNetwork_eq_unaryBottom_of_columnCounts
    (v : Wire → Bool) (height : Col → Nat)
    (hcount : ∀ c, matrixColumnTrueCount c v = height c) :
    (columnSortNetwork 64 64 cols_pos).exec v = unaryBottomTile height := by
  funext w
  rw [← matrixWire_matrixRow_col cols_pos w]
  unfold unaryBottomTile
  simp only [matrixWire_row_col]
  let r := matrixRow 64 64 cols_pos w
  let c := matrixCol 64 64 cols_pos w
  have hcm : ColumnMonotoneInput 64 64 cols_pos
      ((columnSortNetwork 64 64 cols_pos).exec v) :=
    columnSortNetwork_columnMonotone cols_pos v
  have hcounts (j : Col) :
      matrixColumnTrueCount j ((columnSortNetwork 64 64 cols_pos).exec v) = height j := by
    calc
      matrixColumnTrueCount j ((columnSortNetwork 64 64 cols_pos).exec v) =
          matrixColumnTrueCount j v :=
            matrixColumnTrueCount_exec_eq cols_pos j _
              (columnSortNetwork_columnLocal 64 64 cols_pos) v
      _ = height j := hcount j
  have hiff := colMono_true_iff cols_pos hcm r c
  rw [hcounts c] at hiff
  have hheight : height c ≤ 64 := by
    rw [← hcounts c]
    exact matrixColumnTrueCount_le c _
  have hpred : (64 - r.val ≤ height c) ↔ (64 - height c ≤ r.val) := by
    omega
  change (columnSortNetwork 64 64 cols_pos).exec v
      (matrixWire 64 64 r c) = decide (64 - height c ≤ r.val)
  by_cases h : 64 - height c ≤ r.val
  · have hout := hiff.mpr (hpred.mpr h)
    simpa [h] using hout
  · cases hout : (columnSortNetwork 64 64 cols_pos).exec v
        (matrixWire 64 64 r c) with
    | false => simp [h]
    | true => exact (h (hpred.mp (hiff.mp hout))).elim

/-- A rowwise 64-wire ascending sort followed by a vertical column sort acts
on a bottom-suffix unary tile by sorting its 64 column heights. This is the
physical network form of the scalar-height transition used by the D2 profile
calculation. -/
theorem columnSort_after_rowBundleSort_on_unaryBottom (height : Col → Nat)
    (hbound : ∀ c, height c ≤ 64) :
    (columnSortNetwork 64 64 cols_pos).exec
        (rowBundleSortNet.exec (unaryBottomTile height)) =
      unaryBottomTile ((bitonicNetwork 64).exec height) := by
  apply columnSortNetwork_eq_unaryBottom_of_columnCounts
  intro c
  exact rowBundleSortNet_columnHeightBottom height hbound c

/-- Sorting the columns after the actual stride-25 row scramble turns its
output into bottom-suffix unary columns with heights `slope25Load`. -/
theorem columnSort_after_slope25Scramble (width : Col → Nat) :
    (columnSortNetwork 64 64 cols_pos).exec
        (rowPrefixTile width ∘
          (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm) =
      unaryBottomTile (slope25Load width) := by
  apply columnSortNetwork_eq_unaryBottom_of_columnCounts
  exact slope25Scramble_columnCount width

theorem columnSort_after_slope39Scramble (width : Col → Nat) :
    (columnSortNetwork 64 64 cols_pos).exec
        (rowPrefixTile width ∘
          (rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm) =
      unaryBottomTile (slope39Load width) := by
  apply columnSortNetwork_eq_unaryBottom_of_columnCounts
  exact slope39Scramble_columnCount width

theorem slope25Load_le_64 (width : Col → Nat) (target : Col) :
    slope25Load width target ≤ 64 := by
  rw [← slope25Scramble_columnCount width target]
  exact matrixColumnTrueCount_le target _

theorem slope39Load_le_64 (width : Col → Nat) (target : Col) :
    slope39Load width target ≤ 64 := by
  rw [← slope39Scramble_columnCount width target]
  exact matrixColumnTrueCount_le target _

/-- Exact physical two-step realization of the sparse recurrence: scramble a
row-prefix tile by the stride-25 shifts, sort columns, sort each row by the
standard 64-wire network, and sort columns again. The output height profile
is precisely the scalar ascending sort of `slope25Load`. -/
theorem stride25SparsePhysical_twoStep (width : Col → Nat) :
    (columnSortNetwork 64 64 cols_pos).exec
        (rowBundleSortNet.exec
          ((columnSortNetwork 64 64 cols_pos).exec
            (rowPrefixTile width ∘
              (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm))) =
      unaryBottomTile ((bitonicNetwork 64).exec (slope25Load width)) := by
  rw [columnSort_after_slope25Scramble]
  exact columnSort_after_rowBundleSort_on_unaryBottom (slope25Load width)
    (fun c => slope25Load_le_64 width c)

/-- The stride-25/sort/stride-39 fragment realizes the full scalar recurrence
`profile ↦ slope25Load ↦ ascending-sort ↦ slope39Load`, including the transpose
and reflection needed to present the sorted vector as row-prefix widths again. -/
def stride25SortedTransposeTile (width : Col → Nat) : Wire → Bool :=
  transposeReflectTile
    ((columnSortNetwork 64 64 cols_pos).exec
      (rowBundleSortNet.exec
        ((columnSortNetwork 64 64 cols_pos).exec
          (rowPrefixTile width ∘
            (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm))))

theorem stride25SortedTransposeTile_eq_rowPrefix (width : Col → Nat) :
    stride25SortedTransposeTile width =
      rowPrefixTile ((bitonicNetwork 64).exec (slope25Load width)) := by
  let height := (bitonicNetwork 64).exec (slope25Load width)
  have hbound : ∀ c, height c ≤ 64 := by
    intro c
    obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm
      (bitonicNetwork 64) (slope25Load width)
    dsimp [height]
    rw [hρ]
    exact slope25Load_le_64 width (ρ c)
  funext w
  change transposeReflectTile
    ((columnSortNetwork 64 64 cols_pos).exec
      (rowBundleSortNet.exec
        ((columnSortNetwork 64 64 cols_pos).exec
          (rowPrefixTile width ∘
            (rowScrambleWirePerm 64 64 cols_pos slope25Scramble).symm)))) w = _
  rw [columnSort_after_slope25Scramble]
  rw [columnSort_after_rowBundleSort_on_unaryBottom (slope25Load width)
    (fun c => slope25Load_le_64 width c)]
  exact congrFun (transposeReflect_unaryBottom height hbound) w

theorem stride25SortStride39_physical (width : Col → Nat) :
    (columnSortNetwork 64 64 cols_pos).exec
      (stride25SortedTransposeTile width ∘
        (rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm) =
      unaryBottomTile
        (slope39Load ((bitonicNetwork 64).exec (slope25Load width))) := by
  rw [stride25SortedTransposeTile_eq_rowPrefix]
  exact columnSort_after_slope39Scramble
    ((bitonicNetwork 64).exec (slope25Load width))

/-- The physical stride-25/sort/stride-39 schedule has no repeated output
column on every nonincreasing row-width profile of mass at most40. This is
the sparse-edge gate for the concrete comparator schedule, not just its
abstract load recurrence. -/
theorem stride25SortStride39_sparse_gate (width : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → width s ≤ width r)
    (hmass : (∑ r : Col, width r) ≤ 40)
    (hbound : ∀ r, width r ≤ 64) :
    ∀ target : Col,
      slope39Load ((bitonicNetwork 64).exec (slope25Load width)) target ≤ 1 := by
  intro target
  simpa [slope39Load] using
    slope25_then_ascending_bitonic_stride39_no_collision width hmono hmass hbound target

/-- In the same sparse regime, the actual output of the physical comparator
schedule has at most one true wire in each column. -/
theorem stride25SortStride39_physical_columnCount_le_one (width : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → width s ≤ width r)
    (hmass : (∑ r : Col, width r) ≤ 40)
    (hbound : ∀ r, width r ≤ 64) (target : Col) :
    matrixColumnTrueCount target
      ((columnSortNetwork 64 64 cols_pos).exec
        (stride25SortedTransposeTile width ∘
          (rowScrambleWirePerm 64 64 cols_pos slope39Scramble).symm)) ≤ 1 := by
  rw [stride25SortStride39_physical]
  rw [matrixColumnTrueCount_unaryBottom]
  · exact stride25SortStride39_sparse_gate width hmono hmass hbound target
  · exact fun c => slope39Load_le_64 _ c

end Chvatal.D2Slope25BundleSort
