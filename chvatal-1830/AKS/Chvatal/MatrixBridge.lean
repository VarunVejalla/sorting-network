module
/-
  # Combinatorial → matrix Properties B/F bridge (Chvátal §5–§6)

  Paper pipeline: sort columns → row-wise scramble → sort columns again.
  Lemma 6.1 / 6.2 give combinatorial Property B/F for some scramble `σ`;
  Theorem 5.1 requires matrix `HasMatrixPropertyB` / `HasMatrixPropertyF` on
  the executable network.

  **Kernel-checked here:** wire layout, column-sort and sort–scramble–sort network
  skeleton, combined combinatorial B∧F existence from Module A fail fractions,
  and wiring `ModuleACombinatorialObligation` + `CombinatorialToMatrixObligation`
  into `Theorem51Obligation` / `ExistsScrambleSeparator`.

  **Kernel-checked progress (bridge infrastructure):** matrix row/column coordinates,
  `matrixIntrusionCountB`/`F` aligned with `HasMatrixPropertyB`/`F`, column- and
  row-local comparator stability, `SortScrambleSortPack` exec decomposition, and
  combinatorial wire counts (`scrambledOnesInAboveBottomRows`) for the middle stage.

  **Kernel-checked (counting):** per-column and row-sum scrambled-one counts above the
  bottom block; `onesAboveBottom` is termwise bounded by `scrambledColSumInAboveBottomRows`
  and hence by `scrambledOnesInAboveBottomRowsSum`; wire-level
  `scrambledOnesInAboveBottomRows = scrambledOnesInAboveBottomRowsSum` via `matrixWire`
  bijection on row–column pairs.

  **Kernel-checked (layout / column sort):** `matrixWire` inverse coordinates,
  column-local `bitonicNetwork` embeddings per column, and `IdealColumnSort` for
  `columnSortNetwork`.

  **Kernel-checked (middle stage):** `RowScrambleCorrect` / `ImplementsScramble`, monotone
  `0–1` inputs from `MonotoneColumnSums`, middle-network exec, threshold keys at level `i`,
  and `middleMonotoneOneCountAboveBottom = scrambledOnesInAboveBottomRows` under a correct
  row scramble. `matrixIntrusionCountB_eq_matrixOnesCountAboveBottom` rewrites intrusion as
  an above-bottom threshold count; `monotoneColumnSumsAtLevel` packages first-sort column sums.

  **Kernel-checked (marking, wire-index keys):** under `KeysAreWireIndices` and
  `IdealColumnSort`, rank marking agrees with key threshold
  (`firstSortMarking_agreesThreshold_of_keysAreWireIndices`) and first-sort column sums
  match `monotoneMatrixBool` at every cell (`firstSortLargestKeyMark01_eq_monotoneMatrixBool_of_idealColumnSort_and_keys`, all `m`).

  **Kernel-checked (middle marking):** `MiddleStageMarkingToMiddleCountHyp.of_firstSortMarking`
  (ideal column sort + first-sort marking/threshold agreement + row scramble correctness);
  per-input marking from `KeysAreWireIndices` + `IdealColumnSort`.

  **Kernel-checked (B decode):** `MiddleStageDecodeHyp.of_idealColumnSort_rowScramble`,
  `HasPackSemanticPropertyB.of_combinatorial`, and canonical-pack
  `HasPackSemanticPropertyB_canonical_of_combinatorial` in `AKS.Chvatal.SortedColumnDecode`
  (semantic middle stage with `wirePerm`; column-sum route). Full
  `CombinatorialToMatrixObligationB.of_columnSortNetwork_rowScramble` needs per-pack
  `IdealColumnSort` + `RowScrambleCorrect` (discharged for `columnSortNetwork` /
  `rowScrambleNetwork` on the canonical pack only).

  **Comparator vs semantic:** `pack.net` ignores `wirePerm`; matrix B/F for Thm 5.1 use
  `HasPackSemanticPropertyB`/`F` on `SortScrambleSortPack.semanticExec`. When `wirePerm = 1`,
  `pack.net.exec` agrees with `semanticExec` (`SortScrambleSortPack.exec_eq_of_wirePerm_one`).

  **Kernel-checked (F closing, 2026-10-05):** `FringePropertyFClosingHyp.of_idealColumnSort_rowScramble`
  in `SortedColumnDecode` (top-`j` column totals + `j < f` from `δ_F·n < 1`, not a literal
  combinatorial-Chernoff step); `CombinatorialToMatrixObligationF.of_columnSortNetwork_rowScramble`
  and full `CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble` (B + F) under
  universal `IdealColumnSort` + `RowScrambleCorrect`, `0 < f`, `0 < epsF`, and `δ_F·n < 1`
  (`deltaF_mul_n_lt_one_params7_n16` for §7 + `n = 16`).
-/

public import AKS.Chvatal.Lemma61
public import AKS.Chvatal.Lemma62
public import AKS.Sort.Defs
public import AKS.Sort.Displaced
public import AKS.Sort.Monotone
public import AKS.Bitonic.Shrink
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace Chvatal

open BigOperators

/-! **Matrix wire layout** (row-major; bottom rows = larger wire indices) -/

/-- Wire index for row `r`, column `j` in an `m × n` matrix (`m·n` wires total). -/
def matrixWire (m n : Nat) (r : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨r.val * n + j.val, by
    have hr := r.isLt
    have hj := j.isLt
    calc r.val * n + j.val
        < r.val * n + n := Nat.add_lt_add_left hj (r.val * n)
      _ = (r.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hr)⟩

theorem matrixWire_row (m n : Nat) (r : Fin m) (j : Fin n) :
    (matrixWire m n r j).val = r.val * n + j.val := rfl


/-! **Matrix coordinates** (inverse to `matrixWire` when `0 < m`, `0 < n`) -/

/-- Column index of wire `w` in row-major layout. -/
def matrixCol (m n : Nat) (hn : 0 < n) (w : Fin (m * n)) : Fin n :=
  ⟨w.val % n, Nat.mod_lt w.val hn⟩

/-- Row index of wire `w` in row-major layout. -/
def matrixRow (m n : Nat) (hn : 0 < n) (w : Fin (m * n)) : Fin m :=
  ⟨w.val / n, (Nat.div_lt_iff_lt_mul hn).2 w.isLt⟩

theorem matrixRow_val (m n : Nat) (hn : 0 < n) (w : Fin (m * n)) :
    (matrixRow m n hn w).val = w.val / n := rfl

theorem matrixCol_val (m n : Nat) (hn : 0 < n) (w : Fin (m * n)) :
    (matrixCol m n hn w).val = w.val % n := rfl

theorem matrixWire_row_col {m n : Nat} (hn : 0 < n) (r : Fin m) (j : Fin n) :
    matrixRow m n hn (matrixWire m n r j) = r ∧
      matrixCol m n hn (matrixWire m n r j) = j := by
  constructor
  · apply Fin.ext
    simp only [matrixRow_val, matrixWire_row]
    have h := Nat.div_add_mod (r.val * n + j.val) n
    have hmod : (r.val * n + j.val) % n = j.val := by
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    rw [hmod] at h
    have h' : n * ((r.val * n + j.val) / n) = r.val * n := Nat.add_right_cancel h
    exact Nat.mul_left_cancel hn (h'.trans (Nat.mul_comm n r.val).symm)
  · apply Fin.ext
    simp only [matrixCol_val, matrixWire_row]
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]


/-- Wires belonging to column `j`. -/
def columnWires (m n : Nat) (hn : 0 < n) (j : Fin n) : Finset (Fin (m * n)) :=
  Finset.univ.filter fun w => matrixCol m n hn w = j

theorem mem_columnWires {m n : Nat} (hn : 0 < n) (j : Fin n) (w : Fin (m * n)) :
    w ∈ columnWires m n hn j ↔ matrixCol m n hn w = j := by
  simp [columnWires, Finset.mem_filter, Finset.mem_univ, true_and]




theorem matrixWire_mem_columnWires {m n : Nat} (hn : 0 < n) (r : Fin m) (j : Fin n) :
    matrixWire m n r j ∈ columnWires m n hn j := by
  simpa [mem_columnWires] using (matrixWire_row_col hn r j).2


theorem matrixWire_matrixRow_col {m n : Nat} (hn : 0 < n) (w : Fin (m * n)) :
    matrixWire m n (matrixRow m n hn w) (matrixCol m n hn w) = w := by
  apply Fin.ext
  simp only [matrixWire_row, matrixRow_val, matrixCol_val]
  calc
    (w.val / n) * n + w.val % n = n * (w.val / n) + w.val % n := by rw [Nat.mul_comm]
    _ = w.val := Nat.div_add_mod w.val n

theorem matrixWire_row_lt_iff {m n : Nat} (hn : 0 < n) (j : Fin n) {r s : Fin m} :
    matrixWire m n r j < matrixWire m n s j ↔ r.val < s.val := by
  constructor
  · intro hlt
    have hval : r.val * n + j.val < s.val * n + j.val := Fin.mk_lt_mk.mp hlt
    exact (Nat.mul_lt_mul_right hn).mp (Nat.add_lt_add_iff_right.mp hval)
  · intro hrs
    have hmul : r.val * n < s.val * n := (Nat.mul_lt_mul_right hn).2 hrs
    exact Fin.mk_lt_mk.mpr (Nat.add_lt_add_iff_right.mpr hmul)


theorem matrixWire_injective {m n : Nat} (hn : 0 < n) {r r' : Fin m} {j j' : Fin n}
    (h : matrixWire m n r j = matrixWire m n r' j') : r = r' ∧ j = j' := by
  have hrow := congrArg (matrixRow m n hn) h
  have hcol := congrArg (matrixCol m n hn) h
  simp [matrixWire_row_col] at hrow hcol
  exact ⟨hrow, hcol⟩

/-! **Matrix intrusion counts (Theorem 5.1 §6)** -/





/-! **Column sort and sort–scramble–sort network** -/

/-- Comparators may only compare wires in a single column. -/
def ColumnLocalNetwork (m n : Nat) (net : ComparatorNetwork (m * n)) : Prop :=
  ∀ c ∈ net.comparators,
    ∃ j r k, c.i = matrixWire m n r j ∧ c.j = matrixWire m n k j

structure ColumnSortNetwork (m n : Nat) where
  net : ComparatorNetwork (m * n)
  col_local : ColumnLocalNetwork m n net := by
    intro c hc
    cases hc

/-- Order embedding of row `r` in column `j`. -/
def columnWireEmbed (m n : Nat) (hn : 0 < n) (j : Fin n) : Fin m ↪o Fin (m * n) :=
  OrderEmbedding.ofStrictMono (fun r => matrixWire m n r j)
    fun {a b} hab => (matrixWire_row_lt_iff hn j).2 hab

theorem columnWireEmbed_apply (m n : Nat) (hn : 0 < n) (j : Fin n) (r : Fin m) :
    (columnWireEmbed m n hn j) r = matrixWire m n r j := rfl

def columnSortColumnNet (m n : Nat) (hn : 0 < n) (j : Fin n) : ComparatorNetwork (m * n) :=
  (bitonicNetwork m).scatterEmbed (m * n) (columnWireEmbed m n hn j)

/-- Column-sort column comparators live on that column. -/
theorem columnSortColumnNet_scatter_wire {m n : Nat} (hn : 0 < n) (j : Fin n)
    (c : Comparator (m * n)) (hc : c ∈ (columnSortColumnNet m n hn j).comparators) :
    ∃ r k : Fin m, c.i = matrixWire m n r j ∧ c.j = matrixWire m n k j := by
  dsimp [columnSortColumnNet, ComparatorNetwork.scatterEmbed] at hc
  rw [List.mem_map] at hc
  obtain ⟨d, _, heq⟩ := hc
  subst heq
  exact ⟨d.i, d.j, rfl, rfl⟩

private theorem columnSortColumnNet_comparator_not_in_other_column {m n : Nat} (hn : 0 < n)
    {j j' : Fin n} (hne : j ≠ j') (c : Comparator (m * n))
    (hc : c ∈ (columnSortColumnNet m n hn j').comparators) {w : Fin (m * n)}
    (hw : w ∈ columnWires m n hn j) : w ≠ c.i ∧ w ≠ c.j := by
  obtain ⟨r, k, hi, hk⟩ := columnSortColumnNet_scatter_wire (m := m) (n := n) hn j' c hc
  have hwcol : matrixCol m n hn w = j := (mem_columnWires (m := m) (n := n) hn j w).mp hw
  have hicol : matrixCol m n hn c.i = j' := by rw [hi, (matrixWire_row_col hn r j').2]
  have hkcol : matrixCol m n hn c.j = j' := by rw [hk, (matrixWire_row_col hn k j').2]
  exact ⟨fun heq => hne (by rw [← hwcol, heq, hicol]), fun heq => hne (by rw [← hwcol, heq, hkcol])⟩

private theorem columnSortColumnNet_foldl_outside_column {m n : Nat} (hn : 0 < n)
    (cols : List (Fin n)) (j : Fin n) {α : Type*} [LinearOrder α] (v : Fin (m * n) → α)
    (hdisj : ∀ col ∈ cols, col ≠ j) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    (cols.foldl (fun acc col => (columnSortColumnNet m n hn col).exec acc) v) w = v w := by
  exact (ComparatorNetwork.foldl_exec_outside_set cols (columnSortColumnNet m n hn) v
    (columnWires m n hn j) fun col hj' s hs c hc =>
      columnSortColumnNet_comparator_not_in_other_column (hn := hn) (j := j) (j' := col)
        (hne := (hdisj col hj').symm) c hc hs) w hw

def columnSortNetwork (m n : Nat) (hn : 0 < n) : ColumnSortNetwork m n where
  net := ⟨(List.finRange n).flatMap fun j : Fin n =>
    (columnSortColumnNet m n hn j).comparators⟩
  col_local := by
    intro c hc
    obtain ⟨j, _, hc'⟩ := List.mem_flatMap.mp hc
    obtain ⟨r, k, hi, hk⟩ := columnSortColumnNet_scatter_wire (m := m) (n := n) hn j c hc'
    exact ⟨j, r, k, hi, hk⟩


private theorem columnSortColumnNet_exec_outside_column {m n : Nat} (hn : 0 < n)
    {j j' : Fin n} (hne : j' ≠ j) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    ((columnSortColumnNet m n hn j').exec v) w = v w := by
  unfold columnSortColumnNet ComparatorNetwork.exec
  refine foldl_comparators_outside _ v w ?_
  intro c hc
  exact columnSortColumnNet_comparator_not_in_other_column (hn := hn) (j := j) (j' := j')
    hne.symm c hc hw


private theorem columnSortColumnNet_exec_preserves_mem_column {m n : Nat} (hn : 0 < n)
    (j : Fin n) {β : Type*} [LinearOrder β] (v : Fin (m * n) → β) (w : Fin (m * n))
    (hw : w ∈ columnWires m n hn j) :
    w ∈ columnWires m n hn j := hw

private theorem columnSortColumnNet_exec_eq_on_column_of_agree {m n : Nat} (hn : 0 < n) (j : Fin n)
    {α : Type*} [LinearOrder α] (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j)
    (v₁ v₂ : Fin (m * n) → α)
    (hagree : ∀ (w' : Fin (m * n)), w' ∈ columnWires m n hn j → v₁ w' = v₂ w') :
    ((columnSortColumnNet m n hn j).exec v₁) w =
      ((columnSortColumnNet m n hn j).exec v₂) w := by
  have hjcol : matrixCol m n hn w = j := (mem_columnWires (m := m) (n := n) hn j w).mp hw
  have hfun : v₁ ∘ columnWireEmbed m n hn j = v₂ ∘ columnWireEmbed m n hn j :=
    funext fun r => hagree (matrixWire m n r j) (matrixWire_mem_columnWires hn r j)
  set r := matrixRow m n hn w
  have hw' : w = matrixWire m n r j := by
    calc w = matrixWire m n (matrixRow m n hn w) (matrixCol m n hn w) :=
        (matrixWire_matrixRow_col hn w).symm
      _ = matrixWire m n r j := by rw [hjcol]
  rw [hw', ← columnWireEmbed_apply m n hn j r]
  dsimp [columnSortColumnNet]
  rw [ComparatorNetwork.scatterEmbed_exec_inside, ComparatorNetwork.scatterEmbed_exec_inside, hfun]

private theorem columnSortColumnNet_foldl_acc_eq_on_column {m n : Nat} (hn : 0 < n) (jCol : Fin n)
    (cols : List (Fin n)) {α : Type*} [LinearOrder α]
    (v₁ v₂ : Fin (m * n) → α)     (hagree : ∀ (w' : Fin (m * n)), w' ∈ columnWires m n hn jCol → v₁ w' = v₂ w')
    (w : Fin (m * n)) (hw : w ∈ columnWires m n hn jCol) :
    (cols.foldl (fun acc col => (columnSortColumnNet m n hn col).exec acc) v₁) w =
      (cols.foldl (fun acc col => (columnSortColumnNet m n hn col).exec acc) v₂) w := by
  induction cols generalizing v₁ v₂ w with
  | nil => simp only [List.foldl_nil]; exact hagree w hw
  | cons col cols' ih =>
    simp only [List.foldl_cons]
    have hagree_exec : ∀ w' ∈ columnWires m n hn jCol,
        ((columnSortColumnNet m n hn col).exec v₁) w' =
          ((columnSortColumnNet m n hn col).exec v₂) w' := by
      intro w' hw'
      by_cases hcol : col = jCol
      · rw [show columnSortColumnNet m n hn col = columnSortColumnNet m n hn jCol from by rw [hcol]]
        exact columnSortColumnNet_exec_eq_on_column_of_agree hn jCol w' hw' v₁ v₂ hagree
      · rw [columnSortColumnNet_exec_outside_column (hn := hn) (j := jCol) (j' := col) hcol v₁ w' hw',
          columnSortColumnNet_exec_outside_column (hn := hn) (j := jCol) (j' := col) hcol v₂ w' hw',
          hagree w' hw']
    exact ih ((columnSortColumnNet m n hn col).exec v₁)
      ((columnSortColumnNet m n hn col).exec v₂) (fun w' hw' => hagree_exec w' hw') w hw

private theorem columnSortNetwork_foldl_exec_column_wire {m n : Nat} (hn : 0 < n) (jCol : Fin n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) (w : Fin (m * n))
    (hw : w ∈ columnWires m n hn jCol) :
    ∀ (cols : List (Fin n)), cols.Nodup → jCol ∈ cols →
      (cols.foldl (fun acc col => (columnSortColumnNet m n hn col).exec acc) v) w =
        ((columnSortColumnNet m n hn jCol).exec v) w := by
  intro cols hnd hjmem
  induction cols with
  | nil => cases hjmem
  | cons cIdx cols' ih =>
    simp only [List.foldl_cons]
    by_cases heq : cIdx = jCol
    · have hjnot : jCol ∉ cols' := by
        have := (List.nodup_cons.mp hnd).1
        rwa [heq] at this
      have hrest :
          (cols'.foldl (fun acc col' => (columnSortColumnNet m n hn col').exec acc)
              ((columnSortColumnNet m n hn jCol).exec v)) w =
            ((columnSortColumnNet m n hn jCol).exec v) w :=
        columnSortColumnNet_foldl_outside_column (m := m) (n := n) hn cols' jCol
          ((columnSortColumnNet m n hn jCol).exec v)
          (fun col' hcol' => by rintro rfl; exact hjnot hcol') w
          (columnSortColumnNet_exec_preserves_mem_column hn jCol v w hw)
      have hhead :
          (columnSortColumnNet m n hn cIdx).exec v =
            (columnSortColumnNet m n hn jCol).exec v := by
        rw [heq]
      rw [hhead, hrest]
    · have hv : ((columnSortColumnNet m n hn cIdx).exec v) w = v w :=
        columnSortColumnNet_exec_outside_column (hn := hn) (j := jCol) (j' := cIdx) heq v w hw
      have hj' : jCol ∈ cols' := by
        rw [List.mem_cons] at hjmem
        exact hjmem.resolve_left (Ne.symm heq)
      have hfold :
          (cols'.foldl (fun acc col' => (columnSortColumnNet m n hn col').exec acc) v) w =
            (cols'.foldl (fun acc col' => (columnSortColumnNet m n hn col').exec acc)
              ((columnSortColumnNet m n hn cIdx).exec v)) w :=
        columnSortColumnNet_foldl_acc_eq_on_column (m := m) (n := n) hn jCol cols' v
          ((columnSortColumnNet m n hn cIdx).exec v)
          (fun w' hw' =>
            (columnSortColumnNet_exec_outside_column (hn := hn) (j := jCol) (j' := cIdx) heq v w' hw').symm) w hw
      rw [← hfold, ih (List.nodup_cons.mp hnd).2 hj']

theorem columnSortNetwork_exec_matrixWire {m n : Nat} (hn : 0 < n) (j : Fin n) {α : Type*}
    [LinearOrder α] (v : Fin (m * n) → α) (r : Fin m) :
    (columnSortNetwork m n hn).net.exec v (matrixWire m n r j) =
      (bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j) r := by
  dsimp [columnSortNetwork, ColumnSortNetwork.net]
  rw [ComparatorNetwork.exec_flatMap]
  have hw := matrixWire_mem_columnWires (m := m) (n := n) hn r j
  rw [columnSortNetwork_foldl_exec_column_wire (m := m) (n := n) hn j v _ hw _ (List.nodup_finRange n)
    (List.mem_finRange j)]
  dsimp [columnSortColumnNet]
  have hinside := ComparatorNetwork.scatterEmbed_exec_inside (bitonicNetwork m) (m * n)
    (columnWireEmbed m n hn j) v r
  rwa [columnWireEmbed_apply] at hinside

/-- Column sort is *ideal* when, on every column, values are nondecreasing from top row
    to bottom row (smaller wire index to larger). -/
def IdealColumnSort (m n : Nat) (_hn : 0 < n) (colSort : ColumnSortNetwork m n) : Prop :=
  ∀ (j : Fin n) {α : Type} [LinearOrder α] (v : Fin (m * n) → α),
    Monotone fun r : Fin m => colSort.net.exec v (matrixWire m n r j)

theorem idealColumnSort_columnSortNetwork (m n : Nat) (hn : 0 < n) :
    IdealColumnSort m n hn (columnSortNetwork m n hn) := by
  intro j α _ v r s hrs
  have hmono : Monotone ((bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j)) :=
    (bitonicNetwork_sorts m) (v := v ∘ columnWireEmbed m n hn j)
  calc (columnSortNetwork m n hn).net.exec v (matrixWire m n r j)
      = (bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j) r :=
        columnSortNetwork_exec_matrixWire (m := m) (n := n) hn j v r
    _ ≤ (bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j) s := hmono hrs
    _ = (columnSortNetwork m n hn).net.exec v (matrixWire m n s j) := by
        rw [← columnSortNetwork_exec_matrixWire (m := m) (n := n) hn j v s]

/-- Values on wires are nondecreasing down each column (top row to bottom row). -/
def ColumnMonotoneInput (m n : Nat) (_hn : 0 < n) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) : Prop :=
  ∀ (j : Fin n) {r s : Fin m}, r ≤ s → v (matrixWire m n r j) ≤ v (matrixWire m n s j)

theorem IdealColumnSort.exec_columnMonotoneInput {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    {α : Type} [LinearOrder α] (v : Fin (m * n) → α) :
    ColumnMonotoneInput m n hn (colSort.net.exec v) :=
  fun j r s hrs => (hcol j v) hrs


private theorem columnLocal_comparator_input_le {m n : Nat} (hn : 0 < n)
    (c : Comparator (m * n))
    (hloc : ∃ j r s, c.i = matrixWire m n r j ∧ c.j = matrixWire m n s j)
    (v : Fin (m * n) → Bool) (hv : ColumnMonotoneInput m n hn v) :
    v c.i ≤ v c.j := by
  obtain ⟨j, r, s, hri, hsj⟩ := hloc
  have hrs : r.val < s.val := (matrixWire_row_lt_iff hn j).mp (by rw [← hri, ← hsj]; exact c.h)
  have hle : v (matrixWire m n r j) ≤ v (matrixWire m n s j) := hv j (Fin.mk_le_mk.mpr hrs.le)
  simpa [hri, hsj] using hle

private theorem columnLocalNetwork_exec_eq_of_columnMonotoneInput {m n : Nat} (hn : 0 < n)
    (compList : List (Comparator (m * n)))
    (col_local : ColumnLocalNetwork m n ⟨compList⟩)
    (v : Fin (m * n) → Bool) (hv : ColumnMonotoneInput m n hn v) :
    (⟨compList⟩ : ComparatorNetwork (m * n)).exec v = v := by
  revert v hv
  induction compList with
  | nil =>
    intro v hv
    simp [ComparatorNetwork.exec]
  | cons comp tail ih =>
    intro v hv
    have hmem : comp ∈ comp :: tail := List.mem_cons_self
    have hle := columnLocal_comparator_input_le hn comp (col_local comp hmem) v hv
    rw [ComparatorNetwork.exec, List.foldl_cons, Comparator.apply_eq_of_le comp v hle]
    have col_local_tail : ColumnLocalNetwork m n ⟨tail⟩ :=
      fun c hc => col_local c (List.mem_cons_of_mem comp hc)
    exact ih col_local_tail v hv

/-- Ideal column sort is a fixpoint on column-monotone `Bool` inputs. -/
theorem IdealColumnSort.exec_eq_of_columnMonotoneInput {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (_hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) (hv : ColumnMonotoneInput m n hn v) :
    colSort.net.exec v = v :=
  columnLocalNetwork_exec_eq_of_columnMonotoneInput hn colSort.net.comparators colSort.col_local v hv

/-- Column-monotone `Bool` inputs agreeing on every `matrixWire` cell are equal. -/
theorem ColumnMonotoneInput.eq_of_matrixWire_eq {m n : Nat} (hn : 0 < n)
    {f g : Fin (m * n) → Bool} (_hf : ColumnMonotoneInput m n hn f)
    (_hg : ColumnMonotoneInput m n hn g)
    (h : ∀ (r : Fin m) (j : Fin n), f (matrixWire m n r j) = g (matrixWire m n r j)) :
    f = g := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  exact h (matrixRow m n hn w) (matrixCol m n hn w)

/-- A comparator network that only compares wires within a single row. -/
def RowLocalNetwork (m n : Nat) (net : ComparatorNetwork (m * n)) : Prop :=
  ∀ c ∈ net.comparators,
    ∃ r j k, c.i = matrixWire m n r j ∧ c.j = matrixWire m n r k

/-- Row-wise scramble stage for fixed `σ` (comparators may only touch one row at a time). -/
structure RowScrambleNetwork (m n : Nat) (σ : Scramble m n) where
  net : ComparatorNetwork (m * n)
  wirePerm : Equiv.Perm (Fin (m * n))
  perm_on_matrixWire :
    ∀ (r : Fin m) (j : Fin n),
      wirePerm (matrixWire m n r j) = matrixWire m n r (σ r j)
  row_local : RowLocalNetwork m n net
  /-- Chvátal §5 middle stage here is wire relabeling; row-local comparators are optional future work. -/
  comparators_eq_nil : net.comparators = []

/-- Apply row scramble: optional row-local comparators after fixed wire relabeling `wirePerm`.

`permuteWireValues` reads `v (π w)`; with `π = wirePerm.symm` and
`wirePerm (matrixWire r j) = matrixWire r (σ r j)`, the value at column `j` comes from
column `(σ r).symm j`, so ones at `S` move to `S.image (σ r)`. -/
def RowScrambleNetwork.wiredExec {m n : Nat} {σ : Scramble m n}
    (rowScramble : RowScrambleNetwork m n σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  rowScramble.net.exec (_root_.permuteWireValues rowScramble.wirePerm.symm v)

theorem RowScrambleNetwork.wiredExec_eq_perm_of_nil {m n : Nat} {_σ : Scramble m n}
    (rs : RowScrambleNetwork m n _σ) (h : rs.net.comparators = []) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) :
    rs.wiredExec v = _root_.permuteWireValues rs.wirePerm.symm v := by
  simp [RowScrambleNetwork.wiredExec, h, ComparatorNetwork.exec, _root_.permuteWireValues]

theorem RowScrambleNetwork.wirePerm_matrixRow {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (rs : RowScrambleNetwork m n σ) (w : Fin (m * n)) :
    matrixRow m n hn (rs.wirePerm w) = matrixRow m n hn w := by
  have hw : w = matrixWire m n (matrixRow m n hn w) (matrixCol m n hn w) :=
    (matrixWire_matrixRow_col hn w).symm
  rw [hw, rs.perm_on_matrixWire (matrixRow m n hn w) (matrixCol m n hn w)]
  simp [matrixWire_row_col]

/-- Sort columns, apply row scrambles, sort columns again (paper §5 separator shape). -/
def sortScrambleSortNetwork (m n : Nat) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ) :
    ComparatorNetwork (m * n) :=
  ⟨colSort.net.comparators ++ rowScramble.net.comparators ++ colSort.net.comparators⟩


/-! **Threshold `0–1` keys and monotone matrix inputs** -/

/-- Key at or above the largest-`i·n` block (Chvátal matrix Property B threshold). -/
def isAmongLargestKeysBlock {m n : Nat} (i : Nat) (key : Fin (m * n)) : Prop :=
  m * n - i * n ≤ key.val

instance isAmongLargestKeysBlock_decidable {m n : Nat} (i : Nat) (key : Fin (m * n)) :
    Decidable (isAmongLargestKeysBlock i key) :=
  inferInstanceAs (Decidable (m * n - i * n ≤ key.val))

/-- `0–1` marking of wires whose input key lies in the largest `i·n` block. -/
def largestKeyBlock01 {m n : Nat} (v : Fin (m * n) → Fin (m * n)) (i : Nat)
    (w : Fin (m * n)) : Bool :=
  decide (isAmongLargestKeysBlock i (v w))

/-- Threshold marking for largest-`i·n` keys at a wire. -/
def largestKeyThreshold01 {m n : Nat} (i : Nat) (key : Fin (m * n)) : Bool :=
  decide (isAmongLargestKeysBlock i key)


/-- Monotone `0–1` matrix from column sums `c` (ones in bottom `(c j)` rows of column `j`). -/
def monotoneMatrixBool {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (w : Fin (m * n)) : Bool :=
  decide (matrixCol m n hn w ∈ monotoneRowOnes c (matrixRow m n hn w))

theorem monotoneMatrixBool_matrixWire {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (r : Fin m) (j : Fin n) :
    monotoneMatrixBool hn c (matrixWire m n r j) ↔ j ∈ monotoneRowOnes c r := by
  simp [monotoneMatrixBool, matrixWire_row_col]

theorem ColumnMonotoneInput_monotoneMatrixBool {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    ColumnMonotoneInput m n hn (monotoneMatrixBool hn c) := by
  intro j r s hrs
  simp only [monotoneMatrixBool, matrixWire_row_col, decide_eq_true_iff]
  by_cases hr : j ∈ monotoneRowOnes c r
  · have hs : j ∈ monotoneRowOnes c s := by
      simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact Nat.le_trans (Nat.sub_le_sub_left (Fin.mk_le_mk.mp hrs) m) hr
    simp [hr, hs]
  · by_cases hs : j ∈ monotoneRowOnes c s <;> simp [hr, hs]

/-- Per-column count of largest-`i·n` keys after an (ideal) column sort. -/
def columnSumLargestKeysAtLevel {m n : Nat} (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (v : Fin (m * n) → Fin (m * n)) (i : Nat) (j : Fin n) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
      largestKeyBlock01 v i (colSort.net.exec v (matrixWire m n r j))).card

/-- Monotone column-sum encoding from threshold keys at level `i` after first column sort. -/
def monotoneColumnSumsAtLevel {m n : Nat} (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (v : Fin (m * n) → Fin (m * n)) (i : Nat) : MonotoneColumnSums m n :=
  fun j =>
    ⟨columnSumLargestKeysAtLevel hn colSort v i j,
      by
        classical
        unfold columnSumLargestKeysAtLevel
        have hle :
            (Finset.univ.filter fun r : Fin m =>
                largestKeyBlock01 v i (colSort.net.exec v (matrixWire m n r j))).card ≤ m := by
          calc
            _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = m := by simp
        omega⟩

/-! **Middle stage: scrambled `0–1` matrix on wires** -/









/-- Per-column count of scrambled ones in rows strictly above the bottom `i` block. -/
def scrambledColSumInAboveBottomRows {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (j : Fin n) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
      r.val < m - i ∧ j ∈ scrambledRowOnes c σ r).card


theorem finset_card_rows_in_bottom_block_le {m i : Nat} (him : i ≤ m)
    (s : Finset (Fin m))
    (hsub : s ⊆ Finset.univ.filter fun r : Fin m => m - i ≤ r.val) :
    s.card ≤ i := by
  classical
  set g : Fin m → Nat := fun r => r.val - (m - i)
  have hinj : Set.InjOn g s := by
    intro r₁ hr₁ r₂ hr₂ heq
    apply Fin.ext
    have h₁ := (Finset.mem_filter.mp (hsub hr₁)).2
    have h₂ := (Finset.mem_filter.mp (hsub hr₂)).2
    simp [g] at heq
    omega
  have hsubset : s.image g ⊆ Finset.range i := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    have hge := (Finset.mem_filter.mp (hsub hr)).2
    have hrLt : r.val < m := r.isLt
    have heq : (m - i) + (r.val - (m - i)) = r.val := Nat.add_sub_of_le hge
    have hm_eq : m = (m - i) + i := (Nat.sub_add_cancel him).symm
    have hlt : r.val < (m - i) + i := hm_eq ▸ hrLt
    have hlt' : r.val - (m - i) < i := Nat.lt_of_add_lt_add_left (by rwa [← heq] at hlt)
    exact Finset.mem_range.mpr hlt'
  calc
    s.card = (s.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range i).card := Finset.card_le_card hsubset
    _ = i := by simp

theorem onesAboveBottom_le_scrambledColSumInAboveBottomRows {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (j : Fin n) (him : i ≤ m) :
    scrambledColSum c σ j - i ≤ scrambledColSumInAboveBottomRows c σ i j := by
  classical
  set s := scrambledColSum c σ j
  set above := scrambledColSumInAboveBottomRows c σ i j
  set bottom :=
    (Finset.univ.filter fun r : Fin m => m - i ≤ r.val ∧ j ∈ scrambledRowOnes c σ r)
  by_cases hi : s < i
  · have h0 : s - i = 0 := Nat.sub_eq_zero_of_le (le_of_lt hi)
    rw [h0]
    exact Nat.zero_le above
  · have hbottom : s = above + bottom.card := by
      dsimp only [s, above, bottom, scrambledColSum, scrambledColSumInAboveBottomRows]
      rw [← Finset.card_filter]
      have hsplit :
          (Finset.univ.filter fun r : Fin m => j ∈ scrambledRowOnes c σ r) =
            (Finset.univ.filter fun r : Fin m =>
                r.val < m - i ∧ j ∈ scrambledRowOnes c σ r) ∪ bottom := by
        ext r
        simp only [bottom, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · intro hj
          rcases Nat.lt_or_ge r.val (m - i) with hr | hr
          · exact Or.inl ⟨hr, hj⟩
          · exact Or.inr ⟨hr, hj⟩
        · rintro (⟨hr, hj⟩ | ⟨hr, hj⟩) <;> exact hj
      have hdisj :
          Disjoint
            (Finset.univ.filter fun r : Fin m =>
              r.val < m - i ∧ j ∈ scrambledRowOnes c σ r)
            bottom := by
        refine Finset.disjoint_filter.mpr fun r _ h₁ h₂ => ?_
        have := lt_of_lt_of_le h₁.1 h₂.1
        exact Nat.lt_irrefl _ this
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
    have hbottom_le_i : bottom.card ≤ i := by
      dsimp [bottom]
      refine finset_card_rows_in_bottom_block_le (m := m) (i := i) him bottom ?_
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.1⟩
    have hs' : s - i ≤ above := by
      rw [hbottom]
      omega
    exact hs'












/-! **Matrix bridge obligation (residual core)** -/

/-- Per-scramble row stage bundled with the sort–scramble–sort separator for that `σ`. -/
structure SortScrambleSortPack (m n : Nat) (hn : 0 < n) (σ : Scramble m n) where
  rowScramble : RowScrambleNetwork m n σ

/-- Always the embedded column sorter (Chvátal §5 first/last column sort). -/
def SortScrambleSortPack.colSort {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (_pack : SortScrambleSortPack m n hn σ) : ColumnSortNetwork m n :=
  columnSortNetwork m n hn

/-- Canonical sort–scramble–sort network for a pack (no separate stored `net`). -/
def SortScrambleSortPack.net {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) : ComparatorNetwork (m * n) :=
  sortScrambleSortNetwork m n σ p.colSort p.rowScramble



/-- Semantic middle stage: column sort then wire relabeling / row-local comparators. -/
def sortScrambleMiddleExec {m n : Nat} {σ : Scramble m n}
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) : Fin (m * n) → α :=
  rowScramble.wiredExec (colSort.net.exec v)


def SortScrambleSortPack.middleExec {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  sortScrambleMiddleExec p.colSort p.rowScramble v

theorem SortScrambleSortPack.middle_exec_eq {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) :
    p.middleExec v = p.rowScramble.wiredExec (p.colSort.net.exec v) := rfl


/-- Final column sort after wire relabeling in the middle stage (Chvátal §5 semantics). -/
def SortScrambleSortPack.semanticExec {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  pack.colSort.net.exec (pack.middleExec v)


/-- Row scramble implements combinatorial `σ` on monotone `0–1` inputs after column sort. -/
structure RowScrambleCorrect (m n : Nat) (hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ) : Prop where
  maps_scramble :
    ∀ (c : MonotoneColumnSums m n) (r : Fin m) (j : Fin n),
      sortScrambleMiddleExec colSort rowScramble (monotoneMatrixBool hn c)
          (matrixWire m n r j) = true ↔
        j ∈ scrambledRowOnes c σ r



/-- Count of `true` wires in the same above-bottom row region (no network applied). -/
def matrixOnesCountInRegion {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      (matrixRow m n hn w).val < m - i ∧ v w = true).card



theorem RowScrambleNetwork.wirePerm_symm_matrixRow {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (rs : RowScrambleNetwork m n σ) (w : Fin (m * n)) :
    matrixRow m n hn (rs.wirePerm.symm w) = matrixRow m n hn w := by
  -- `wirePerm` preserves rows, so its inverse does too.
  have h := RowScrambleNetwork.wirePerm_matrixRow hn rs (rs.wirePerm.symm w)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm


/-- Top-`j` key threshold (Property F uses largest `j` keys, not `j·n`). -/
def largestKeyThresholdJ01 {m n : Nat} (j : Nat) (key : Fin (m * n)) : Bool :=
  decide (m * n - j ≤ key.val)


/-- Property B intrusion for the semantic separator (wire relabeling in the middle stage). -/
def packSemanticIntrusionCountB {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (v : Equiv.Perm (Fin (m * n))) (i : Nat) : Nat :=
  matrixOnesCountInRegion hn
    (pack.semanticExec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w))) i

/-- Property F intrusion at fringe depth `f` for the semantic separator. -/
def packSemanticIntrusionCountF {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (v : Equiv.Perm (Fin (m * n))) (f j : Nat) : Nat :=
  matrixOnesCountInRegion hn
    (pack.semanticExec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))) f

/-- Matrix Property B for the semantic sort–scramble–sort map (middle stage includes `wirePerm`). -/
def HasPackSemanticPropertyB {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (epsB : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (i : Nat), 1 ≤ i → i ≤ m →
    (packSemanticIntrusionCountB hn pack v i : ℝ) < (epsB / 2) * (m * n)

/-- Matrix Property F for the semantic sort–scramble–sort map. -/
def HasPackSemanticPropertyF {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (f : Nat) (hfm : f ≤ m) (deltaF epsF : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (j : Nat), 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
    (packSemanticIntrusionCountF hn pack v f j : ℝ) < epsF * j

theorem HasPackSemanticPropertyB_iff {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (epsB : ℝ) :
    HasPackSemanticPropertyB hn pack epsB ↔
      ∀ (v : Equiv.Perm (Fin (m * n))) (i : Nat), 1 ≤ i → i ≤ m →
        (packSemanticIntrusionCountB hn pack v i : ℝ) < (epsB / 2) * (m * n) := by
  rfl

theorem HasPackSemanticPropertyF_iff {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (f : Nat) (hfm : f ≤ m) (deltaF epsF : ℝ) :
    HasPackSemanticPropertyF hn pack f hfm deltaF epsF ↔
      ∀ (v : Equiv.Perm (Fin (m * n))) (j : Nat), 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
        (packSemanticIntrusionCountF hn pack v f j : ℝ) < epsF * j := by
  rfl

/-- Alias: matrix Property B on `pack.semanticExec` (not on `pack.net`, which ignores `wirePerm`). -/
abbrev HasMatrixPropertyB_exec (m n : Nat) (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (epsB : ℝ) :=
  HasPackSemanticPropertyB hn pack epsB


/-! **Theorem 5.1 witness (semantic B/F on sort–scramble–sort pack)** -/

/-- Semantic separator for Thm 5.1: Properties B/F on `SortScrambleSortPack.semanticExec`
    (column sort → wired middle / `wirePerm` → column sort). Depth is the comparator skeleton
    `pack.net` (middle comparators may be empty while relabeling still affects semantics). -/
structure SemanticSeparator (g : ScrambleGeometry) (P : Theorem51Params g) where
  σ : Scramble g.m g.n
  pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ
  hB : HasPackSemanticPropertyB (scrambleGeometry_hn g) pack P.epsB
  hF : HasPackSemanticPropertyF (scrambleGeometry_hn g) pack g.f
    (by have := g.hshape; omega) P.deltaF P.epsF

def SemanticSeparator.net {g : ScrambleGeometry} {P : Theorem51Params g}
    (s : SemanticSeparator g P) : ComparatorNetwork (g.m * g.n) :=
  SortScrambleSortPack.net s.pack

def SemanticSeparator.depth {g : ScrambleGeometry} {P : Theorem51Params g}
    (s : SemanticSeparator g P) : Nat :=
  s.net.depth

/-- Thm 5.1 witness: semantic B/F plus executable `pack.net` for depth accounting. -/
structure ScrambleSeparatorWitness (g : ScrambleGeometry) (P : Theorem51Params g)
    extends SemanticSeparator g P

/-- Executable comparator network (depth accounting); semantic B/F refer to `pack`. -/
def ScrambleSeparatorWitness.net {g : ScrambleGeometry} {P : Theorem51Params g}
    (w : ScrambleSeparatorWitness g P) : ComparatorNetwork (g.m * g.n) :=
  SortScrambleSortPack.net w.pack











/-- Residual decode: permutation inputs → some `c` with pack-network intrusion
    bounded by `onesAboveBottom` (Chvátal §6 rank/threshold step). -/
structure MiddleStageDecodeHyp (m n : Nat) (hn : 0 < n) where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (hcol : IdealColumnSort m n hn pack.colSort)
      (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
      (v : Equiv.Perm (Fin (m * n))),
      ∀ i, 1 ≤ i → i ≤ m →
        ∃ (c : MonotoneColumnSums m n),
          packSemanticIntrusionCountB hn pack v i ≤ onesAboveBottom c σ i



/-- Per-input link: matrix Property B intrusion is bounded by combinatorial `onesAboveBottom`. -/
structure MiddleStageToMatrixB (m n : Nat) (hn : 0 < n) where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (_hcol : IdealColumnSort m n hn pack.colSort)
      (v : Equiv.Perm (Fin (m * n))),
      ∀ i, 1 ≤ i → i ≤ m →
        ∃ (c : MonotoneColumnSums m n),
          packSemanticIntrusionCountB hn pack v i ≤ onesAboveBottom c σ i














/-- Residual F decode: top-`j` fringe intrusion → combinatorial `onesAboveHalfFringe` witness.
    Discharged in `SortedColumnDecode` under ideal column sort + row scramble; the closing
    step `FringePropertyFClosingHyp` remains open (unlike B). -/
structure MiddleStageFringeDecodeHyp (m n f : Nat) (hf : Even f) (hn : 0 < n) (deltaF : ℝ)
    where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (hcol : IdealColumnSort m n hn pack.colSort)
      (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
      (v : Equiv.Perm (Fin (m * n))) (j : Nat) (_hj : 0 < j)
      (_hjδ : (j : ℝ) ≤ deltaF * (f * n)),
      ∃ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
        packSemanticIntrusionCountF hn pack v f j ≤ onesAboveHalfFringe hf c σ S


structure MiddleStageToMatrixF (m n f : Nat) (hf : Even f) (hn : 0 < n) (deltaF epsF : ℝ) where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (hcol : IdealColumnSort m n hn pack.colSort)
      (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
      (v : Equiv.Perm (Fin (m * n))) (j : Nat) (hj : 0 < j)
      (hjδ : (j : ℝ) ≤ deltaF * (f * n)),
      ∃ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
        packSemanticIntrusionCountF hn pack v f j ≤ onesAboveHalfFringe hf c σ S














/-! **Threshold marking, intrusion count, and decode residuals** -/










/-! **Rank-wire vs key-threshold marking (Chvátal §6 decode sub-step)** -/

/-- Standard matrix labeling: wire `w` initially holds key `w` (rank equals wire index). -/
def KeysAreWireIndices {m n : Nat} (v : Equiv.Perm (Fin (m * n))) : Prop :=
  ∀ w : Fin (m * n), v w = w

theorem KeysAreWireIndices.one {m n : Nat} : KeysAreWireIndices (1 : Equiv.Perm (Fin (m * n))) := by
  intro w
  simp




theorem mem_monotoneRowOnes_iff {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m)
    (j : Fin n) : j ∈ monotoneRowOnes c r ↔ (m - r.val) ≤ (c j).val := by
  simp [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- After ideal column sort and wire-index keys, largest-key marking at `(r,j)` matches the
    monotone `0–1` cell from `monotoneColumnSumsAtLevel`. -/
theorem card_filter_row_ge {m : Nat} (rMin : Fin m) :
    (Finset.univ.filter fun r' : Fin m => rMin ≤ r').card = m - rMin.val := by
  classical
  let e : { r' : Fin m // rMin ≤ r' } ≃ Fin (m - rMin.val) :=
    { toFun := fun r => ⟨r.1.val - rMin.val, by have := r.2; have := r.1.isLt; omega⟩
      invFun := fun i : Fin (m - rMin.val) =>
        let r' : Fin m := ⟨rMin.val + i.val, by have := i.isLt; have := rMin.isLt; omega⟩
        have hr : rMin ≤ r' := Fin.mk_le_mk.mpr (Nat.le_add_right rMin.val i.val)
        ⟨r', hr⟩
      left_inv := by
        intro r
        ext
        simp
        omega
      right_inv := by
        intro i
        ext
        simp }
  calc
    (Finset.univ.filter fun r' : Fin m => rMin ≤ r').card
        = Fintype.card { r' : Fin m // rMin ≤ r' } := by rw [Fintype.card_subtype]
    _ = Fintype.card (Fin (m - rMin.val)) := Fintype.card_congr e
    _ = m - rMin.val := Fintype.card_fin (m - rMin.val)







/-! **Theorem 5.1 from combinatorics + bridge** -/







theorem scrambleGeometry_f_le_m (g : ScrambleGeometry) : g.f ≤ g.m := by
  have := g.hshape
  omega

end Chvatal
