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

theorem mem_aboveBottomRows_iff {m n i : Nat} (hi : i ≤ m) (w : Fin (m * n)) :
    w ∈ aboveBottomRows m n i hi ↔ w.val < (m - i) * n := by
  simp [aboveBottomRows, Finset.mem_filter, Finset.mem_univ, true_and]

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

theorem mem_aboveBottomRows_iff_row {m n i : Nat} (hi : i ≤ m) (hn : 0 < n)
    (w : Fin (m * n)) :
    w ∈ aboveBottomRows m n i hi ↔ (matrixRow m n hn w).val < m - i := by
  rw [mem_aboveBottomRows_iff, matrixRow_val, Nat.div_lt_iff_lt_mul hn]

/-- Wires belonging to column `j`. -/
def columnWires (m n : Nat) (hn : 0 < n) (j : Fin n) : Finset (Fin (m * n)) :=
  Finset.univ.filter fun w => matrixCol m n hn w = j

theorem mem_columnWires {m n : Nat} (hn : 0 < n) (j : Fin n) (w : Fin (m * n)) :
    w ∈ columnWires m n hn j ↔ matrixCol m n hn w = j := by
  simp [columnWires, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Wires belonging to row `r`. -/
def rowWires (m n : Nat) (hn : 0 < n) (r : Fin m) : Finset (Fin (m * n)) :=
  Finset.univ.filter fun w => matrixRow m n hn w = r

theorem mem_rowWires {m n : Nat} (hn : 0 < n) (r : Fin m) (w : Fin (m * n)) :
    w ∈ rowWires m n hn r ↔ matrixRow m n hn w = r := by
  simp [rowWires, Finset.mem_filter, Finset.mem_univ, true_and]

theorem matrixWire_mem_rowWires {m n : Nat} (hn : 0 < n) (r : Fin m) (j : Fin n) :
    matrixWire m n r j ∈ rowWires m n hn r := by
  simpa [mem_rowWires] using (matrixWire_row_col hn r j).1

theorem matrixWire_mem_columnWires {m n : Nat} (hn : 0 < n) (r : Fin m) (j : Fin n) :
    matrixWire m n r j ∈ columnWires m n hn j := by
  simpa [mem_columnWires] using (matrixWire_row_col hn r j).2

theorem columnWires_disjoint {m n : Nat} (hn : 0 < n) {j j' : Fin n} (hne : j ≠ j') :
    Disjoint (columnWires m n hn j) (columnWires m n hn j') := by
  classical
  refine Finset.disjoint_filter.mpr fun w _ h₁ h₂ => hne (h₁.symm.trans h₂)

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

theorem matrixWire_le_of_le_row {m n : Nat} (hn : 0 < n) {r s : Fin m} (hrs : r ≤ s)
    (j : Fin n) : matrixWire m n r j ≤ matrixWire m n s j := by
  have hval : (matrixWire m n r j).val ≤ (matrixWire m n s j).val := by
    simp only [matrixWire_row]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right n (Fin.mk_le_mk.mp hrs)) j.val
  exact Fin.mk_le_mk.mpr hval

theorem matrixWire_injective {m n : Nat} (hn : 0 < n) {r r' : Fin m} {j j' : Fin n}
    (h : matrixWire m n r j = matrixWire m n r' j') : r = r' ∧ j = j' := by
  have hrow := congrArg (matrixRow m n hn) h
  have hcol := congrArg (matrixCol m n hn) h
  simp [matrixWire_row_col] at hrow hcol
  exact ⟨hrow, hcol⟩

/-! **Matrix intrusion counts (Theorem 5.1 §6)** -/

/-- Count of largest `i·n` keys landing above the bottom `i` rows after `net` (Property B). -/
def matrixIntrusionCountB {m n : Nat} (net : ComparatorNetwork (m * n))
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) : Nat :=
  (Finset.univ.filter fun pos : Fin (m * n) =>
      pos.val < (m - i) * n ∧
        m * n - i * n ≤ (net.exec (v : Fin (m * n) → Fin (m * n)) pos).val).card

/-- Count for Property F at fringe depth `f` and top-`j` key block. -/
def matrixIntrusionCountF {m n : Nat} (net : ComparatorNetwork (m * n))
    (v : Equiv.Perm (Fin (m * n))) (f j : Nat) : Nat :=
  (Finset.univ.filter fun pos : Fin (m * n) =>
      pos.val < (m - f) * n ∧
        m * n - j ≤ (net.exec (v : Fin (m * n) → Fin (m * n)) pos).val).card

theorem HasMatrixPropertyB_iff {m n : Nat} (net : ComparatorNetwork (m * n)) (epsB : ℝ) :
    HasMatrixPropertyB net epsB ↔
      ∀ (v : Equiv.Perm (Fin (m * n))) (i : Nat), 1 ≤ i → i ≤ m →
        (matrixIntrusionCountB net v i : ℝ) < (epsB / 2) * (m * n) := by
  unfold HasMatrixPropertyB matrixIntrusionCountB
  simp

theorem HasMatrixPropertyF_iff {m n : Nat} (net : ComparatorNetwork (m * n))
    (f : Nat) (hfm : f ≤ m) (deltaF epsF : ℝ) :
    HasMatrixPropertyF net f hfm deltaF epsF ↔
      ∀ (v : Equiv.Perm (Fin (m * n))) (j : Nat), 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
        (matrixIntrusionCountF net v f j : ℝ) < epsF * j := by
  unfold HasMatrixPropertyF matrixIntrusionCountF
  simp

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

private theorem columnSortColumnNet_exec_preserves_col {m n : Nat} (hn : 0 < n)
    (j : Fin n) {β : Type*} [LinearOrder β] (v : Fin (m * n) → β) (w : Fin (m * n))
    (hw : w ∈ columnWires m n hn j) :
    matrixCol m n hn w = j :=
  (mem_columnWires (m := m) (n := n) hn j w).mp hw

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

theorem ColumnMonotoneInput_columnSortNetwork {m n : Nat} (hn : 0 < n) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) (_hv : ColumnMonotoneInput m n hn v) :
    ColumnMonotoneInput m n hn ((columnSortNetwork m n hn).net.exec v) :=
  IdealColumnSort.exec_columnMonotoneInput hn (columnSortNetwork m n hn)
    (idealColumnSort_columnSortNetwork m n hn) v

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

theorem rowWires_disjoint {m n : Nat} (hn : 0 < n) {r r' : Fin m} (hne : r ≠ r') :
    Disjoint (rowWires m n hn r) (rowWires m n hn r') := by
  classical
  refine Finset.disjoint_filter.mpr fun w _ h₁ h₂ => hne (h₁.symm.trans h₂)

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

theorem largestKeyThreshold01_monotone {m n : Nat} (i : Nat) :
    Monotone (largestKeyThreshold01 (m := m) (n := n) i) := by
  intro a b hab
  unfold largestKeyThreshold01 isAmongLargestKeysBlock
  by_cases ha : m * n - i * n ≤ a.val
  · have hb : m * n - i * n ≤ b.val := le_trans ha (Fin.mk_le_mk.mp hab)
    simp [ha, hb]
  · by_cases hb : m * n - i * n ≤ b.val
    · simp [ha, hb]
    · simp [ha, hb]

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

/-- `1`-cell after row scramble on wire `(r,j)` (before the second column sort). -/
def scrambledMatrix01 {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (w : Fin (m * n)) : Prop :=
  matrixCol m n hn w ∈ scrambledRowOnes c σ (matrixRow m n hn w)

theorem matrixWire_scrambledMatrix01 {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (r : Fin m) (j : Fin n) :
    scrambledMatrix01 hn c σ (matrixWire m n r j) ↔ j ∈ scrambledRowOnes c σ r := by
  simp [scrambledMatrix01, matrixWire_row_col]

/-- Number of `1`s in wires strictly above the bottom `i` row block after scramble. -/
def scrambledOnesInAboveBottomRows {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      (matrixRow m n hn w).val < m - i ∧
        matrixCol m n hn w ∈ scrambledRowOnes c σ (matrixRow m n hn w)).card

/-- Row-wise count of ones above the bottom `i` block (middle stage, before second column sort). -/
def scrambledOnesInAboveBottomRowsSum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) : Nat :=
  ∑ r : Fin m, if r.val < m - i then (scrambledRowOnes c σ r).card else 0

/-- Row–column pairs that index a scrambled `1` strictly above the bottom `i` block. -/
def scrambledRowColPairsInAboveBottomRows {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p =>
    p.1.val < m - i ∧ p.2 ∈ scrambledRowOnes c σ p.1

theorem scrambledRowColPairsInAboveBottomRows_card_eq_sum {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    (scrambledRowColPairsInAboveBottomRows c σ i).card =
      scrambledOnesInAboveBottomRowsSum c σ i := by
  classical
  unfold scrambledRowColPairsInAboveBottomRows scrambledOnesInAboveBottomRowsSum
  set rowsAbove : Finset (Fin m) := Finset.univ.filter fun r => r.val < m - i
  have hpairEq :
      (Finset.univ.filter fun p : Fin m × Fin n =>
          p.1.val < m - i ∧ p.2 ∈ scrambledRowOnes c σ p.1) =
        rowsAbove.biUnion fun r =>
          (scrambledRowOnes c σ r).image fun j => (r, j) := by
    ext p
    simp only [rowsAbove, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · intro ⟨hr, hj⟩
      refine ⟨p.1, hr, p.2, hj, ?_⟩
      rfl
    · rintro ⟨r, hr, j, hj, heq⟩
      subst heq
      exact ⟨hr, hj⟩
  have hinj (r : Fin m) :
      Set.InjOn (fun j : Fin n => (r, j)) (scrambledRowOnes c σ r : Set (Fin n)) := by
    intro j₁ _ j₂ _ h
    exact Prod.ext_iff.mp h |>.2
  have hdisj :
      Set.PairwiseDisjoint (rowsAbove : Set (Fin m)) fun r =>
        (scrambledRowOnes c σ r).image fun j => (r, j) := by
    intro r₁ hr₁ r₂ hr₂ hne
    refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
    obtain ⟨j₁, _, h₁⟩ := Finset.mem_image.mp hp₁
    obtain ⟨j₂, _, h₂⟩ := Finset.mem_image.mp hp₂
    exact Prod.ext_iff.mp h₁ |>.1.trans (Prod.ext_iff.mp h₂ |>.1.symm)
  rw [hpairEq, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl fun r _ => Finset.card_image_of_injOn (hinj r), ← Finset.sum_filter]

theorem scrambledOnesInAboveBottomRows_eq_rowColPairs_card {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    scrambledOnesInAboveBottomRows hn c σ i =
      (scrambledRowColPairsInAboveBottomRows c σ i).card := by
  classical
  unfold scrambledOnesInAboveBottomRows scrambledRowColPairsInAboveBottomRows
  symm
  apply Finset.card_bij (fun p _ => matrixWire m n p.1 p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hr, hj⟩ := hp
    constructor
    · simp only [matrixWire_row_col hn]
      exact hr
    · simpa [scrambledMatrix01, matrixWire_row_col hn] using hj
  · intro p _ q _ h
    exact Prod.ext (matrixWire_injective hn h).1 (matrixWire_injective hn h).2
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hr, hj⟩ := hw
    refine ⟨(matrixRow m n hn w, matrixCol m n hn w), ?_, ?_⟩
    · exact ⟨hr, hj⟩
    · exact matrixWire_matrixRow_col hn w

theorem scrambledOnesInAboveBottomRows_eq_scrambledOnesInAboveBottomRowsSum {m n : Nat}
    (hn : 0 < n) (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    scrambledOnesInAboveBottomRows hn c σ i = scrambledOnesInAboveBottomRowsSum c σ i := by
  rw [scrambledOnesInAboveBottomRows_eq_rowColPairs_card,
    scrambledRowColPairsInAboveBottomRows_card_eq_sum]

/-- Per-column count of scrambled ones in rows strictly above the bottom `i` block. -/
def scrambledColSumInAboveBottomRows {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (j : Fin n) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
      r.val < m - i ∧ j ∈ scrambledRowOnes c σ r).card

theorem scrambledColSumInAboveBottomRows_le_scrambledColSum {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (j : Fin n) :
    scrambledColSumInAboveBottomRows c σ i j ≤ scrambledColSum c σ j := by
  classical
  unfold scrambledColSumInAboveBottomRows scrambledColSum
  have hsub :
      (Finset.univ.filter fun r : Fin m =>
          r.val < m - i ∧ j ∈ scrambledRowOnes c σ r) ⊆
        Finset.univ.filter fun r : Fin m => j ∈ scrambledRowOnes c σ r := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
  rw [← Finset.card_filter]
  exact Finset.card_le_card hsub

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

theorem onesAboveBottom_le_sum_scrambledColSumInAboveBottomRows {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (him : i ≤ m) :
    onesAboveBottom c σ i ≤
      ∑ j : Fin n, scrambledColSumInAboveBottomRows c σ i j := by
  classical
  unfold onesAboveBottom
  refine Finset.sum_le_sum fun j _ => ?_
  exact onesAboveBottom_le_scrambledColSumInAboveBottomRows c σ i j him

theorem scrambledRowOnes_card_eq_sum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (r : Fin m) :
    (scrambledRowOnes c σ r).card =
      ∑ j : Fin n, if j ∈ scrambledRowOnes c σ r then (1 : Nat) else 0 := by
  classical
  rw [← Finset.card_filter]
  congr 1
  ext j
  simp

theorem scrambledOnesInAboveBottomRowsSum_eq_sum_scrambledColSumInAboveBottomRows
    {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    scrambledOnesInAboveBottomRowsSum c σ i =
      ∑ j : Fin n, scrambledColSumInAboveBottomRows c σ i j := by
  classical
  unfold scrambledOnesInAboveBottomRowsSum scrambledColSumInAboveBottomRows
  have hrow (r : Fin m) :
      (if r.val < m - i then (scrambledRowOnes c σ r).card else (0 : Nat)) =
        ∑ j : Fin n,
          if r.val < m - i ∧ j ∈ scrambledRowOnes c σ r then (1 : Nat) else 0 := by
    by_cases hr : r.val < m - i
    · simp only [hr, if_true]
      rw [scrambledRowOnes_card_eq_sum c σ r]
      refine Finset.sum_congr rfl fun j _ => by
        by_cases hj : j ∈ scrambledRowOnes c σ r <;> simp [hj]
    · simp only [hr, if_false]
      rw [Finset.sum_eq_zero]
      intro j _
      simp [hr]
  calc
    (∑ r : Fin m,
        if r.val < m - i then (scrambledRowOnes c σ r).card else (0 : Nat)) =
        ∑ r : Fin m,
          ∑ j : Fin n,
            if r.val < m - i ∧ j ∈ scrambledRowOnes c σ r then (1 : Nat) else 0 := by
      refine Finset.sum_congr rfl fun r _ => hrow r
    _ = ∑ j : Fin n, scrambledColSumInAboveBottomRows c σ i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.card_filter]
      rfl

theorem onesAboveBottom_le_scrambledOnesInAboveBottomRowsSum {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (him : i ≤ m) :
    onesAboveBottom c σ i ≤ scrambledOnesInAboveBottomRowsSum c σ i := by
  rw [scrambledOnesInAboveBottomRowsSum_eq_sum_scrambledColSumInAboveBottomRows]
  exact onesAboveBottom_le_sum_scrambledColSumInAboveBottomRows c σ i him

theorem onesAboveBottom_le_scrambledOnesInAboveBottomRows {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (him : i ≤ m) :
    onesAboveBottom c σ i ≤ scrambledOnesInAboveBottomRows hn c σ i := by
  rw [scrambledOnesInAboveBottomRows_eq_scrambledOnesInAboveBottomRowsSum]
  exact onesAboveBottom_le_scrambledOnesInAboveBottomRowsSum c σ i him

def ExistsCombinatorialScrambleBF (m n f : Nat) (hf : Even f) (epsB deltaF epsF : ℝ) :
    Prop :=
  ∃ σ : Scramble m n,
    HasCombinatorialPropertyB σ epsB ∧
      HasCombinatorialPropertyF hf σ deltaF epsF

/-- B on the pipeline matrix class (`totalColumnOnes c ≤ n·i`); sufficient for decode → matrix B. -/
def ExistsCombinatorialScrambleBF_onPipeline (m n f : Nat) (hf : Even f)
    (epsB deltaF epsF : ℝ) : Prop :=
  ∃ σ : Scramble m n,
    HasCombinatorialPropertyBOnPipeline σ epsB ∧
      HasCombinatorialPropertyF hf σ deltaF epsF

theorem not_hasCombinatorialScrambleBF_onPipeline_iff {m n f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ} :
    ¬ ExistsCombinatorialScrambleBF_onPipeline m n f hf epsB deltaF epsF ↔
      ∀ σ : Scramble m n,
        ¬ HasCombinatorialPropertyBOnPipeline σ epsB ∨
          ¬ HasCombinatorialPropertyF hf σ deltaF epsF := by
  classical
  constructor
  · intro hnone σ
    by_contra hall
    push_neg at hall
    exact hnone ⟨σ, hall.1, hall.2⟩
  · intro hall h
    rcases h with ⟨σ, hB, hF⟩
    rcases hall σ with hB' | hF'
    · exact hB' hB
    · exact hF' hF

theorem not_hasCombinatorialScrambleBF_iff {m n f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ} :
    ¬ ExistsCombinatorialScrambleBF m n f hf epsB deltaF epsF ↔
      ∀ σ : Scramble m n,
        ¬ HasCombinatorialPropertyB σ epsB ∨
          ¬ HasCombinatorialPropertyF hf σ deltaF epsF := by
  classical
  constructor
  · intro hnone σ
    by_contra hall
    push_neg at hall
    exact hnone ⟨σ, hall.1, hall.2⟩
  · intro hall h
    rcases h with ⟨σ, hB, hF⟩
    rcases hall σ with hB' | hF'
    · exact hB' hB
    · exact hF' hF

/-- Fail-fraction union: if B-fail and F-fail fractions sum to `< 1`, some scramble has both. -/
theorem exists_combinatorialScrambleBF_of_failFractions
    (m n f : Nat) (hf : Even f) (epsB deltaF epsF x : ℝ)
    (hB : Lemma61FailBound m n epsB)
    (hF : Lemma62FailBound m n f hf deltaF epsF x)
    (hNpos : 0 < Fintype.card (Scramble m n))
    (hαβ : lemma61_failFactor m n + lemma62_failFactor x < 1) :
    ExistsCombinatorialScrambleBF m n f hf epsB deltaF epsF := by
  classical
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNpos
  by_contra hnone
  have hall := (not_hasCombinatorialScrambleBF_iff (m := m) (n := n) (f := f)).1 hnone
  set badB : Finset (Scramble m n) :=
    Finset.univ.filter fun σ => ¬ HasCombinatorialPropertyB σ epsB
  set badF : Finset (Scramble m n) :=
    Finset.univ.filter fun σ => ¬ HasCombinatorialPropertyF hf σ deltaF epsF
  have hsub : (Finset.univ : Finset (Scramble m n)) ⊆ badB ∪ badF := by
    intro σ _
    rcases hall σ with hB | hF
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩)
  have hunion :
      (Fintype.card (Scramble m n) : ℝ) ≤ (badB ∪ badF).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard :
      (badB ∪ badF).card ≤ badB.card + badF.card :=
    Finset.card_union_le badB badF
  have hB' := hB.bound badB (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  have hF' := hF.bound badF (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  set α := lemma61_failFactor m n
  set β := lemma62_failFactor x
  have hle : (1 : ℝ) ≤ α + β := by
    have h1 : (1 : ℝ) * N ≤ (badB.card + badF.card : ℝ) := by
      calc (1 : ℝ) * N
          = N := by ring
        _ ≤ (badB ∪ badF).card := hunion
        _ ≤ badB.card + badF.card := by exact_mod_cast hcard
    have h2 : (badB.card : ℝ) ≤ α * N := by simpa [α] using hB'
    have h3 : (badF.card : ℝ) ≤ β * N := by simpa [β] using hF'
    have h4 : (badB.card + badF.card : ℝ) ≤ (α + β) * N := by
      calc (badB.card + badF.card : ℝ)
          = (badB.card : ℝ) + badF.card := by ring
        _ ≤ α * N + β * N := by gcongr
        _ = (α + β) * N := by ring
    have h5 : (1 : ℝ) * N ≤ (α + β) * N := h1.trans h4
    exact le_of_mul_le_mul_right h5 hN
  linarith [hαβ, hle]

theorem exists_combinatorialScrambleBF_onPipeline_of_failFractions
    (m n f : Nat) (hf : Even f) (epsB deltaF epsF x : ℝ)
    (hB : Lemma61FailBoundOnPipeline m n epsB)
    (hF : Lemma62FailBound m n f hf deltaF epsF x)
    (hNpos : 0 < Fintype.card (Scramble m n))
    (hαβ : lemma61_failFactor m n + lemma62_failFactor x < 1) :
    ExistsCombinatorialScrambleBF_onPipeline m n f hf epsB deltaF epsF := by
  classical
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNpos
  by_contra hnone
  have hall := (not_hasCombinatorialScrambleBF_onPipeline_iff (m := m) (n := n) (f := f)).1 hnone
  set badB : Finset (Scramble m n) :=
    Finset.univ.filter fun σ => ¬ HasCombinatorialPropertyBOnPipeline σ epsB
  set badF : Finset (Scramble m n) :=
    Finset.univ.filter fun σ => ¬ HasCombinatorialPropertyF hf σ deltaF epsF
  have hsub : (Finset.univ : Finset (Scramble m n)) ⊆ badB ∪ badF := by
    intro σ _
    rcases hall σ with hB | hF
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩)
  have hunion :
      (Fintype.card (Scramble m n) : ℝ) ≤ (badB ∪ badF).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard :
      (badB ∪ badF).card ≤ badB.card + badF.card :=
    Finset.card_union_le badB badF
  have hB' := hB.bound badB (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  have hF' := hF.bound badF (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  set α := lemma61_failFactor m n
  set β := lemma62_failFactor x
  have hle : (1 : ℝ) ≤ α + β := by
    have h1 : (1 : ℝ) * N ≤ (badB.card + badF.card : ℝ) := by
      calc (1 : ℝ) * N
          = N := by ring
        _ ≤ (badB ∪ badF).card := hunion
        _ ≤ badB.card + badF.card := by exact_mod_cast hcard
    have h2 : (badB.card : ℝ) ≤ α * N := by simpa [α] using hB'
    have h3 : (badF.card : ℝ) ≤ β * N := by simpa [β] using hF'
    have h4 : (badB.card + badF.card : ℝ) ≤ (α + β) * N := by
      calc (badB.card + badF.card : ℝ)
          = (badB.card : ℝ) + badF.card := by ring
        _ ≤ α * N + β * N := by gcongr
        _ = (α + β) * N := by ring
    have h5 : (1 : ℝ) * N ≤ (α + β) * N := h1.trans h4
    exact le_of_mul_le_mul_right h5 hN
  linarith [hαβ, hle]

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

theorem SortScrambleSortPack.net_eq {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) :
    p.net = sortScrambleSortNetwork m n σ p.colSort p.rowScramble := rfl

/-- Column sort then row scramble (middle stage, before the second column sort). -/
def sortScrambleMiddleNetwork (m n : Nat) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ) :
    ComparatorNetwork (m * n) :=
  ⟨colSort.net.comparators ++ rowScramble.net.comparators⟩

/-- Semantic middle stage: column sort then wire relabeling / row-local comparators. -/
def sortScrambleMiddleExec {m n : Nat} {σ : Scramble m n}
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) : Fin (m * n) → α :=
  rowScramble.wiredExec (colSort.net.exec v)

def SortScrambleSortPack.middleNet {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) : ComparatorNetwork (m * n) :=
  sortScrambleMiddleNetwork m n σ p.colSort p.rowScramble

def SortScrambleSortPack.middleExec {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  sortScrambleMiddleExec p.colSort p.rowScramble v

theorem SortScrambleSortPack.middle_exec_eq {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) :
    p.middleExec v = p.rowScramble.wiredExec (p.colSort.net.exec v) := rfl

theorem SortScrambleSortPack.middleExec_eq_rowNet_of_wirePerm_one {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (p : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (hπ : p.rowScramble.wirePerm = 1) :
    p.middleExec v = p.rowScramble.net.exec (p.colSort.net.exec v) := by
  rw [SortScrambleSortPack.middle_exec_eq, RowScrambleNetwork.wiredExec, hπ]
  simp [_root_.permuteWireValues_one]

/-- Final column sort after wire relabeling in the middle stage (Chvátal §5 semantics). -/
def SortScrambleSortPack.semanticExec {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  pack.colSort.net.exec (pack.middleExec v)

/-- Chvátal §5 sort–scramble–sort on keys: column sort, wire relabel / row stage, column sort. -/
def SortScrambleSortPack.semanticKeyExec {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (v : Equiv.Perm (Fin (m * n))) :
    Fin (m * n) → Fin (m * n) :=
  pack.semanticExec (v : Fin (m * n) → Fin (m * n))

/-- Row scramble implements combinatorial `σ` on monotone `0–1` inputs after column sort. -/
structure RowScrambleCorrect (m n : Nat) (hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ) : Prop where
  maps_scramble :
    ∀ (c : MonotoneColumnSums m n) (r : Fin m) (j : Fin n),
      sortScrambleMiddleExec colSort rowScramble (monotoneMatrixBool hn c)
          (matrixWire m n r j) = true ↔
        j ∈ scrambledRowOnes c σ r

/-- Alias: row-local network plus semantic scramble action on column-sorted monotone inputs. -/
def ImplementsScramble (m n : Nat) (hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ) : Prop :=
  RowScrambleCorrect m n hn σ colSort rowScramble

/-- Count of `true` wires strictly above the bottom `i` rows after `net` on a Boolean input. -/
def matrixOnesCountAboveBottom {m n : Nat} (hn : 0 < n) (net : ComparatorNetwork (m * n))
    (v : Fin (m * n) → Bool) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      (matrixRow m n hn w).val < m - i ∧
        net.exec v w = true).card

/-- Count of `true` wires in the same above-bottom row region (no network applied). -/
def matrixOnesCountInRegion {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      (matrixRow m n hn w).val < m - i ∧ v w = true).card

theorem matrixOnesCountAboveBottom_eq_inRegion {m n : Nat} (hn : 0 < n)
    (net : ComparatorNetwork (m * n)) (v : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountAboveBottom hn net v i =
      matrixOnesCountInRegion hn (net.exec v) i := rfl

theorem matrixOnesCountInRegion_permuteWireValues_rowPreserving {m n : Nat} (hn : 0 < n)
    (π : Equiv.Perm (Fin (m * n))) (hrow : ∀ w, matrixRow m n hn (π w) = matrixRow m n hn w)
    (v : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (permuteWireValues π v) i =
      matrixOnesCountInRegion hn v i := by
  classical
  simp only [matrixOnesCountInRegion, permuteWireValues]
  apply Finset.card_bij (fun w _ => π w)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine ⟨?_, hw.2⟩
    exact (congrArg Fin.val (hrow w)).symm ▸ hw.1
  · intro w _ w' _ h
    exact π.injective h
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    refine ⟨π.symm z, ⟨?_, ?_⟩, Equiv.apply_symm_apply π z⟩
    · have heq := congrArg Fin.val (hrow (π.symm z))
      rw [Equiv.apply_symm_apply] at heq
      exact heq ▸ hz.1
    · simpa [Equiv.apply_symm_apply] using hz.2

theorem RowScrambleNetwork.wirePerm_symm_matrixRow {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (rs : RowScrambleNetwork m n σ) (w : Fin (m * n)) :
    matrixRow m n hn (rs.wirePerm.symm w) = matrixRow m n hn w := by
  -- `wirePerm` preserves rows, so its inverse does too.
  have h := RowScrambleNetwork.wirePerm_matrixRow hn rs (rs.wirePerm.symm w)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem SortScrambleSortPack.middleExec_threshold_region_eq_rowNet {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ) (i : Nat)
    (u : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn (pack.middleExec u) i =
      matrixOnesCountInRegion hn
        (pack.rowScramble.net.exec (pack.colSort.net.exec u)) i := by
  have hmid :
      pack.middleExec u =
        permuteWireValues pack.rowScramble.wirePerm.symm (pack.colSort.net.exec u) := by
    rw [SortScrambleSortPack.middle_exec_eq]
    exact RowScrambleNetwork.wiredExec_eq_perm_of_nil pack.rowScramble
      pack.rowScramble.comparators_eq_nil (pack.colSort.net.exec u)
  have hnet :
      pack.rowScramble.net.exec (pack.colSort.net.exec u) = pack.colSort.net.exec u := by
    simp [pack.rowScramble.comparators_eq_nil, ComparatorNetwork.exec]
  rw [hmid, hnet]
  exact matrixOnesCountInRegion_permuteWireValues_rowPreserving hn pack.rowScramble.wirePerm.symm
    (RowScrambleNetwork.wirePerm_symm_matrixRow hn pack.rowScramble) (pack.colSort.net.exec u) i

/-- Top-`j` key threshold (Property F uses largest `j` keys, not `j·n`). -/
def largestKeyThresholdJ01 {m n : Nat} (j : Nat) (key : Fin (m * n)) : Bool :=
  decide (m * n - j ≤ key.val)

theorem largestKeyThresholdJ01_monotone {m n : Nat} (j : Nat) :
    Monotone (largestKeyThresholdJ01 (m := m) (n := n) j) := by
  intro a b hab
  unfold largestKeyThresholdJ01
  by_cases ha : m * n - j ≤ a.val
  · have hb : m * n - j ≤ b.val := le_trans ha (Fin.mk_le_mk.mp hab)
    simp [ha, hb]
  · by_cases hb : m * n - j ≤ b.val
    · simp [ha, hb]
    · simp [ha, hb]

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

/-- Alias: matrix Property F on `pack.semanticExec`. -/
abbrev HasMatrixPropertyF_exec (m n : Nat) (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (f : Nat) (hfm : f ≤ m) (deltaF epsF : ℝ) :=
  HasPackSemanticPropertyF hn pack f hfm deltaF epsF

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

def ScrambleSeparatorWitness.ofSemanticSeparator {g : ScrambleGeometry} {P : Theorem51Params g}
    (s : SemanticSeparator g P) : ScrambleSeparatorWitness g P :=
  ⟨s⟩

/-- Theorem 5.1 existence statement (paper conclusion). -/
def ExistsScrambleSeparator (g : ScrambleGeometry) (P : Theorem51Params g) : Prop :=
  Nonempty (ScrambleSeparatorWitness g P)

/-- Residual: Thm 5.1 scramble existence for a concrete geometry/params. -/
structure Theorem51Obligation (g : ScrambleGeometry) (P : Theorem51Params g) where
  exists_separator : ExistsScrambleSeparator g P

/-- Property F intrusion is an above-bottom count for the top-`j` key marking (fringe depth `f`). -/
theorem matrixIntrusionCountF_eq_matrixOnesCountAboveBottom {m n : Nat} (hn : 0 < n)
    (net : ComparatorNetwork (m * n)) (v : Equiv.Perm (Fin (m * n))) (f j : Nat)
    (hfm : f ≤ m) :
    matrixIntrusionCountF net v f j =
      matrixOnesCountAboveBottom hn net
        (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) f := by
  classical
  unfold matrixIntrusionCountF matrixOnesCountAboveBottom largestKeyThresholdJ01
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcomm :
      net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) =
        largestKeyThresholdJ01 (m := m) (n := n) j ∘ net.exec (v : Fin (m * n) → Fin (m * n)) :=
    (net.exec_comp_monotone (f := largestKeyThresholdJ01 (m := m) (n := n) j)
        (largestKeyThresholdJ01_monotone (m := m) (n := n) j)
        (v : Fin (m * n) → Fin (m * n))).symm
  have hrow : w.val < (m - f) * n ↔ (matrixRow m n hn w).val < m - f := by
    rw [← mem_aboveBottomRows_iff (i := f) (hi := hfm),
      mem_aboveBottomRows_iff_row hn (i := f) (hi := hfm) w]
  rw [hrow]
  have hfw :
      net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) w =
        largestKeyThresholdJ01 (m := m) (n := n) j (net.exec (v : Fin (m * n) → Fin (m * n)) w) := by
    rw [hcomm, Function.comp]
  constructor
  · intro ⟨hr, hk⟩
    refine ⟨hr, ?_⟩
    change net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) w = true
    rw [hfw]
    exact decide_eq_true_iff.mpr hk
  · intro ⟨hr, hb⟩
    refine ⟨hr, ?_⟩
    have hb' : net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) w = true := by
      simpa [largestKeyThresholdJ01] using hb
    rw [hfw] at hb'
    exact decide_eq_true_iff.mp hb'

def middleMonotoneOneCountAboveBottom {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (c : MonotoneColumnSums m n) (i : Nat) : Nat :=
  matrixOnesCountInRegion hn (pack.middleExec (monotoneMatrixBool hn c)) i

theorem RowScrambleCorrect.middleMonotoneOneCountAboveBottom_eq_scrambledOnes
    {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (i : Nat) :
    middleMonotoneOneCountAboveBottom hn pack c i =
      scrambledOnesInAboveBottomRows hn c σ i := by
  classical
  unfold middleMonotoneOneCountAboveBottom matrixOnesCountInRegion
  let mb := monotoneMatrixBool hn c
  let mid := pack.middleExec mb
  have hwire (r : Fin m) (j : Fin n) :
      mid (matrixWire m n r j) = true ↔ j ∈ scrambledRowOnes c σ r := by
    dsimp [mid, SortScrambleSortPack.middleExec]
    exact hrow.maps_scramble c r j
  have hpoint (w : Fin (m * n)) :
      mid w = true ↔ scrambledMatrix01 hn c σ w := by
    let r := matrixRow m n hn w
    let j := matrixCol m n hn w
    rw [← matrixWire_matrixRow_col hn w, hwire r j, matrixWire_scrambledMatrix01 hn c σ r j]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mid, mb, hpoint w, scrambledMatrix01]

/-- Middle-stage monotone `0–1` wire count matches scrambled ones above the bottom block. -/
theorem onesAboveBottom_le_middleMonotoneOneCountAboveBottom {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (i : Nat) (_hi1 : 1 ≤ i) (him : i ≤ m) :
    onesAboveBottom c σ i ≤ middleMonotoneOneCountAboveBottom hn pack c i := by
  rw [RowScrambleCorrect.middleMonotoneOneCountAboveBottom_eq_scrambledOnes hn pack hrow c i]
  exact onesAboveBottom_le_scrambledOnesInAboveBottomRows hn c σ i him

theorem middleMonotoneOneCountAboveBottom_le_onesAboveBottom {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hle : middleMonotoneOneCountAboveBottom hn pack c i ≤ onesAboveBottom c σ i) :
    middleMonotoneOneCountAboveBottom hn pack c i ≤ onesAboveBottom c σ i :=
  hle

theorem middleMonotoneOneCountAboveBottom_eq_onesAboveBottom_of_antisandwich {m n : Nat}
    (hn : 0 < n) {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hle : middleMonotoneOneCountAboveBottom hn pack c i ≤ onesAboveBottom c σ i) :
    middleMonotoneOneCountAboveBottom hn pack c i = onesAboveBottom c σ i := by
  exact le_antisymm hle (onesAboveBottom_le_middleMonotoneOneCountAboveBottom hn pack hrow c i hi1 him)

/-- Matrix Property B intrusion on the middle network (before the second column sort). -/
abbrev matrixIntrusionCountB_middle {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (v : Equiv.Perm (Fin (m * n))) (i : Nat) : Nat :=
  matrixIntrusionCountB pack.middleNet v i

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

/-- Vacuous geometry (`m = 0`): no levels `1 ≤ i ≤ m`. -/
theorem MiddleStageDecodeHyp.of_zero_rows {n : Nat} (hn : 0 < n) :
    MiddleStageDecodeHyp 0 n hn where
  decode := fun _σ _pack _hcol _hrow _v i _hi1 _him =>
    ⟨fun _j => 0, by omega⟩

/-- Target B-bridge inequality for permutations; packaged as `MiddleStageDecodeHyp`. -/
theorem packSemanticIntrusionCountB_le_onesAboveBottom_of_decodeHyp {m n : Nat} (hn : 0 < n)
    (h : MiddleStageDecodeHyp m n hn) (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m) :
    ∃ c : MonotoneColumnSums m n,
      packSemanticIntrusionCountB hn pack v i ≤ onesAboveBottom c σ i := by
  exact h.decode σ pack hcol hrow v i hi1 him

/-- Per-input link: matrix Property B intrusion is bounded by combinatorial `onesAboveBottom`. -/
structure MiddleStageToMatrixB (m n : Nat) (hn : 0 < n) where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (_hcol : IdealColumnSort m n hn pack.colSort)
      (v : Equiv.Perm (Fin (m * n))),
      ∀ i, 1 ≤ i → i ≤ m →
        ∃ (c : MonotoneColumnSums m n),
          packSemanticIntrusionCountB hn pack v i ≤ onesAboveBottom c σ i

theorem MiddleStageToMatrixB.of_decodeHyp {m n : Nat} (hn : 0 < n)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (h : MiddleStageDecodeHyp m n hn) : MiddleStageToMatrixB m n hn where
  decode := fun σ pack hcol v i hi1 him =>
    h.decode σ pack hcol (hrow σ pack) v i hi1 him

/-- Vacuous geometry (`m = 0`): no levels `1 ≤ i ≤ m`. -/
theorem MiddleStageToMatrixB_of_zero_rows {n : Nat} (hn : 0 < n) :
    MiddleStageToMatrixB 0 n hn where
  decode := fun _σ _pack _hcol _v i _hi1 _him =>
    ⟨fun _j => 0, by omega⟩

theorem MiddleStageToMatrixB.packSemanticIntrusionCountB_le_scrambledOnesInAboveBottomRows
    {m n : Nat} (hn : 0 < n) (hm : MiddleStageToMatrixB m n hn)
    (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m) :
    ∃ c : MonotoneColumnSums m n,
      packSemanticIntrusionCountB hn pack v i ≤ scrambledOnesInAboveBottomRows hn c σ i := by
  obtain ⟨c, hle⟩ := hm.decode σ pack hcol v i hi1 him
  refine ⟨c, le_trans hle (onesAboveBottom_le_scrambledOnesInAboveBottomRows hn c σ i him)⟩

/-- B-side only: combinatorial Property B ⇒ semantic matrix Property B on the pack. -/
structure CombinatorialToMatrixObligationB (m n : Nat) (hn : 0 < n) (epsB : ℝ) where
  matrixB :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      HasCombinatorialPropertyB σ epsB →
        HasPackSemanticPropertyB hn pack epsB

theorem CombinatorialToMatrixObligationB.of_idealColumnSort {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hmiddle : MiddleStageToMatrixB m n hn) :
    CombinatorialToMatrixObligationB m n hn epsB where
  matrixB := by
    intro σ pack hComb
    rw [HasPackSemanticPropertyB_iff]
    intro v i hi1 him
    obtain ⟨c, hle⟩ := hmiddle.decode σ pack (hcol σ pack) v i hi1 him
    exact lt_of_le_of_lt (by exact_mod_cast hle) (hComb c i hi1 him)

theorem CombinatorialToMatrixObligationB.of_idealColumnSort_rowScrambleCorrect_decodeHyp
    {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hdecode : MiddleStageDecodeHyp m n hn) :
    CombinatorialToMatrixObligationB m n hn epsB :=
  CombinatorialToMatrixObligationB.of_idealColumnSort hn hcol
    (MiddleStageToMatrixB.of_decodeHyp hn hrow hdecode)

/-- F-side only: combinatorial Property F ⇒ matrix Property F on the pack network. -/
structure CombinatorialToMatrixObligationF (m n f : Nat) (hn : 0 < n) (hf : Even f) (hfm : f ≤ m)
    (deltaF epsF : ℝ) where
  matrixF :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      HasCombinatorialPropertyF hf σ deltaF epsF →
        HasPackSemanticPropertyF hn pack f hfm deltaF epsF

theorem rowHit_univ_eq_scrambledRowOnes_card {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (r : Fin m) :
    rowHit c (Finset.univ : Finset (Fin n)) r (σ r) = (scrambledRowOnes c σ r).card := by
  simp [rowHit, scrambledRowOnes, Finset.inter_univ]

theorem onesAboveHalfFringe_univ_eq_sum_scrambledRowOnes {m n f : Nat} {hf : Even f}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) :
    onesAboveHalfFringe hf c σ (Finset.univ : Finset (Fin n)) =
      ∑ r ∈ aboveHalfFringeRows m f hf, (scrambledRowOnes c σ r).card := by
  rw [onesAboveHalfFringe_eq_sum_rowHit]
  refine Finset.sum_congr rfl fun r _ => rowHit_univ_eq_scrambledRowOnes_card c σ r

theorem aboveBottomRowFilter_subset_aboveHalfFringeRows {m f : Nat} {hf : Even f} :
    (Finset.univ.filter fun r : Fin m => r.val < m - f) ⊆
      aboveHalfFringeRows m f hf := by
  intro r hr
  have hr' : r.val < m - f := (Finset.mem_filter.mp hr).2
  simp only [aboveHalfFringeRows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_of_lt_of_le hr' (Nat.sub_le_sub_left (Nat.div_le_self f 2) m)

theorem scrambledOnesInAboveBottomRowsSum_eq_sum_rowFilter {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    scrambledOnesInAboveBottomRowsSum c σ i =
      ∑ r ∈ Finset.univ.filter fun r : Fin m => r.val < m - i,
        (scrambledRowOnes c σ r).card := by
  classical
  unfold scrambledOnesInAboveBottomRowsSum
  rw [← Finset.sum_filter (s := Finset.univ)
    (p := fun r : Fin m => r.val < m - i)
    (f := fun r => (scrambledRowOnes c σ r).card)]

theorem scrambledOnesInAboveBottomRowsSum_le_onesAboveHalfFringe_univ {m n f : Nat} {hf : Even f}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) :
    scrambledOnesInAboveBottomRowsSum c σ f ≤
      onesAboveHalfFringe hf c σ (Finset.univ : Finset (Fin n)) := by
  rw [scrambledOnesInAboveBottomRowsSum_eq_sum_rowFilter,
    onesAboveHalfFringe_univ_eq_sum_scrambledRowOnes]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (aboveBottomRowFilter_subset_aboveHalfFringeRows (m := m) (f := f) (hf := hf)) ?_
  intro r _ _
  exact Nat.zero_le _

theorem onesAboveBottom_le_onesAboveHalfFringe_univ {m n f : Nat} {hf : Even f} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (him : f ≤ m) :
    onesAboveBottom c σ f ≤
      onesAboveHalfFringe hf c σ (Finset.univ : Finset (Fin n)) := by
  exact le_trans (onesAboveBottom_le_scrambledOnesInAboveBottomRowsSum c σ f him)
    (scrambledOnesInAboveBottomRowsSum_le_onesAboveHalfFringe_univ c σ)

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

/-- Target F-bridge inequality; packaged as `MiddleStageFringeDecodeHyp`. -/
theorem packSemanticIntrusionCountF_le_onesAboveHalfFringe_of_fringeDecodeHyp {m n f : Nat} {hf : Even f}
    {hn : 0 < n} {deltaF epsF : ℝ}
    (h : MiddleStageFringeDecodeHyp m n f hf hn deltaF) (σ : Scramble m n)
    (pack : SortScrambleSortPack m n hn σ) (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (j : Nat) (hj : 0 < j)
    (hjδ : (j : ℝ) ≤ deltaF * (f * n)) :
    ∃ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
      packSemanticIntrusionCountF hn pack v f j ≤ onesAboveHalfFringe hf c σ S :=
  h.decode σ pack hcol hrow v j hj hjδ

structure MiddleStageToMatrixF (m n f : Nat) (hf : Even f) (hn : 0 < n) (deltaF epsF : ℝ) where
  decode :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
      (hcol : IdealColumnSort m n hn pack.colSort)
      (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
      (v : Equiv.Perm (Fin (m * n))) (j : Nat) (hj : 0 < j)
      (hjδ : (j : ℝ) ≤ deltaF * (f * n)),
      ∃ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
        packSemanticIntrusionCountF hn pack v f j ≤ onesAboveHalfFringe hf c σ S

theorem MiddleStageToMatrixF.of_fringeDecodeHyp {m n f : Nat} {hf : Even f} {hn : 0 < n}
    {deltaF epsF : ℝ} (h : MiddleStageFringeDecodeHyp m n f hf hn deltaF) :
    MiddleStageToMatrixF m n f hf hn deltaF epsF where
  decode := h.decode

/-- Residual closing step: intrusion ≤ `onesAboveHalfFringe` ⇒ matrix Property F. -/
def FringePropertyFClosingHyp (m n f : Nat) (hn : 0 < n) (hf : Even f) (hfm : f ≤ m)
    (deltaF epsF : ℝ) : Prop :=
  ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ)
    (hComb : HasCombinatorialPropertyF hf σ deltaF epsF) (v : Equiv.Perm (Fin (m * n)))
    (j : Nat) (hj : 0 < j) (hjδ : (j : ℝ) ≤ deltaF * (f * n))
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
    packSemanticIntrusionCountF hn pack v f j ≤ onesAboveHalfFringe hf c σ S →
      (packSemanticIntrusionCountF hn pack v f j : ℝ) < epsF * j

theorem CombinatorialToMatrixObligationF.of_fringeDecodeHyp_and_close {m n f : Nat}
    {hf : Even f} {hfm : f ≤ m} {deltaF epsF : ℝ} (hn : 0 < n)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hdecode : MiddleStageFringeDecodeHyp m n f hf hn deltaF)
    (hclose : FringePropertyFClosingHyp m n f hn hf hfm deltaF epsF) :
    CombinatorialToMatrixObligationF (m := m) (n := n) (f := f) (hn := hn) (hf := hf) (hfm := hfm)
      (deltaF := deltaF) (epsF := epsF) where
  matrixF := fun σ pack hComb => by
    rw [HasPackSemanticPropertyF_iff]
    intro v j hj hjδ
    obtain ⟨c, S, hle⟩ :=
      hdecode.decode σ pack (hcol σ pack) (hrow σ pack) v j hj hjδ
    exact hclose σ pack hComb v j hj hjδ c S hle

/-- Residual sub-steps for the B-bridge (not yet discharged). -/
structure MatrixBridgeBResidual (m n : Nat) (hn : 0 < n) (epsB : ℝ) where
  /-- Ideal column sort on every pack (embedded column sorters). -/
  ideal_column_sort :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort
  /-- Row scramble implements combinatorial `σ` on sorted monotone `0–1` inputs. -/
  row_scramble_correct :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble
  /-- Permutation decode to `onesAboveBottom` (see `MiddleStageDecodeHyp`). -/
  middle_stage_decode : MiddleStageDecodeHyp m n hn

theorem MatrixBridgeBResidual.combinatorialToMatrixObligationB {m n : Nat} {hn : 0 < n} {epsB : ℝ}
    (h : MatrixBridgeBResidual m n hn epsB) :
    CombinatorialToMatrixObligationB m n hn epsB :=
  CombinatorialToMatrixObligationB.of_idealColumnSort_rowScrambleCorrect_decodeHyp hn
    h.ideal_column_sort h.row_scramble_correct h.middle_stage_decode

/-- B-bridge residuals when universal ideal column sort + row scramble correctness hold.
    The decode field is supplied separately (discharged in `SortedColumnDecode`). -/
theorem MatrixBridgeBResidual.of_columnSortNetwork_rowScramble {m n : Nat} {hn : 0 < n} {epsB : ℝ}
    (hdecode : MiddleStageDecodeHyp m n hn)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    MatrixBridgeBResidual m n hn epsB where
  ideal_column_sort := hcol
  row_scramble_correct := hrow
  middle_stage_decode := hdecode

/-- Residual sub-steps for the F-bridge (fringe decode + closing step). -/
structure MatrixBridgeFResidual (m n f : Nat) (hf : Even f) (hn : 0 < n) (hfm : f ≤ m)
    (deltaF epsF : ℝ) where
  ideal_column_sort :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort
  row_scramble_correct :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble
  middle_stage_fringe_decode : MiddleStageFringeDecodeHyp m n f hf hn deltaF
  fringe_property_f_close : FringePropertyFClosingHyp m n f hn hf hfm deltaF epsF

theorem MatrixBridgeFResidual.combinatorialToMatrixObligationF {m n f : Nat} {hf : Even f}
    {hn : 0 < n} {hfm : f ≤ m} {deltaF epsF : ℝ}
    (h : MatrixBridgeFResidual m n f hf hn hfm deltaF epsF) :
    CombinatorialToMatrixObligationF (m := m) (n := n) (f := f) (hn := hn) (hf := hf) (hfm := hfm)
      (deltaF := deltaF) (epsF := epsF) :=
  CombinatorialToMatrixObligationF.of_fringeDecodeHyp_and_close (m := m) (n := n) (f := f) (hf := hf)
    (hfm := hfm) (deltaF := deltaF) (epsF := epsF) hn h.ideal_column_sort h.row_scramble_correct
    h.middle_stage_fringe_decode h.fringe_property_f_close

/-- Combinatorial Property B/F on a scramble implies matrix B/F on its pack (paper §6 bridge). -/
structure CombinatorialToMatrixObligation (m n f : Nat) (hn : 0 < n) (hf : Even f) (hfm : f ≤ m)
    (epsB deltaF epsF : ℝ) where
  matrixB :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      HasCombinatorialPropertyB σ epsB →
        HasPackSemanticPropertyB hn pack epsB
  matrixF :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      HasCombinatorialPropertyF hf σ deltaF epsF →
        HasPackSemanticPropertyF hn pack f hfm deltaF epsF

theorem CombinatorialToMatrixObligation.of_split {m n f : Nat} {hn : 0 < n} {hf : Even f} {hfm : f ≤ m}
    {epsB deltaF epsF : ℝ}
    (hB : CombinatorialToMatrixObligationB m n hn epsB)
    (hF : CombinatorialToMatrixObligationF m n f hn hf hfm deltaF epsF) :
    CombinatorialToMatrixObligation m n f hn hf hfm epsB deltaF epsF where
  matrixB := hB.matrixB
  matrixF := hF.matrixF

/-- Convenience: default pack from a row-scramble witness. -/
def SortScrambleSortPack.ofRowScramble {m n : Nat} (hn : 0 < n) {σ : Scramble m n}
    (rowScramble : RowScrambleNetwork m n σ) : SortScrambleSortPack m n hn σ :=
  { rowScramble := rowScramble }

theorem SortScrambleSortPack.exec_eq {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) :
    pack.net.exec v =
      pack.colSort.net.exec (pack.rowScramble.net.exec (pack.colSort.net.exec v)) := by
  rw [SortScrambleSortPack.net_eq, sortScrambleSortNetwork]
  rw [ComparatorNetwork.exec_append, ComparatorNetwork.exec_append]

theorem SortScrambleSortPack.exec_eq_of_wirePerm_one {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (hπ : pack.rowScramble.wirePerm = 1) :
    pack.net.exec v = pack.colSort.net.exec (pack.middleExec v) := by
  rw [SortScrambleSortPack.exec_eq pack v, SortScrambleSortPack.middleExec_eq_rowNet_of_wirePerm_one pack v hπ]

/-! **Threshold marking, intrusion count, and decode residuals** -/

/-- Largest-key Property B intrusion is an above-bottom count for the threshold marking input. -/
theorem matrixIntrusionCountB_eq_matrixOnesCountAboveBottom {m n : Nat} (hn : 0 < n)
    (net : ComparatorNetwork (m * n)) (v : Equiv.Perm (Fin (m * n))) (i : Nat) (him : i ≤ m) :
    matrixIntrusionCountB net v i =
      matrixOnesCountAboveBottom hn net (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) i := by
  classical
  unfold matrixIntrusionCountB matrixOnesCountAboveBottom largestKeyThreshold01
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcomm :
      net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) =
        largestKeyThreshold01 (m := m) (n := n) i ∘ net.exec (v : Fin (m * n) → Fin (m * n)) :=
    (net.exec_comp_monotone (f := largestKeyThreshold01 (m := m) (n := n) i)
        (largestKeyThreshold01_monotone (m := m) (n := n) i) (v : Fin (m * n) → Fin (m * n))).symm
  have hrow : w.val < (m - i) * n ↔ (matrixRow m n hn w).val < m - i := by
    rw [← mem_aboveBottomRows_iff (i := i) (hi := him),
      mem_aboveBottomRows_iff_row hn (i := i) (hi := him) w]
  rw [hrow]
  have hfw :
      net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) w =
        largestKeyThreshold01 (m := m) (n := n) i (net.exec (v : Fin (m * n) → Fin (m * n)) w) := by
    rw [hcomm, Function.comp]
  constructor
  · intro ⟨hr, hk⟩
    refine ⟨hr, ?_⟩
    change net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) w = true
    rw [hfw]
    exact decide_eq_true_iff.mpr hk
  · intro ⟨hr, hb⟩
    refine ⟨hr, ?_⟩
    have hb' : net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) w = true := by
      simpa [largestKeyThreshold01, isAmongLargestKeysBlock] using hb
    rw [hfw] at hb'
    exact decide_eq_true_iff.mp hb'

/-- First-sort rank marking at `(r,j)` (column sums in `monotoneColumnSumsAtLevel`). -/
def firstSortLargestKeyMark01 {m n : Nat} (v : Fin (m * n) → Fin (m * n))
    (colSort : ColumnSortNetwork m n) (i : Nat) (r : Fin m) (j : Fin n) : Bool :=
  largestKeyBlock01 v i (colSort.net.exec v (matrixWire m n r j))

/-- Residual: rank wire index at `(r,j)` agrees with threshold on the occupying key. -/
def FirstSortMarkingAgreesThreshold (m n : Nat) (_hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (i : Nat) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (r : Fin m) (j : Fin n),
    firstSortLargestKeyMark01 v colSort i r j =
      largestKeyThreshold01 (m := m) (n := n) i (colSort.net.exec v (matrixWire m n r j))

/-- Residual: first-sort rank marking is `monotoneMatrixBool` for `monotoneColumnSumsAtLevel`. -/
def FirstSortMarkingEqMonotone (m n : Nat) (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (i : Nat) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (r : Fin m) (j : Fin n),
    let c := monotoneColumnSumsAtLevel hn colSort v i
    firstSortLargestKeyMark01 v colSort i r j =
      monotoneMatrixBool hn c (matrixWire m n r j)

/-- Residual sub-step: ideal second column sort does not increase above-bottom `true` counts
    (see `AKS.Chvatal.ColumnOnesRegion`). -/
def MiddleStageSecondColSortHyp (m n : Nat) (hn : 0 < n) : Prop :=
  ∀ (colSort : ColumnSortNetwork m n) (_hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) (i : Nat) (him : i ≤ m),
    matrixOnesCountAboveBottom hn colSort.net (colSort.net.exec v) i ≤
      matrixOnesCountAboveBottom hn colSort.net v i

/-- Residual sub-step: threshold marking through column sort + row scramble matches
    `middleMonotoneOneCountAboveBottom` for `c = monotoneColumnSumsAtLevel`. -/
def MiddleStageMarkingToMiddleCountHyp (m n : Nat) (hn : 0 < n) (iLevel : Nat) : Prop :=
  ∀ {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (_hcol : IdealColumnSort m n hn pack.colSort)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hmark : FirstSortMarkingEqMonotone m n hn pack.colSort iLevel)
    (_hagree : FirstSortMarkingAgreesThreshold m n hn pack.colSort iLevel)
    (v : Equiv.Perm (Fin (m * n))) (him : iLevel ≤ m),
    matrixOnesCountInRegion hn
        (pack.middleExec (fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w))) iLevel =
      middleMonotoneOneCountAboveBottom hn pack (monotoneColumnSumsAtLevel hn pack.colSort v iLevel)
        iLevel

/-- After ideal column sort, threshold marking on wire-index keys becomes `monotoneMatrixBool`
    at `c = monotoneColumnSumsAtLevel`. -/
theorem colSort_exec_largestKeyThreshold01_eq_monotoneMatrixBool {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (iLevel : Nat) (v : Equiv.Perm (Fin (m * n))) (r : Fin m)
    (j : Fin n)
    (hagree : firstSortLargestKeyMark01 v colSort iLevel r j =
      largestKeyThreshold01 (m := m) (n := n) iLevel
        (colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r j)))
    (hmark : firstSortLargestKeyMark01 v colSort iLevel r j =
      monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn colSort v iLevel) (matrixWire m n r j)) :
    colSort.net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w))
        (matrixWire m n r j) =
      monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn colSort v iLevel) (matrixWire m n r j) := by
  set u := fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w)
  have hwire :
      colSort.net.exec u (matrixWire m n r j) =
        largestKeyThreshold01 (m := m) (n := n) iLevel
          (colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r j)) := by
    have hcomp :=
      (colSort.net.exec_comp_monotone (f := largestKeyThreshold01 (m := m) (n := n) iLevel)
          (largestKeyThreshold01_monotone (m := m) (n := n) iLevel)
          (v : Fin (m * n) → Fin (m * n))).symm
    simpa [u, Function.comp] using congrArg (fun g => g (matrixWire m n r j)) hcomp
  rw [hwire, hagree.symm.trans hmark]

private theorem middleNet_thresholdOnesCount_eq_middleMonotoneCount {m n : Nat} (hn : 0 < n)
    (iLevel : Nat) {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n)))
    (hcell :
      ∀ (r : Fin m) (j : Fin n),
        firstSortLargestKeyMark01 v pack.colSort iLevel r j =
          largestKeyThreshold01 (m := m) (n := n) iLevel
            (pack.colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r j)) ∧
          firstSortLargestKeyMark01 v pack.colSort iLevel r j =
            monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn pack.colSort v iLevel)
              (matrixWire m n r j)) :
    matrixOnesCountInRegion hn
        (pack.middleExec (fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w))) iLevel =
      middleMonotoneOneCountAboveBottom hn pack (monotoneColumnSumsAtLevel hn pack.colSort v iLevel)
        iLevel := by
  set c := monotoneColumnSumsAtLevel hn pack.colSort v iLevel
  set mb := monotoneMatrixBool hn c
  set u := fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w)
  have hcm_col : ColumnMonotoneInput m n hn (pack.colSort.net.exec u) :=
    IdealColumnSort.exec_columnMonotoneInput hn pack.colSort hcol u
  have hcm_mb : ColumnMonotoneInput m n hn mb :=
    ColumnMonotoneInput_monotoneMatrixBool hn c
  have hcol_u : ∀ (r : Fin m) (j : Fin n),
      pack.colSort.net.exec u (matrixWire m n r j) = mb (matrixWire m n r j) := fun r j =>
    colSort_exec_largestKeyThreshold01_eq_monotoneMatrixBool hn pack.colSort iLevel v r j
      (hcell r j).1 (hcell r j).2
  have hu_eq_mb : pack.colSort.net.exec u = mb :=
    ColumnMonotoneInput.eq_of_matrixWire_eq hn hcm_col hcm_mb hcol_u
  have hcol_mb : pack.colSort.net.exec mb = mb :=
    IdealColumnSort.exec_eq_of_columnMonotoneInput hn pack.colSort hcol mb hcm_mb
  have hmid : pack.middleExec u = pack.middleExec mb := by
    rw [SortScrambleSortPack.middle_exec_eq, SortScrambleSortPack.middle_exec_eq, hu_eq_mb, hcol_mb]
  dsimp [middleMonotoneOneCountAboveBottom]
  rw [hmid]

theorem MiddleStageMarkingToMiddleCountHyp.of_firstSortMarking {m n : Nat} (hn : 0 < n)
    (iLevel : Nat) : MiddleStageMarkingToMiddleCountHyp m n hn iLevel := by
  intro σ pack hcol hrow hmark hagree v _him
  refine middleNet_thresholdOnesCount_eq_middleMonotoneCount hn iLevel pack hcol hrow v ?_
  intro r j
  exact ⟨hagree v r j, hmark v r j⟩

/-! **Rank-wire vs key-threshold marking (Chvátal §6 decode sub-step)** -/

/-- Standard matrix labeling: wire `w` initially holds key `w` (rank equals wire index). -/
def KeysAreWireIndices {m n : Nat} (v : Equiv.Perm (Fin (m * n))) : Prop :=
  ∀ w : Fin (m * n), v w = w

theorem KeysAreWireIndices.one {m n : Nat} : KeysAreWireIndices (1 : Equiv.Perm (Fin (m * n))) := by
  intro w
  simp

def colSortKeyAt {m n : Nat} (colSort : ColumnSortNetwork m n)
    (v : Equiv.Perm (Fin (m * n))) (r : Fin m) (j : Fin n) : Fin (m * n) :=
  colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r j)

private theorem isAmongLargestKeysBlock_monotone_up {m n : Nat} (i : Nat)
    {a b : Fin (m * n)} (hab : a ≤ b) :
    isAmongLargestKeysBlock i a → isAmongLargestKeysBlock i b := by
  unfold isAmongLargestKeysBlock
  intro ha
  exact Nat.le_trans ha (Fin.mk_le_mk.mp hab)

/-- Rank-wire marking agrees with key threshold when keys are wire indices (Chvátal §6).

The packaged Prop `FirstSortMarkingAgreesThreshold` quantifies over all permutations; in general
rank marking uses `v` at the wire index of the occupying key, so agreement with the key
threshold requires the wire-index labeling below (or an equivalent hypothesis). -/
theorem firstSortMarking_agreesThreshold_of_keysAreWireIndices {m n : Nat} (_hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (i : Nat) {v : Equiv.Perm (Fin (m * n))}
    (hkeys : KeysAreWireIndices v) (r : Fin m) (j : Fin n) :
    firstSortLargestKeyMark01 v colSort i r j =
      largestKeyThreshold01 (m := m) (n := n) i (colSortKeyAt colSort v r j) := by
  unfold firstSortLargestKeyMark01 largestKeyBlock01 largestKeyThreshold01 colSortKeyAt
  simp [hkeys (colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r j)),
    KeysAreWireIndices]

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

private theorem isAmongLargestKeysBlock_colSortKey_iff_le_colSum
    {m n : Nat} (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (hcol : IdealColumnSort m n hn colSort) (v : Equiv.Perm (Fin (m * n))) (i : Nat)
    (hkeys : KeysAreWireIndices v) (j : Fin n) (r : Fin m) :
    isAmongLargestKeysBlock i (colSortKeyAt colSort v r j) ↔
      (m - r.val) ≤ (monotoneColumnSumsAtLevel hn colSort v i j).val := by
  classical
  set c := monotoneColumnSumsAtLevel hn colSort v i
  set key : Fin m → Fin (m * n) := fun r' => colSortKeyAt colSort v r' j
  have hmono : Monotone key := by
    intro r s hrs
    dsimp only [key, colSortKeyAt]
    exact hcol j (v := (v : Fin (m * n) → Fin (m * n))) hrs
  set S : Finset (Fin m) := Finset.univ.filter fun r' : Fin m => isAmongLargestKeysBlock i (key r')
  have hfilter :
      (Finset.univ.filter fun r' : Fin m =>
          largestKeyBlock01 v i (colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r' j))) =
        S := by
    apply Finset.ext
    intro r'
    set w := colSort.net.exec (v : Fin (m * n) → Fin (m * n)) (matrixWire m n r' j)
    simp only [S, key, colSortKeyAt, largestKeyBlock01, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_iff, isAmongLargestKeysBlock]
    rw [hkeys w]
  have hsum : columnSumLargestKeysAtLevel hn colSort v i j = S.card := by
    unfold columnSumLargestKeysAtLevel
    rw [← hfilter]
  have hcount : (c j).val = S.card := by
    dsimp [c, monotoneColumnSumsAtLevel]
    simpa using hsum
  have hup :
      ∀ {r s : Fin m}, r ≤ s → isAmongLargestKeysBlock i (key r) → isAmongLargestKeysBlock i (key s) := by
    intro r s hrs hblock
    exact isAmongLargestKeysBlock_monotone_up i (hmono hrs) hblock
  by_cases ht : S.card = 0
  · have hem : S = ∅ := Finset.card_eq_zero.mp ht
    have hempty : ∀ r' : Fin m, ¬ isAmongLargestKeysBlock i (key r') := by
      intro r' hblock
      have : r' ∈ S := by simpa [S] using hblock
      rw [hem] at this
      exact Finset.notMem_empty r' this
    constructor
    · intro hblock
      exact (hempty r hblock).elim
    · intro hle
      rw [hcount, ht] at hle
      have : 0 < m - r.val := by have := r.isLt; omega
      omega
  · have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      have : S.card = 0 := by rw [hem, Finset.card_empty]
      omega
    set rMin := S.min' hne
    have hrMinmem : rMin ∈ S := Finset.min'_mem S hne
    have hrMinblock : isAmongLargestKeysBlock i (key rMin) := by simpa [S] using hrMinmem
    have hmin' : ∀ r' : Fin m, isAmongLargestKeysBlock i (key r') → rMin ≤ r' := by
      intro r' hblock
      exact Finset.min'_le S r' (by simpa [S] using hblock)
    have hge : ∀ r' : Fin m, rMin ≤ r' → isAmongLargestKeysBlock i (key r') := by
      intro r' hle
      exact hup hle hrMinblock
    have hS' : S = Finset.univ.filter fun r' : Fin m => rMin ≤ r' := by
      ext r'
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hmin' r'
      · exact hge r'
    have hcard : S.card = m - rMin.val := by rw [hS', card_filter_row_ge rMin]
    rw [hcount, hcard]
    constructor
    · intro hblock
      have := hmin' r hblock
      omega
    · intro hle
      exact hge r (by omega)

theorem firstSortLargestKeyMark01_eq_monotoneMatrixBool_of_idealColumnSort_and_keys
    {m n : Nat} (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (hcol : IdealColumnSort m n hn colSort) (i : Nat) {v : Equiv.Perm (Fin (m * n))}
    (hkeys : KeysAreWireIndices v) (r : Fin m) (j : Fin n) :
    firstSortLargestKeyMark01 v colSort i r j =
      monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn colSort v i) (matrixWire m n r j) := by
  rw [firstSortMarking_agreesThreshold_of_keysAreWireIndices hn colSort i hkeys r j]
  simp only [largestKeyThreshold01, monotoneMatrixBool, decide_eq_decide, mem_monotoneRowOnes_iff,
    matrixWire_row_col]
  exact isAmongLargestKeysBlock_colSortKey_iff_le_colSum hn colSort hcol v i hkeys j r

theorem FirstSortMarkingEqMonotone.of_idealColumnSort_and_keysAreWireIndices {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort) (i : Nat)
    {v : Equiv.Perm (Fin (m * n))} (hkeys : KeysAreWireIndices v) :
    ∀ (r : Fin m) (j : Fin n),
      firstSortLargestKeyMark01 v colSort i r j =
        monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn colSort v i) (matrixWire m n r j) :=
  firstSortLargestKeyMark01_eq_monotoneMatrixBool_of_idealColumnSort_and_keys hn colSort hcol i hkeys

/-- Per-input threshold agreement (wire-index keys); the global `FirstSortMarkingAgreesThreshold`
    Prop still quantifies over all permutations. -/
theorem FirstSortMarkingAgreesThreshold.of_keysAreWireIndices {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (i : Nat) {v : Equiv.Perm (Fin (m * n))}
    (hkeys : KeysAreWireIndices v) (r : Fin m) (j : Fin n) :
    firstSortLargestKeyMark01 v colSort i r j =
      largestKeyThreshold01 (m := m) (n := n) i (colSort.net.exec v (matrixWire m n r j)) :=
  firstSortMarking_agreesThreshold_of_keysAreWireIndices hn colSort i hkeys r j

/-- First-sort marking (monotone matrix + threshold) at a level under wire-index keys. -/
theorem idealRowMarking_eq_and_agrees_of_keysAreWireIndices {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort) (i : Nat)
    {v : Equiv.Perm (Fin (m * n))} (hkeys : KeysAreWireIndices v) :
    (∀ (r : Fin m) (j : Fin n),
        firstSortLargestKeyMark01 v colSort i r j =
          monotoneMatrixBool hn (monotoneColumnSumsAtLevel hn colSort v i) (matrixWire m n r j)) ∧
      (∀ (r : Fin m) (j : Fin n),
        firstSortLargestKeyMark01 v colSort i r j =
          largestKeyThreshold01 (m := m) (n := n) i (colSort.net.exec v (matrixWire m n r j))) :=
  ⟨FirstSortMarkingEqMonotone.of_idealColumnSort_and_keysAreWireIndices hn colSort hcol i hkeys,
    fun r j => FirstSortMarkingAgreesThreshold.of_keysAreWireIndices hn colSort i hkeys r j⟩

/-- Wire-index keys: middle threshold count equals scrambled monotone count at `monotoneColumnSumsAtLevel`. -/
theorem matrixOnesCountAboveBottom_middleNet_eq_middleMonotoneCount_of_keysAreWireIndices
    {m n : Nat} (hn : 0 < n) (iLevel : Nat) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    {v : Equiv.Perm (Fin (m * n))} (hkeys : KeysAreWireIndices v) :
    matrixOnesCountInRegion hn
        (pack.middleExec (fun w => largestKeyThreshold01 (m := m) (n := n) iLevel (v w))) iLevel =
      middleMonotoneOneCountAboveBottom hn pack (monotoneColumnSumsAtLevel hn pack.colSort v iLevel)
        iLevel :=
  middleNet_thresholdOnesCount_eq_middleMonotoneCount hn iLevel pack hcol hrow v fun r j =>
    ⟨FirstSortMarkingAgreesThreshold.of_keysAreWireIndices hn pack.colSort iLevel hkeys r j,
      firstSortLargestKeyMark01_eq_monotoneMatrixBool_of_idealColumnSort_and_keys hn pack.colSort
        hcol iLevel hkeys r j⟩

/-! **Theorem 5.1 from combinatorics + bridge** -/

def semanticSeparator_of_combinatorial_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hB : HasCombinatorialPropertyB σ P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    SemanticSeparator g P where
  σ := σ
  pack := pack
  hB := bridge.matrixB σ pack hB
  hF := bridge.matrixF σ pack hF

def scrambleSeparatorWitness_of_combinatorial_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hB : HasCombinatorialPropertyB σ P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    ScrambleSeparatorWitness g P :=
  ScrambleSeparatorWitness.ofSemanticSeparator
    (semanticSeparator_of_combinatorial_and_bridge (pack := pack) hnpos hB hF hfm bridge)

theorem ExistsScrambleSeparator_of_combinatorial_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hB : HasCombinatorialPropertyB σ P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    ExistsScrambleSeparator g P :=
  ⟨scrambleSeparatorWitness_of_combinatorial_and_bridge (pack := pack) hnpos hB hF hfm bridge⟩

def semanticSeparator_of_combinatorial_onPipeline_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hBsem : HasPackSemanticPropertyB hnpos pack P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    SemanticSeparator g P where
  σ := σ
  pack := pack
  hB := hBsem
  hF := bridge.matrixF σ pack hF

theorem ExistsScrambleSeparator_of_combinatorial_onPipeline_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hBsem : HasPackSemanticPropertyB hnpos pack P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    ExistsScrambleSeparator g P :=
  ⟨ScrambleSeparatorWitness.ofSemanticSeparator
    (semanticSeparator_of_combinatorial_onPipeline_and_bridge (pack := pack) hnpos hBsem hF hfm
      bridge)⟩

theorem Theorem51Obligation.of_combinatorial_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    {σ : Scramble g.m g.n} {pack : SortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ}
    (hnpos : 0 < g.n)
    (hB : HasCombinatorialPropertyB σ P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (hfm : g.f ≤ g.m)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f hnpos g.hfeven hfm P.epsB P.deltaF
      P.epsF) :
    Theorem51Obligation g P :=
  ⟨ExistsScrambleSeparator_of_combinatorial_and_bridge (pack := pack) hnpos hB hF hfm bridge⟩

theorem scrambleGeometry_f_le_m (g : ScrambleGeometry) : g.f ≤ g.m := by
  have := g.hshape
  omega

end Chvatal
