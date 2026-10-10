module
/- Combinatorial → matrix Properties B/F bridge (Chvátal §5–§6): matrix wire layout, column
sort, the sort–scramble–sort pack, and the semantic Properties B/F on it. -/

public import AKS.Chvatal.Lemma61
public import AKS.Bitonic.Shrink
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Order.Hom.Basic
public import AKS.Misc.Fin

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

/-! **Row scramble, column sort and the semantic sort–scramble–sort map** -/

/-- Wire permutation for the row-wise column scramble `σ` (the paper's middle stage; it needs no
comparators): row-preserving, sending `(r, j)` to `(r, σ r j)`. -/
def rowScrambleWirePerm (m n : Nat) (hn : 0 < n) (σ : Scramble m n) : Equiv.Perm (Fin (m * n)) where
  toFun w :=
    matrixWire m n (matrixRow m n hn w) (σ (matrixRow m n hn w) (matrixCol m n hn w))
  invFun w :=
    matrixWire m n (matrixRow m n hn w) ((σ (matrixRow m n hn w)).symm (matrixCol m n hn w))
  left_inv w := by
    simp only [(matrixWire_row_col hn _ _).1, (matrixWire_row_col hn _ _).2,
      Equiv.symm_apply_apply, matrixWire_matrixRow_col]
  right_inv w := by
    simp only [(matrixWire_row_col hn _ _).1, (matrixWire_row_col hn _ _).2,
      Equiv.apply_symm_apply, matrixWire_matrixRow_col]

theorem rowScrambleWirePerm_apply (m n : Nat) (hn : 0 < n) (σ : Scramble m n) (r : Fin m)
    (j : Fin n) : rowScrambleWirePerm m n hn σ (matrixWire m n r j) = matrixWire m n r (σ r j) := by
  simp [rowScrambleWirePerm, (matrixWire_row_col hn r j).1, (matrixWire_row_col hn r j).2]

theorem rowScrambleWirePerm_symm_apply (m n : Nat) (hn : 0 < n) (σ : Scramble m n) (r : Fin m)
    (j : Fin n) :
    (rowScrambleWirePerm m n hn σ).symm (matrixWire m n r j) = matrixWire m n r ((σ r).symm j) := by
  simp [rowScrambleWirePerm, (matrixWire_row_col hn r j).1, (matrixWire_row_col hn r j).2]

theorem matrixRow_rowScrambleWirePerm {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (w : Fin (m * n)) : matrixRow m n hn (rowScrambleWirePerm m n hn σ w) = matrixRow m n hn w := by
  simp [rowScrambleWirePerm, (matrixWire_row_col hn _ _).1]

theorem matrixRow_rowScrambleWirePerm_symm {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (w : Fin (m * n)) :
    matrixRow m n hn ((rowScrambleWirePerm m n hn σ).symm w) = matrixRow m n hn w := by
  simpa using (matrixRow_rowScrambleWirePerm hn σ ((rowScrambleWirePerm m n hn σ).symm w)).symm


/-- Comparators may only compare wires in a single column. -/
def ColumnLocalNetwork (m n : Nat) (net : ComparatorNetwork (m * n)) : Prop :=
  ∀ c ∈ net.comparators,
    ∃ j r k, c.i = matrixWire m n r j ∧ c.j = matrixWire m n k j

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

/-- Bitonic sorter on every column. -/
def columnSortNetwork (m n : Nat) (hn : 0 < n) : ComparatorNetwork (m * n) :=
  ⟨(List.finRange n).flatMap fun j : Fin n => (columnSortColumnNet m n hn j).comparators⟩

theorem columnSortNetwork_columnLocal (m n : Nat) (hn : 0 < n) :
    ColumnLocalNetwork m n (columnSortNetwork m n hn) := by
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

private theorem foldl_columnSortColumnNet {m n : Nat} (hn : 0 < n) {α : Type*} [LinearOrder α] :
    ∀ (cols : List (Fin n)), cols.Nodup → ∀ (v : Fin (m * n) → α) (r : Fin m) (j : Fin n),
      j ∈ cols →
      (cols.foldl (fun acc col => (columnSortColumnNet m n hn col).exec acc) v) (matrixWire m n r j) =
        (bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j) r := by
  intro cols
  induction cols with
  | nil => simp
  | cons c cs ih =>
    intro hnd v r j hj
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases hjc : j = c
    · subst hjc
      rw [columnSortColumnNet_foldl_outside_column hn cs j _ (fun col hcol h => hnd.1 (h ▸ hcol))
        _ (matrixWire_mem_columnWires hn r j)]
      have := ComparatorNetwork.scatterEmbed_exec_inside (bitonicNetwork m) (m * n)
        (columnWireEmbed m n hn j) v r
      rwa [columnWireEmbed_apply] at this
    · rw [ih hnd.2 _ r j ((List.mem_cons.mp hj).resolve_left hjc)]
      exact congrArg (fun u => (bitonicNetwork m).exec u r) (funext fun s =>
        columnSortColumnNet_exec_outside_column hn (Ne.symm hjc) v _
          (matrixWire_mem_columnWires hn s j))

theorem columnSortNetwork_exec_matrixWire {m n : Nat} (hn : 0 < n) (j : Fin n) {α : Type*}
    [LinearOrder α] (v : Fin (m * n) → α) (r : Fin m) :
    (columnSortNetwork m n hn).exec v (matrixWire m n r j) =
      (bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn j) r := by
  dsimp [columnSortNetwork]
  rw [ComparatorNetwork.exec_flatMap]
  exact foldl_columnSortColumnNet hn _ (List.nodup_finRange n) v r j (List.mem_finRange j)

/-- Values on wires are nondecreasing down each column (top row to bottom row). -/
def ColumnMonotoneInput (m n : Nat) (_hn : 0 < n) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) : Prop :=
  ∀ (j : Fin n) {r s : Fin m}, r ≤ s → v (matrixWire m n r j) ≤ v (matrixWire m n s j)

theorem columnSortNetwork_columnMonotone {m n : Nat} (hn : 0 < n) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) : ColumnMonotoneInput m n hn ((columnSortNetwork m n hn).exec v) :=
  fun j _ _ hrs => by
    rw [columnSortNetwork_exec_matrixWire, columnSortNetwork_exec_matrixWire]
    exact ((bitonicNetwork_sorts m) (v := v ∘ columnWireEmbed m n hn j)) hrs

/-- Column-monotone `Bool` inputs agreeing on every `matrixWire` cell are equal. -/
theorem ColumnMonotoneInput.eq_of_matrixWire_eq {m n : Nat} (hn : 0 < n)
    {f g : Fin (m * n) → Bool} (_hf : ColumnMonotoneInput m n hn f)
    (_hg : ColumnMonotoneInput m n hn g)
    (h : ∀ (r : Fin m) (j : Fin n), f (matrixWire m n r j) = g (matrixWire m n r j)) :
    f = g := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  exact h (matrixRow m n hn w) (matrixCol m n hn w)

/-- Key at or above the largest-`i·n` block (Chvátal matrix Property B threshold). -/
abbrev isAmongLargestKeysBlock {m n : Nat} (i : Nat) (key : Fin (m * n)) : Prop :=
  m * n - i * n ≤ key.val

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

/-- Per-column count of scrambled ones in rows strictly above the bottom `i` block. -/
def scrambledColSumInAboveBottomRows {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (j : Fin n) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
      r.val < m - i ∧ j ∈ scrambledRowOnes c σ r).card

theorem onesAboveBottom_le_scrambledColSumInAboveBottomRows {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) (j : Fin n) (him : i ≤ m) :
    scrambledColSum c σ j - i ≤ scrambledColSumInAboveBottomRows c σ i j := by
  classical
  have hbot : (Finset.univ.filter fun r : Fin m => m - i ≤ r.val).card = i := by
    rw [card_filter_val_ge m (m - i) (by omega)]; omega
  have hT : (Finset.univ.filter fun r : Fin m => j ∈ scrambledRowOnes c σ r) ⊆
      (Finset.univ.filter fun r : Fin m => r.val < m - i ∧ j ∈ scrambledRowOnes c σ r) ∪
        Finset.univ.filter fun r : Fin m => m - i ≤ r.val := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hr ⊢
    rcases lt_or_ge r.val (m - i) with h | h
    exacts [Or.inl ⟨h, hr⟩, Or.inr h]
  have h := (Finset.card_le_card hT).trans (Finset.card_union_le _ _)
  have hs : scrambledColSum c σ j =
      (Finset.univ.filter fun r : Fin m => j ∈ scrambledRowOnes c σ r).card := by
    unfold scrambledColSum
    rw [Finset.card_filter]
  unfold scrambledColSumInAboveBottomRows
  omega

/-- Final column sort after the wire relabeling of the middle stage (Chvátal §5 semantics). -/
def semanticExec {m n : Nat} (hn : 0 < n) (σ : Scramble m n) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  (columnSortNetwork m n hn).exec ((columnSortNetwork m n hn).exec v ∘
    (rowScrambleWirePerm m n hn σ).symm)

/-- Count of `true` wires in the above-bottom row region (no network applied). -/
def matrixOnesCountInRegion {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      (matrixRow m n hn w).val < m - i ∧ v w = true).card

/-- Top-`j` key threshold (Property F uses largest `j` keys, not `j·n`). -/
def largestKeyThresholdJ01 {m n : Nat} (j : Nat) (key : Fin (m * n)) : Bool :=
  decide (m * n - j ≤ key.val)

/-- Matrix Property B for the semantic sort–scramble–sort map (middle stage includes `wirePerm`). -/
def HasPackSemanticPropertyB {m n : Nat} (hn : 0 < n) (σ : Scramble m n) (epsB : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (i : Nat), 1 ≤ i → i ≤ m →
    (matrixOnesCountInRegion hn
        (semanticExec hn σ fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) i : ℝ) <
      (epsB / 2) * (m * n)

/-- Matrix Property F for the semantic sort–scramble–sort map. -/
def HasPackSemanticPropertyF {m n : Nat} (hn : 0 < n) (σ : Scramble m n) (f : Nat) (_hfm : f ≤ m)
    (deltaF epsF : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin (m * n))) (j : Nat), 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
    (matrixOnesCountInRegion hn
        (semanticExec hn σ fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) f : ℝ) <
      epsF * j

theorem mem_monotoneRowOnes_iff {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m)
    (j : Fin n) : j ∈ monotoneRowOnes c r ↔ (m - r.val) ≤ (c j).val := by
  simp [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem scrambleGeometry_f_le_m (g : ScrambleGeometry) : g.f ≤ g.m := by
  have := g.hshape
  omega

end Chvatal
