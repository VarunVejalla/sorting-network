module
/-
  # Column networks from any per-column network (UB-39)

  `columnNet N` runs the network `N : ComparatorNetwork m` on every column of the `m × n` matrix layout,
  exactly as `Chvatal.columnSortNetwork` does with `bitonicNetwork m`. The execution theorem is proved
  once for every `N`; `columnRunMergeNetwork` (merge of sorted runs of length `2^l`) is the instance used
  to replace the first column sort when every column of the node input consists of sorted runs.
-/

public import AKS.Chvatal.MatrixBridge
public import AKS.Bitonic.RunMerge
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

namespace Chvatal

/-- `N` embedded on column `j`. -/
def columnNetCol {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) (j : Fin n) :
    ComparatorNetwork (m * n) :=
  N.scatterEmbed (m * n) (columnWireEmbed m n hn j)

/-- `N` on every column. -/
def columnNet {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) : ComparatorNetwork (m * n) :=
  ⟨(List.finRange n).flatMap fun j : Fin n => (columnNetCol hn N j).comparators⟩

theorem columnNetCol_scatter_wire {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) (j : Fin n)
    (c : Comparator (m * n)) (hc : c ∈ (columnNetCol hn N j).comparators) :
    ∃ r k : Fin m, c.i = matrixWire m n r j ∧ c.j = matrixWire m n k j := by
  dsimp [columnNetCol, ComparatorNetwork.scatterEmbed] at hc
  rw [List.mem_map] at hc
  obtain ⟨d, _, heq⟩ := hc
  subst heq
  exact ⟨d.i, d.j, rfl, rfl⟩

theorem columnNetCol_not_in_other_column {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m)
    {j j' : Fin n} (hne : j ≠ j') (c : Comparator (m * n))
    (hc : c ∈ (columnNetCol hn N j').comparators) {w : Fin (m * n)}
    (hw : w ∈ columnWires m n hn j) : w ≠ c.i ∧ w ≠ c.j := by
  obtain ⟨r, k, hi, hk⟩ := columnNetCol_scatter_wire hn N j' c hc
  have hwcol : matrixCol m n hn w = j := (mem_columnWires (m := m) (n := n) hn j w).mp hw
  have hicol : matrixCol m n hn c.i = j' := by rw [hi, (matrixWire_row_col hn r j').2]
  have hkcol : matrixCol m n hn c.j = j' := by rw [hk, (matrixWire_row_col hn k j').2]
  exact ⟨fun heq => hne (by rw [← hwcol, heq, hicol]), fun heq => hne (by rw [← hwcol, heq, hkcol])⟩

theorem columnNetCol_foldl_outside_column {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m)
    (cols : List (Fin n)) (j : Fin n) {α : Type*} [LinearOrder α] (v : Fin (m * n) → α)
    (hdisj : ∀ col ∈ cols, col ≠ j) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    (cols.foldl (fun acc col => (columnNetCol hn N col).exec acc) v) w = v w :=
  ComparatorNetwork.foldl_exec_outside_set cols (columnNetCol hn N) v
    (columnWires m n hn j) (fun col hj' s hs c hc =>
      columnNetCol_not_in_other_column hn N (j := j) (j' := col)
        ((hdisj col hj').symm) c hc hs) w hw

theorem columnNetCol_exec_outside_column {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m)
    {j j' : Fin n} (hne : j' ≠ j) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    ((columnNetCol hn N j').exec v) w = v w := by
  unfold columnNetCol ComparatorNetwork.exec
  refine foldl_comparators_outside _ v w ?_
  intro c hc
  exact columnNetCol_not_in_other_column hn N (j := j) (j' := j') hne.symm c hc hw

theorem foldl_columnNetCol {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) {α : Type*}
    [LinearOrder α] :
    ∀ (cols : List (Fin n)), cols.Nodup → ∀ (v : Fin (m * n) → α) (r : Fin m) (j : Fin n),
      j ∈ cols →
      (cols.foldl (fun acc col => (columnNetCol hn N col).exec acc) v) (matrixWire m n r j) =
        N.exec (v ∘ columnWireEmbed m n hn j) r := by
  intro cols
  induction cols with
  | nil => simp
  | cons c cs ih =>
    intro hnd v r j hj
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases hjc : j = c
    · subst hjc
      rw [columnNetCol_foldl_outside_column hn N cs j _ (fun col hcol h => hnd.1 (h ▸ hcol))
        _ (matrixWire_mem_columnWires hn r j)]
      have := ComparatorNetwork.scatterEmbed_exec_inside N (m * n) (columnWireEmbed m n hn j) v r
      rwa [columnWireEmbed_apply] at this
    · rw [ih hnd.2 _ r j ((List.mem_cons.mp hj).resolve_left hjc)]
      exact congrArg (fun u => N.exec u r) (funext fun s =>
        columnNetCol_exec_outside_column hn N (Ne.symm hjc) v _
          (matrixWire_mem_columnWires hn s j))

/-- **Execution**: on column `j`, `columnNet N` acts as `N` on that column. -/
theorem columnNet_exec_matrixWire {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) (j : Fin n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) (r : Fin m) :
    (columnNet hn N).exec v (matrixWire m n r j) = N.exec (v ∘ columnWireEmbed m n hn j) r := by
  dsimp [columnNet]
  rw [ComparatorNetwork.exec_flatMap]
  exact foldl_columnNetCol hn N _ (List.nodup_finRange n) v r j (List.mem_finRange j)

theorem columnNet_columnLocal {m n : Nat} (hn : 0 < n) (N : ComparatorNetwork m) :
    ColumnLocalNetwork m n (columnNet hn N) := by
  intro c hc
  obtain ⟨j, _, hc'⟩ := List.mem_flatMap.mp hc
  obtain ⟨r, k, hi, hk⟩ := columnNetCol_scatter_wire hn N j c hc'
  exact ⟨j, r, k, hi, hk⟩

/-- Merge of sorted `2^l`-runs on every column. -/
def columnRunMergeNetwork (m n : Nat) (hn : 0 < n) (l : Nat) : ComparatorNetwork (m * n) :=
  columnNet hn (Bitonic.runMergeNetwork l m)

/-- Every column of `v` consists of sorted aligned runs of length `2^l` (top to bottom). -/
def ColumnRunSorted (m n : Nat) (hn : 0 < n) (l : Nat) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) : Prop :=
  ∀ j : Fin n, Bitonic.RunSorted l (v ∘ columnWireEmbed m n hn j)

/-- **The column run merge column-sorts every column-run-sorted input.** -/
theorem columnRunMergeNetwork_columnMonotone {m n : Nat} (hn : 0 < n) (l : Nat) {α : Type}
    [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnRunSorted m n hn l v) :
    ColumnMonotoneInput m n hn ((columnRunMergeNetwork m n hn l).exec v) :=
  fun j _ _ hrs => by
    unfold columnRunMergeNetwork
    rw [columnNet_exec_matrixWire, columnNet_exec_matrixWire]
    exact Bitonic.runMergeNetwork_sorts l m _ (hv j) hrs

theorem comparator_apply_comp_perm' {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : ∃ ρ : Equiv.Perm (Fin n), c.apply v = v ∘ ρ := by
  have hij := c.h.ne
  rcases le_total (v c.i) (v c.j) with h | h
  · refine ⟨1, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all
  · refine ⟨Equiv.swap c.i c.j, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

/-- A network's output is its input composed with a wire permutation (local copy of
`Chvatal.ComparatorNetwork.exec_eq_comp_perm`, to avoid importing `ExecPlacement`). -/
theorem exec_comp_perm' {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), net.exec v = v ∘ ρ := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
    obtain ⟨ρ₁, h₁⟩ := comparator_apply_comp_perm' c v
    obtain ⟨ρ₂, h₂⟩ := ih (c.apply v)
    exact ⟨ρ₁ * ρ₂, by
      show ComparatorNetwork.exec ⟨cs⟩ (c.apply v) = _
      rw [h₂, h₁]; rfl⟩

/-- Two networks that both sort `v` give the same output (outputs are sorted rearrangements of `v`). -/
theorem exec_eq_of_both_monotone {k : Nat} {α : Type*} [LinearOrder α] (A B : ComparatorNetwork k)
    (v : Fin k → α) (hA : Monotone (A.exec v)) (hB : Monotone (B.exec v)) : A.exec v = B.exec v := by
  obtain ⟨ρ, hρ⟩ := exec_comp_perm' A v
  obtain ⟨τ, hτ⟩ := exec_comp_perm' B v
  rw [hρ] at hA ⊢
  rw [hτ] at hB ⊢
  exact Tuple.unique_monotone hA hB

/-- **On column-run-sorted inputs the run merge and the full column sort agree**, so every
statement about `columnSortNetwork` as the first stage transfers to `columnRunMergeNetwork`. -/
theorem columnRunMergeNetwork_exec_eq {m n : Nat} (hn : 0 < n) (l : Nat) {α : Type}
    [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnRunSorted m n hn l v) :
    (columnRunMergeNetwork m n hn l).exec v = (columnSortNetwork m n hn).exec v := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  unfold columnRunMergeNetwork
  rw [columnNet_exec_matrixWire, columnSortNetwork_exec_matrixWire]
  exact congrFun (exec_eq_of_both_monotone (Bitonic.runMergeNetwork l m) (bitonicNetwork m)
    (v ∘ columnWireEmbed m n hn _) (Bitonic.runMergeNetwork_sorts l m _ (hv _))
    ((bitonicNetwork_sorts m) (v := v ∘ columnWireEmbed m n hn _))) _

end Chvatal

end
