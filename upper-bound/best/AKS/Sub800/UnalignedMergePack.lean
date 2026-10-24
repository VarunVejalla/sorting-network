module
/-
  # Merge-first two-round separator for unaligned sorted runs (UB-43)

  `uMergePack2Net` is `physicalPack2Net` with its first column sort replaced by the column
  unaligned run merge `columnURunMergeNetwork` (`Bitonic.uRunMergeNetwork` on every column). On every
  input whose columns are sorted runs with descents at least `R` apart (`ColumnDescentsApart`, run
  boundaries arbitrary), `2^s ≤ R + 1`, it computes exactly what `physicalPack2Net` computes, so every
  Property B / F statement proved for the physical pack transfers to such inputs
  (`uMergePack2Net_exec_eq`). This is the unaligned analogue of `MergePack.mergePack2Net_exec_eq`.

  Depth at `≤ 2^25` rows and runs of length `≥ 2047` (`s = 11`, e.g. the F blocks of `f + 1 ≥ 3330`
  rows): the first stage has depth `≤ 21 + (325 - 66) = 280`, the separator `≤ 280 + 2·325 = 930`
  (`uMergePack2Net_depth_le_930`), against `975` for `physicalPack2Net`.
-/

public import AKS.Sub800.MergePack
public import AKS.Bitonic.UnalignedRunMerge
public import AKS.Chvatal.SeparatorDepth

@[expose] public section

namespace Chvatal

/-- The unaligned run merge (two-run block sorts, then the run merge) on every column. -/
def columnURunMergeNetwork (m n : Nat) (hn : 0 < n) (s : Nat) : ComparatorNetwork (m * n) :=
  columnNet hn (Bitonic.uRunMergeNetwork s m)

/-- Every column of `v` (top to bottom) is a concatenation of sorted runs whose descents are at least
`R` apart; the run boundaries are arbitrary. -/
def ColumnDescentsApart (m n : Nat) (hn : 0 < n) (R : Nat) {α : Type} [LinearOrder α]
    (v : Fin (m * n) → α) : Prop :=
  ∀ j : Fin n, Bitonic.DescentsApart R (v ∘ columnWireEmbed m n hn j)

/-- **The column unaligned run merge column-sorts every column-descents-apart input.** -/
theorem columnURunMergeNetwork_columnMonotone {m n : Nat} (hn : 0 < n) {s R : Nat}
    (hR : 2 ^ s ≤ R + 1) {α : Type} [LinearOrder α] (v : Fin (m * n) → α)
    (hv : ColumnDescentsApart m n hn R v) :
    ColumnMonotoneInput m n hn ((columnURunMergeNetwork m n hn s).exec v) :=
  fun j _ _ hrs => by
    unfold columnURunMergeNetwork
    rw [columnNet_exec_matrixWire, columnNet_exec_matrixWire]
    exact Bitonic.uRunMergeNetwork_sorts_of_descentsApart hR m _ (hv j) hrs

/-- **On column-descents-apart inputs the unaligned run merge and the full column sort agree.** -/
theorem columnURunMergeNetwork_exec_eq {m n : Nat} (hn : 0 < n) {s R : Nat} (hR : 2 ^ s ≤ R + 1)
    {α : Type} [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnDescentsApart m n hn R v) :
    (columnURunMergeNetwork m n hn s).exec v = (columnSortNetwork m n hn).exec v := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  unfold columnURunMergeNetwork
  rw [columnNet_exec_matrixWire, columnSortNetwork_exec_matrixWire]
  exact congrFun (exec_eq_of_both_monotone (Bitonic.uRunMergeNetwork s m) (bitonicNetwork m)
    (v ∘ columnWireEmbed m n hn _) (Bitonic.uRunMergeNetwork_sorts_of_descentsApart hR m _ (hv _))
    ((bitonicNetwork_sorts m) (v := v ∘ columnWireEmbed m n hn _))) _

theorem columnURunMergeNetwork_depth_le {m n : Nat} (hn : 0 < n) (s : Nat) :
    (columnURunMergeNetwork m n hn (s + 1)).depth + bitonicDepthBudget (s + 1) ≤
      2 * s + 1 + bitonicDepthBudget (s + 1 + (Nat.clog 2 m - (s + 1))) :=
  (Nat.add_le_add_right (columnNet_depth_le hn _) _).trans (Bitonic.uRunMergeNetwork_depth_le s m)

/-- Merge-first two-round separator for unaligned runs: column unaligned run merge, then the two
later stages of `physicalPack2Net`. -/
def uMergePack2Net (m n : ℕ) (hn : 0 < n) (s : ℕ) (σ1 σ2 : Scramble m n) :
    ComparatorNetwork (m * n) :=
  ⟨(columnURunMergeNetwork m n hn s).comparators ++ (pack2Rest m n hn σ1 σ2).comparators⟩

/-- **On column-descents-apart inputs the unaligned merge-first separator equals the physical
two-round separator.** -/
theorem uMergePack2Net_exec_eq {m n : ℕ} (hn : 0 < n) {s R : ℕ} (hR : 2 ^ s ≤ R + 1)
    (σ1 σ2 : Scramble m n) {α : Type} [LinearOrder α] (v : Fin (m * n) → α)
    (hv : ColumnDescentsApart m n hn R v) :
    (uMergePack2Net m n hn s σ1 σ2).exec v = (physicalPack2Net m n hn σ1 σ2).exec v := by
  rw [physicalPack2Net_eq_append, uMergePack2Net, ComparatorNetwork.exec_append,
    ComparatorNetwork.exec_append, columnURunMergeNetwork_exec_eq hn hR v hv]

theorem uMergePack2Net_depth_le (m n : ℕ) (hn : 0 < n) (s : ℕ) (σ1 σ2 : Scramble m n) :
    (uMergePack2Net m n hn s σ1 σ2).depth ≤
      (columnURunMergeNetwork m n hn s).depth + 2 * (columnSortNetwork m n hn).depth := by
  have h := ComparatorNetwork.depth_append_le (columnURunMergeNetwork m n hn s)
    (pack2Rest m n hn σ1 σ2)
  unfold uMergePack2Net
  exact h.trans (Nat.add_le_add_left (pack2Rest_depth_le m n hn σ1 σ2) _)

/-- **First stage at `≤ 2^25` rows, block length `2^11`: depth `≤ 21 + 325 - 66 = 280`.** -/
theorem columnURunMergeNetwork_depth_le_280 {m n : ℕ} (hn : 0 < n) (hm : m ≤ 2 ^ 25) :
    (columnURunMergeNetwork m n hn 11).depth ≤ 280 := by
  show (columnURunMergeNetwork m n hn (10 + 1)).depth ≤ 280
  have h := columnURunMergeNetwork_depth_le (m := m) hn 10
  have hc : Nat.clog 2 m ≤ 25 := Nat.clog_le_of_le_pow hm
  have hmono : bitonicDepthBudget (10 + 1 + (Nat.clog 2 m - (10 + 1))) ≤ bitonicDepthBudget 25 :=
    bitonicDepthBudget_mono (by omega)
  have h25 : bitonicDepthBudget 25 = 325 := by rw [bitonicDepthBudget_eq]
  have h11 : bitonicDepthBudget (10 + 1) = 66 := by rw [bitonicDepthBudget_eq]
  omega

/-- **The unaligned merge-first separator at `≤ 2^25` rows, runs of length `≥ 2047`: depth
`≤ 930`** (versus `3 · 325 = 975` for the physical two-round separator). -/
theorem uMergePack2Net_depth_le_930 {m n : ℕ} (hn : 0 < n) (hm : m ≤ 2 ^ 25)
    (σ1 σ2 : Scramble m n) : (uMergePack2Net m n hn 11 σ1 σ2).depth ≤ 930 := by
  have h1 := uMergePack2Net_depth_le m n hn 11 σ1 σ2
  have h2 := columnURunMergeNetwork_depth_le_280 hn hm
  have h3 := columnSortNetwork_depth_le_budget m n hn
  have hc : Nat.clog 2 m ≤ 25 := Nat.clog_le_of_le_pow hm
  have hmono : bitonicDepthBudget (Nat.clog 2 m) ≤ bitonicDepthBudget 25 :=
    bitonicDepthBudget_mono hc
  have h25 : bitonicDepthBudget 25 = 325 := by rw [bitonicDepthBudget_eq]
  omega

/-- The exact semantic statement used downstream: for runs of length `≥ 3330` (descents `3330`
apart, as for the child F blocks of `f + 1 > 3329` rows) at `≤ 2^25` rows, the depth-`930`
separator computes `physicalPack2Net`. -/
theorem uMergePack2Net_exec_eq_3330 {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n) {α : Type}
    [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnDescentsApart m n hn 3330 v) :
    (uMergePack2Net m n hn 11 σ1 σ2).exec v = (physicalPack2Net m n hn σ1 σ2).exec v :=
  uMergePack2Net_exec_eq hn (by norm_num) σ1 σ2 v hv

end Chvatal

end
