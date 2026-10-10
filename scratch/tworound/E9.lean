import AKS.Chvatal.PackSpec2
namespace Chvatal

/-- Column sort fixes a column-monotone matrix. -/
theorem columnSort_exec_of_columnMonotone {m n : Nat} (hn : 0 < n) {α : Type} [LinearOrder α]
    (u : Fin (m * n) → α) (hu : ColumnMonotoneInput m n hn u) :
    (columnSortNetwork m n hn).exec u = u := by
  funext w
  rw [← matrixWire_matrixRow_col hn w, columnSortNetwork_exec_matrixWire,
    (bitonicNetwork m).exec_eq_of_monotone (fun r s hrs => by
      simpa [columnWireEmbed_apply] using hu (matrixCol m n hn w) hrs)]
  simp [columnWireEmbed_apply]

/-- **Bridge.** `semanticExec2 σ1 σ2 = semanticExec σ2 ∘ semanticExec σ1`: the leading column
sort of the second round acts on an already column-sorted matrix. -/
theorem semanticExec2_eq_comp {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n) {α : Type}
    [LinearOrder α] (v : Fin (m * n) → α) :
    semanticExec2 hn σ1 σ2 v = semanticExec hn σ2 (semanticExec hn σ1 v) := by
  unfold semanticExec2
  show _ = (columnSortNetwork m n hn).exec ((columnSortNetwork m n hn).exec (semanticExec hn σ1 v) ∘ _)
  have h : (columnSortNetwork m n hn).exec (semanticExec hn σ1 v) = semanticExec hn σ1 v :=
    columnSort_exec_of_columnMonotone hn _ (columnSortNetwork_columnMonotone hn _)
  rw [h]

end Chvatal
