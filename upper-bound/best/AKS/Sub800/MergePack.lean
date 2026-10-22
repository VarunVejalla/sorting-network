module
/-
  # Merge-first two-round separator (UB-39)

  `mergePack2Net` is `physicalPack2Net` with its first column sort replaced by the column run merge
  (`columnRunMergeNetwork`, sorted runs of length `2^l`). On every column-run-sorted input it computes
  exactly what `physicalPack2Net` computes, so every Property B / F statement proved for the physical
  pack transfers to such inputs. Depth: the run merge saves `bitonicDepthBudget l` levels of the first
  sort (`columnRunMergeNetwork_depth_le`).
-/

public import AKS.Sub800.ColumnNet
public import AKS.Chvatal.PhysicalPack2

@[expose] public section

namespace Chvatal

/-- The two later stages of `physicalPack2Net`: the relabeled second and third column sorts. -/
def pack2Rest (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) : ComparatorNetwork (m * n) :=
  ⟨(relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ1)).comparators ++
    (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel2_lt hn σ1 σ2)).comparators⟩

theorem physicalPack2Net_eq_append (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    physicalPack2Net m n hn σ1 σ2 =
      ⟨(columnSortNetwork m n hn).comparators ++ (pack2Rest m n hn σ1 σ2).comparators⟩ := by
  unfold physicalPack2Net pack2Rest
  simp [List.append_assoc]

/-- Merge-first two-round separator: run merge, then the two later stages of `physicalPack2Net`. -/
def mergePack2Net (m n : ℕ) (hn : 0 < n) (l : ℕ) (σ1 σ2 : Scramble m n) : ComparatorNetwork (m * n) :=
  ⟨(columnRunMergeNetwork m n hn l).comparators ++ (pack2Rest m n hn σ1 σ2).comparators⟩

/-- **On column-run-sorted inputs the merge-first separator equals the physical two-round separator.** -/
theorem mergePack2Net_exec_eq {m n : ℕ} (hn : 0 < n) (l : ℕ) (σ1 σ2 : Scramble m n) {α : Type}
    [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnRunSorted m n hn l v) :
    (mergePack2Net m n hn l σ1 σ2).exec v = (physicalPack2Net m n hn σ1 σ2).exec v := by
  rw [physicalPack2Net_eq_append, mergePack2Net, ComparatorNetwork.exec_append,
    ComparatorNetwork.exec_append, columnRunMergeNetwork_exec_eq hn l v hv]

theorem pack2Rest_depth_le (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    (pack2Rest m n hn σ1 σ2).depth ≤ 2 * (columnSortNetwork m n hn).depth := by
  have h := ComparatorNetwork.depth_append_le
    (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ1))
    (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel2_lt hn σ1 σ2))
  rw [relabelNet_depth, relabelNet_depth] at h
  unfold pack2Rest
  exact h.trans (by omega)

/-- Depth of the merge-first separator: run merge plus two column sorts. -/
theorem mergePack2Net_depth_le (m n : ℕ) (hn : 0 < n) (l : ℕ) (σ1 σ2 : Scramble m n) :
    (mergePack2Net m n hn l σ1 σ2).depth ≤
      (columnRunMergeNetwork m n hn l).depth + 2 * (columnSortNetwork m n hn).depth := by
  have h := ComparatorNetwork.depth_append_le (columnRunMergeNetwork m n hn l) (pack2Rest m n hn σ1 σ2)
  unfold mergePack2Net
  exact h.trans (Nat.add_le_add_left (pack2Rest_depth_le m n hn σ1 σ2) _)

end Chvatal

end
