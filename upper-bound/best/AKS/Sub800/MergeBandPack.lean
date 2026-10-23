module
/-
  # Merge-first, band-repaired two-round separator (the sub-500 stage, UB-32 + UB-39)

  `mergeBandPack2Net` = column run merge (merge-first, runs of length `2^l`), then the scrambled second
  column sort, then the **band repair** (`columnSegmentRepairNetwork`: in every column, sort the row
  segments `[o, o + 2^b)`, `o ∈ offs`, centred on the output cuts) relabeled by the second scramble, in
  place of the third column sort. This is the stage of `experiments/sub500-screen/INDUCTION-v6.md`
  (merge-first 245 + sort 300 + band 171 at q = 24, b = 18).

  * Depth: run merge + one column sort + one bitonic sort of `2^b` wires (`mergeBandPack2Net_depth_le`).
  * On column-run-sorted inputs, the first two stages compute exactly `physicalPackNet` (sort,
    scramble, sort): `mergeBandPack2Net_exec_eq`. The third stage is the relabeled band repair, whose
    per-column behaviour is `columnSegmentRepair_exec_outside` / `columnSegmentRepair_seg`.
-/

public import AKS.Sub800.MergePack

@[expose] public section

namespace Chvatal

/-- Comparators of any column network join rows `r < r'` of one column. -/
theorem columnNet_comparator_rows {m n : ℕ} (hn : 0 < n) (N : ComparatorNetwork m)
    (c : Comparator (m * n)) (hc : c ∈ (columnNet hn N).comparators) :
    matrixRow m n hn c.i < matrixRow m n hn c.j := by
  obtain ⟨j, r, k, hi, hk⟩ := columnNet_columnLocal hn N c hc
  have hrk : r < k := (matrixWire_row_lt_iff hn j).mp (by rw [← hi, ← hk]; exact c.h)
  rw [hi, hk, (matrixWire_row_col hn r j).1, (matrixWire_row_col hn k j).1]
  exact hrk

theorem columnSegmentRepair_relabel2_lt {m n : ℕ} (hn : 0 < n) (b : ℕ) (offs : List ℕ)
    (σ1 σ2 : Scramble m n) (c : Comparator (m * n))
    (hc : c ∈ (columnSegmentRepairNetwork m n hn b offs).comparators) :
    (rowScrambleWirePerm2 m n hn σ1 σ2).symm c.i < (rowScrambleWirePerm2 m n hn σ1 σ2).symm c.j := by
  apply wire_lt_of_matrixRow_lt hn
  rw [matrixRow_rowScrambleWirePerm2_symm, matrixRow_rowScrambleWirePerm2_symm]
  exact columnNet_comparator_rows hn _ c hc

/-- The relabeled band repair (third stage). -/
def bandStage (m n : ℕ) (hn : 0 < n) (b : ℕ) (offs : List ℕ) (σ1 σ2 : Scramble m n) :
    ComparatorNetwork (m * n) :=
  relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSegmentRepairNetwork m n hn b offs)
    (columnSegmentRepair_relabel2_lt hn b offs σ1 σ2)

/-- Second stage of `physicalPackNet`: the column sort relabeled by the first scramble. -/
def sortStage (m n : ℕ) (hn : 0 < n) (σ1 : Scramble m n) : ComparatorNetwork (m * n) :=
  relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
    (columnSortNetwork_relabel_lt hn σ1)

/-- **Merge-first, band-repaired separator**: run merge, scrambled sort, scrambled band repair. -/
def mergeBandPack2Net (m n : ℕ) (hn : 0 < n) (l b : ℕ) (offs : List ℕ) (σ1 σ2 : Scramble m n) :
    ComparatorNetwork (m * n) :=
  ⟨(columnRunMergeNetwork m n hn l).comparators ++ (sortStage m n hn σ1).comparators ++
    (bandStage m n hn b offs σ1 σ2).comparators⟩

theorem exec_append' {N : ℕ} (a c : ComparatorNetwork N) {α : Type*} [LinearOrder α] (v : Fin N → α) :
    (a.append c).exec v = c.exec (a.exec v) :=
  ComparatorNetwork.exec_append a c v

theorem mergeBandPack2Net_eq (m n : ℕ) (hn : 0 < n) (l b : ℕ) (offs : List ℕ) (σ1 σ2 : Scramble m n) :
    mergeBandPack2Net m n hn l b offs σ1 σ2 =
      ((columnRunMergeNetwork m n hn l).append (sortStage m n hn σ1)).append
        (bandStage m n hn b offs σ1 σ2) := by
  unfold mergeBandPack2Net ComparatorNetwork.append
  simp [List.append_assoc]

/-- **Depth**: run merge + one column sort + one bitonic sort of `2^b` wires (disjoint segments). -/
theorem mergeBandPack2Net_depth_le (m n : ℕ) (hn : 0 < n) (l b : ℕ) {offs : List ℕ}
    (hd : Bitonic.SegDisjoint b offs) (σ1 σ2 : Scramble m n) :
    (mergeBandPack2Net m n hn l b offs σ1 σ2).depth ≤
      (columnRunMergeNetwork m n hn l).depth + (columnSortNetwork m n hn).depth +
        bitonicDepthBudget b := by
  have h3 : (sortStage m n hn σ1).depth = (columnSortNetwork m n hn).depth := relabelNet_depth _ _ _
  have h4 : (bandStage m n hn b offs σ1 σ2).depth = (columnSegmentRepairNetwork m n hn b offs).depth :=
    relabelNet_depth _ _ _
  have h5 := columnSegmentRepairNetwork_depth_le (m := m) hn b hd
  rw [mergeBandPack2Net_eq]
  calc _ ≤ ((columnRunMergeNetwork m n hn l).append (sortStage m n hn σ1)).depth +
        (bandStage m n hn b offs σ1 σ2).depth := ComparatorNetwork.depth_append_le _ _
    _ ≤ ((columnRunMergeNetwork m n hn l).depth + (sortStage m n hn σ1).depth) +
        (bandStage m n hn b offs σ1 σ2).depth :=
        Nat.add_le_add_right (ComparatorNetwork.depth_append_le _ _) _
    _ ≤ _ := by rw [h3, h4]; omega

/-- **On column-run-sorted inputs, the first two stages are the physical sort–scramble–sort**, so the
output is the band stage applied to `physicalPackNet`'s output. -/
theorem mergeBandPack2Net_exec_eq {m n : ℕ} (hn : 0 < n) (l b : ℕ) (offs : List ℕ)
    (σ1 σ2 : Scramble m n) {α : Type} [LinearOrder α] (v : Fin (m * n) → α)
    (hv : ColumnRunSorted m n hn l v) :
    (mergeBandPack2Net m n hn l b offs σ1 σ2).exec v =
      (bandStage m n hn b offs σ1 σ2).exec ((physicalPackNet m n hn σ1).exec v) := by
  have e2 : physicalPackNet m n hn σ1 =
      (columnSortNetwork m n hn).append (sortStage m n hn σ1) := rfl
  rw [mergeBandPack2Net_eq, e2, exec_append', exec_append', exec_append',
    columnRunMergeNetwork_exec_eq hn l v hv]

end Chvatal

end
