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

/-! ### L3a at matrix level: the band stage moves `true`s up by at most the segment reach -/

open Finset in
/-- `true` wires at rows `≥ i`. -/
def rowCount {m n : ℕ} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : ℕ) : ℕ :=
  (univ.filter fun w : Fin (m * n) => i ≤ (matrixRow m n hn w).val ∧ v w = true).card

open Finset in
theorem rowCount_comp_perm {m n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin (m * n)))
    (hπ : ∀ w, matrixRow m n hn (π w) = matrixRow m n hn w) (x : Fin (m * n) → Bool) (i : ℕ) :
    rowCount hn (x ∘ π) i = rowCount hn x i := by
  unfold rowCount
  refine Finset.card_bij (fun w _ => π w) ?_ (fun a _ b _ h => π.injective h) ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hw ⊢
    rw [hπ]; exact hw
  · intro w hw
    refine ⟨π.symm w, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, Equiv.apply_symm_apply] at hw ⊢
    have := hπ (π.symm w)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]; exact hw

open Finset in
theorem rowCount_eq_sum_columns {m n : ℕ} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : ℕ) :
    rowCount hn v i = ∑ j : Fin n,
      Bitonic.cntT (univ.filter fun r : Fin m => i ≤ r.val) (v ∘ columnWireEmbed m n hn j) := by
  unfold rowCount
  rw [Finset.card_eq_sum_card_fiberwise (f := matrixCol m n hn) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Bitonic.cntT
  refine (Finset.card_bij (fun r _ => matrixWire m n r j) ?_ ?_ ?_).symm
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, columnWireEmbed_apply] at hr ⊢
    rw [(matrixWire_row_col hn r j).1, (matrixWire_row_col hn r j).2]
    exact ⟨hr, rfl⟩
  · intro a _ c _ h
    exact (matrixWire_injective hn h).1
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨⟨hr, hv⟩, rfl⟩ := hw
    refine ⟨matrixRow m n hn w, ?_, matrixWire_matrixRow_col hn w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, columnWireEmbed_apply]
    refine ⟨hr, ?_⟩
    rw [matrixWire_matrixRow_col]; exact hv

/-- **L3a (matrix level).** If every band segment reaching rows `≥ i` starts at row `≥ h` (`h ≤ i`), the
band stage's output has at most as many `true`s at rows `≥ i` as its input has at rows `≥ h`. With the
input's column counts `c'` after the second sort, the right side is `Σ_k (c'_k − h)₊`
(PROOFS-L3-L4.md, row identity). -/
theorem bandStage_rowCount_le {m n : ℕ} (hn : 0 < n) (b : ℕ) {offs : List ℕ}
    (hd : Bitonic.SegDisjoint b offs) (hfit : ∀ o ∈ offs, o + 2 ^ b ≤ m) (σ1 σ2 : Scramble m n)
    {h i : ℕ} (hhi : h ≤ i) (hseg : ∀ o ∈ offs, i < o + 2 ^ b → h ≤ o) (x : Fin (m * n) → Bool) :
    rowCount hn ((bandStage m n hn b offs σ1 σ2).exec x) i ≤ rowCount hn x h := by
  set P := rowScrambleWirePerm2 m n hn σ1 σ2
  have hP : ∀ w, matrixRow m n hn (P w) = matrixRow m n hn w := matrixRow_rowScrambleWirePerm2 hn σ1 σ2
  have hPs : ∀ w, matrixRow m n hn (P.symm w) = matrixRow m n hn w :=
    matrixRow_rowScrambleWirePerm2_symm hn σ1 σ2
  unfold bandStage
  rw [relabelNet_exec]
  have e1 : (fun w => (columnSegmentRepairNetwork m n hn b offs).exec (x ∘ P.symm) (P.symm.symm w)) =
      ((columnSegmentRepairNetwork m n hn b offs).exec (x ∘ P.symm)) ∘ P := by
    funext w; simp
  rw [e1, rowCount_comp_perm hn P hP, ← rowCount_comp_perm hn P.symm hPs x h,
    rowCount_eq_sum_columns, rowCount_eq_sum_columns]
  refine Finset.sum_le_sum fun j _ => ?_
  have ecol : (columnSegmentRepairNetwork m n hn b offs).exec (x ∘ P.symm) ∘ columnWireEmbed m n hn j =
      (Bitonic.segmentSort m b offs).exec ((x ∘ P.symm) ∘ columnWireEmbed m n hn j) := by
    funext r
    simp only [Function.comp, columnWireEmbed_apply]
    unfold columnSegmentRepairNetwork
    rw [columnNet_exec_matrixWire]
  rw [ecol]
  exact Bitonic.segmentSort_cnt_rows_le hd hfit hhi hseg _

end Chvatal

end
