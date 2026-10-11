module
/-
  Column-monotone `Bool` decode: above-bottom counts are `∑ⱼ (colSumⱼ - i)₊`. For the concrete
  `semanticExec` (column sort, row scramble, column sort), the region count of any Boolean marking
  equals the combinatorial `onesAboveBottom` of its post-first-sort column sums; this gives matrix
  Property B from the pipeline combinatorial Property B, and is the decode step of Property F.
-/

public import AKS.Chvatal.MatrixBridge
public import AKS.Misc.Fin

@[expose] public section

namespace Chvatal

open Finset

/-- Wires as `(row, column)` pairs. -/
def matrixWireEquiv {m n : Nat} (hn : 0 < n) : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := matrixWire m n p.1 p.2
  invFun w := (matrixRow m n hn w, matrixCol m n hn w)
  left_inv p := Prod.ext (matrixWire_row_col hn _ _).1 (matrixWire_row_col hn _ _).2
  right_inv w := matrixWire_matrixRow_col hn w

theorem sum_matrixWire {m n : Nat} (hn : 0 < n) {M : Type*} [AddCommMonoid M]
    (f : Fin (m * n) → M) : ∑ w, f w = ∑ j : Fin n, ∑ r : Fin m, f (matrixWire m n r j) := by
  rw [← (matrixWireEquiv hn).sum_comp, Fintype.sum_prod_type_right]; rfl

/-- Number of `true` wires in column `j`. -/
def matrixColumnTrueCount {m n : Nat} (j : Fin n) (v : Fin (m * n) → Bool) : Nat :=
  (univ.filter fun r : Fin m => v (matrixWire m n r j) = true).card

private theorem matrixColumnTrueCount_eq_sum {m n : Nat} (j : Fin n) (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount j v = ∑ r : Fin m, if v (matrixWire m n r j) = true then 1 else 0 := by
  rw [matrixColumnTrueCount, card_filter]

theorem matrixColumnTrueCount_le {m n : Nat} (j : Fin n) (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount j v ≤ m :=
  (card_filter_le _ _).trans (by simp)

/-- In a column-monotone `Bool` matrix, row `r` of column `j` is `true` iff `r ≥ m - colSum j`. -/
theorem colMono_true_iff {m n : Nat} (hn : 0 < n) {v : Fin (m * n) → Bool}
    (hcm : ColumnMonotoneInput m n hn v) (r : Fin m) (j : Fin n) :
    v (matrixWire m n r j) = true ↔ m - r.val ≤ matrixColumnTrueCount j v := by
  have hr := r.isLt
  unfold matrixColumnTrueCount
  constructor
  · intro h
    have hsub : Ici r ⊆ univ.filter fun s => v (matrixWire m n s j) = true := fun s hs => by
      simpa using Bool.le_iff_imp.mp (hcm j (mem_Ici.mp hs)) h
    simpa using card_le_card hsub
  · intro h
    by_contra hf
    have hsub : (univ.filter fun s => v (matrixWire m n s j) = true) ⊆ Ioi r := fun s hs => by
      by_contra hs'
      exact hf (Bool.le_iff_imp.mp (hcm j (not_lt.mp (mem_Ioi.not.mp hs'))) (mem_filter.mp hs).2)
    have := card_le_card hsub
    simp at this
    omega

private theorem card_filter_Ico (m a b : Nat) :
    (univ.filter fun r : Fin m => a ≤ r.val ∧ r.val < b).card = min b m - a := by
  rw [← Nat.card_Ico, ← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
  constructor
  · rintro ⟨r, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, lt_min h2 r.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2.trans_le (min_le_right _ _)⟩, ⟨h1, h2.trans_le (min_le_left _ _)⟩, rfl⟩

private theorem swap_matrixWire_row {m n : Nat} (hn : 0 < n) (j : Fin n) (r s t : Fin m) :
    Equiv.swap (matrixWire m n r j) (matrixWire m n s j) (matrixWire m n t j) =
      matrixWire m n (Equiv.swap r s t) j := by
  by_cases ht : t = r
  · subst ht; simp [Equiv.swap_apply_left]
  · by_cases ht' : t = s
    · subst ht'; simp [Equiv.swap_apply_right]
    · simp [Equiv.swap_apply_of_ne_of_ne ht ht',
        Equiv.swap_apply_of_ne_of_ne (fun h => ht (matrixWire_injective hn h).1)
          (fun h => ht' (matrixWire_injective hn h).1)]

/-- One column-local comparator preserves the true-count in every column. -/
private theorem matrixColumnTrueCount_apply_eq {m n : Nat} (hn : 0 < n) (j : Fin n)
    (c : Comparator (m * n))
    (hcol : ∃ j' r s, c.i = matrixWire m n r j' ∧ c.j = matrixWire m n s j')
    (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount j (c.apply v) = matrixColumnTrueCount j v := by
  obtain ⟨j', r, s, hi, hj⟩ := hcol
  by_cases hle : v c.i ≤ v c.j
  · rw [Comparator.apply_eq_of_le c v hle]
  · have hsw := Comparator.apply_eq_swap c v (not_le.mp hle)
    simp only [matrixColumnTrueCount_eq_sum, hsw]
    by_cases hjj : j' = j
    · subst hjj
      simp only [hi, hj, swap_matrixWire_row hn]
      exact Equiv.sum_comp (Equiv.swap r s) fun t => if v (matrixWire m n t j') = true then 1 else 0
    · refine sum_congr rfl fun t _ => ?_
      rw [Equiv.swap_apply_of_ne_of_ne (by rw [hi]; exact fun h => hjj (matrixWire_injective hn h).2.symm)
        (by rw [hj]; exact fun h => hjj (matrixWire_injective hn h).2.symm)]

/-- Column-local networks preserve per-column true counts. -/
theorem matrixColumnTrueCount_exec_eq {m n : Nat} (hn : 0 < n) (j : Fin n)
    (net : ComparatorNetwork (m * n)) (hcol : ColumnLocalNetwork m n net)
    (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount j (net.exec v) = matrixColumnTrueCount j v := by
  rcases net with ⟨cs⟩
  induction cs generalizing v with
  | nil => simp [ComparatorNetwork.exec]
  | cons c cs ih =>
    have htail : ColumnLocalNetwork m n ⟨cs⟩ := fun c' hc' =>
      hcol c' (List.mem_cons_of_mem c hc')
    exact (ih (c.apply v) htail).trans
      (matrixColumnTrueCount_apply_eq hn j c (hcol c List.mem_cons_self) v)

/-- After column sort, the region count equals `∑ⱼ (colSumⱼ - i)`. -/
theorem matrixOnesCountInRegion_colSort_eq_sum_columnSub {m n : Nat} (hn : 0 < n) (i : Nat)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn ((columnSortNetwork m n hn).exec v) i =
      ∑ j : Fin n, (matrixColumnTrueCount j v - i) := by
  set u := (columnSortNetwork m n hn).exec v
  have hcm : ColumnMonotoneInput m n hn u := columnSortNetwork_columnMonotone hn v
  rw [matrixOnesCountInRegion, card_filter, sum_matrixWire hn]
  refine sum_congr rfl fun j _ => ?_
  have hcnt : matrixColumnTrueCount j u = matrixColumnTrueCount j v :=
    matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn) v
  have h1 := matrixColumnTrueCount_le j v
  rw [← card_filter]
  simp only [(matrixWire_row_col hn _ _).1]
  rw [show (univ.filter fun r : Fin m => r.val < m - i ∧ u (matrixWire m n r j) = true) =
      univ.filter fun r : Fin m => m - matrixColumnTrueCount j u ≤ r.val ∧ r.val < m - i by
    ext r
    have := r.isLt
    have := matrixColumnTrueCount_le j u
    simp only [mem_filter, mem_univ, true_and, colMono_true_iff hn hcm]
    omega, card_filter_Ico, hcnt]
  omega

/-- Column sums of a Boolean matrix, as a `MonotoneColumnSums` witness. -/
def monotoneColumnSumsOfBool {m n : Nat} (v : Fin (m * n) → Bool) : MonotoneColumnSums m n :=
  fun j => ⟨matrixColumnTrueCount j v, Nat.lt_succ_of_le (matrixColumnTrueCount_le j v)⟩

theorem monotoneMatrixBool_eq_of_columnMonotone {m n : Nat} (hn : 0 < n)
    (v : Fin (m * n) → Bool) (hcm : ColumnMonotoneInput m n hn v) :
    v = monotoneMatrixBool hn (monotoneColumnSumsOfBool v) := by
  funext w
  rw [← matrixWire_matrixRow_col hn w, Bool.eq_iff_iff, monotoneMatrixBool_matrixWire,
    mem_monotoneRowOnes_iff, colMono_true_iff hn hcm]
  rfl

theorem scrambledColSum_eq_matrixColumnTrueCount {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (c : MonotoneColumnSums m n) (j : Fin n) :
    scrambledColSum c σ j =
      matrixColumnTrueCount j (monotoneMatrixBool hn c ∘ (rowScrambleWirePerm m n hn σ).symm) := by
  classical
  unfold scrambledColSum
  rw [matrixColumnTrueCount_eq_sum]
  refine sum_congr rfl fun r _ => ?_
  have h : (monotoneMatrixBool hn c ∘ (rowScrambleWirePerm m n hn σ).symm) (matrixWire m n r j) =
      true ↔ j ∈ scrambledRowOnes c σ r := by
    simp only [Function.comp, rowScrambleWirePerm_symm_apply,
      monotoneMatrixBool_matrixWire, scrambledRowOnes, mem_image]
    exact ⟨fun hj => ⟨_, hj, Equiv.apply_symm_apply _ _⟩, fun ⟨j0, hj0, e⟩ => by
      simpa [← e] using hj0⟩
  simp only [h]

/-- After the semantic map on a Boolean marking, the region count at level `i ≤ m` is the
combinatorial `onesAboveBottom` of the post-first-sort column sums (Property B and F decode). -/
theorem matrixOnesCountInRegion_semanticExec {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (v : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (semanticExec hn σ v) i =
      onesAboveBottom (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec v)) σ i := by
  set c := monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec v)
  have hu1 : (columnSortNetwork m n hn).exec v = monotoneMatrixBool hn c :=
    monotoneMatrixBool_eq_of_columnMonotone hn _ (columnSortNetwork_columnMonotone hn v)
  rw [semanticExec, matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i]
  refine sum_congr rfl fun j _ => ?_
  rw [scrambledColSum_eq_matrixColumnTrueCount hn σ c j, hu1]

/-- A permutation maps the `j` largest keys' wires to a set of `j` wires. -/
private theorem topJMarking_trueWireCount_eq {m n : Nat} (j : Nat) (hjmn : j ≤ m * n)
    (v : Equiv.Perm (Fin (m * n))) :
    (univ.filter fun w : Fin (m * n) =>
        largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true).card = j := by
  rw [card_equiv v (t := univ.filter fun k : Fin (m * n) => m * n - j ≤ k.val)
    (by simp [largestKeyThresholdJ01]), card_filter_val_ge _ _ (Nat.sub_le _ _)]
  omega

theorem totalColumnOnes_colSort_exec_eq {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) :
    totalColumnOnes (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec v)) =
      (univ.filter fun w : Fin (m * n) => v w = true).card := by
  rw [card_filter, sum_matrixWire hn]
  refine sum_congr rfl fun j _ => ?_
  rw [← matrixColumnTrueCount_eq_sum]
  exact matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn) v

theorem HasPackSemanticPropertyB.of_combinatorial_onPipeline {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (σ : Scramble m n) (hComb : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasPackSemanticPropertyB hn σ epsB := fun v i hi1 him => by
  rw [matrixOnesCountInRegion_semanticExec]
  refine hComb _ i ?_ hi1 him
  rw [totalColumnOnes_colSort_exec_eq, topJMarking_trueWireCount_eq (i * n)
    (Nat.mul_le_mul_right n him) v, Nat.mul_comm]

theorem sum_topJ_colSums_eq_j {m n : Nat} (hn : 0 < n) (v : Equiv.Perm (Fin (m * n))) (j : Nat)
    (hjmn : j ≤ m * n) :
    totalColumnOnes (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec
        fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))) = j := by
  rw [totalColumnOnes_colSort_exec_eq]
  exact topJMarking_trueWireCount_eq j hjmn v

end Chvatal
