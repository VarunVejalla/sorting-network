module
/- The row scramble as a fixed wire permutation (Chvátal §5 middle stage; no comparators). -/

public import AKS.Chvatal.MatrixBridge
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Chvatal

/-- Wire permutation for row-wise column scramble `σ` (row-major matrix layout). -/
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
    (j : Fin n) :
    rowScrambleWirePerm m n hn σ (matrixWire m n r j) = matrixWire m n r (σ r j) := by
  dsimp [rowScrambleWirePerm]
  rw [(matrixWire_row_col hn r j).1, (matrixWire_row_col hn r j).2]

/-- Full matrix row-scramble witness for scramble `σ`: a wire relabeling with no comparators. -/
def rowScrambleNetwork (m n : Nat) (hn : 0 < n) (σ : Scramble m n) : RowScrambleNetwork m n σ where
  net := ⟨[]⟩
  wirePerm := rowScrambleWirePerm m n hn σ
  perm_on_matrixWire := rowScrambleWirePerm_apply m n hn σ
  comparators_eq_nil := rfl

theorem rowScrambleNetwork_comparators_eq_nil (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    (rowScrambleNetwork m n hn σ).net.comparators = [] := rfl

theorem RowScrambleCorrect.of_rowScrambleNetwork {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ)
    (hcol : IdealColumnSort m n hn colSort) :
    RowScrambleCorrect m n hn σ colSort rowScramble := by
  refine ⟨fun c r j => ?_⟩
  let v := monotoneMatrixBool (m := m) (n := n) hn c
  have hcol' : colSort.net.exec v = v :=
    IdealColumnSort.exec_eq_of_columnMonotoneInput hn colSort hcol v
      (ColumnMonotoneInput_monotoneMatrixBool hn c)
  have hwire :
      rowScramble.wirePerm.symm (matrixWire m n r j) =
        matrixWire m n r ((σ r).symm j) := by
    apply rowScramble.wirePerm.injective
    rw [Equiv.apply_symm_apply, rowScramble.perm_on_matrixWire r ((σ r).symm j)]
    simp
  have hmid :
      sortScrambleMiddleExec colSort rowScramble v (matrixWire m n r j) =
        v (matrixWire m n r ((σ r).symm j)) := by
    rw [sortScrambleMiddleExec, rowScramble.wiredExec_eq_perm_of_nil rowScramble.comparators_eq_nil]
    show colSort.net.exec v (rowScramble.wirePerm.symm _) = _
    rw [hcol', hwire]
  rw [hmid, monotoneMatrixBool_matrixWire]
  constructor
  · intro hj
    exact Finset.mem_image.mpr ⟨(σ r).symm j, hj, Equiv.apply_symm_apply _ _⟩
  · intro hj
    obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
    simpa [Equiv.symm_apply_apply] using hj0

theorem RowScrambleCorrect.rowScrambleNetwork_columnSortNetwork {m n : Nat} (hn : 0 < n)
    (σ : Scramble m n) :
    RowScrambleCorrect m n hn σ (columnSortNetwork m n hn)
      (rowScrambleNetwork m n hn σ) :=
  RowScrambleCorrect.of_rowScrambleNetwork hn σ _ _ (idealColumnSort_columnSortNetwork m n hn)

theorem IdealColumnSort.pack_colSort {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (_pack : SortScrambleSortPack m n hn σ) :
    IdealColumnSort m n hn _pack.colSort :=
  idealColumnSort_columnSortNetwork m n hn

theorem RowScrambleCorrect.all_packs {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) :
    RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble :=
  RowScrambleCorrect.of_rowScrambleNetwork hn σ pack.colSort pack.rowScramble
    (IdealColumnSort.pack_colSort pack)

/-- Canonical Chvátal pack: embedded column sorters + `rowScrambleNetwork` (wired middle stage). -/
def canonicalSortScrambleSortPack (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    SortScrambleSortPack m n hn σ :=
  { rowScramble := rowScrambleNetwork m n hn σ }

theorem IdealColumnSort.all_packs {m n : Nat} (hn : 0 < n) :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort :=
  fun _σ pack => IdealColumnSort.pack_colSort pack

theorem RowScrambleCorrect.all_packs_forall {m n : Nat} (hn : 0 < n) :
    ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble :=
  fun _σ pack => RowScrambleCorrect.all_packs pack

end Chvatal
