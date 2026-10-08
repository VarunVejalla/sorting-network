module
/-
  Row-local scramble as a fixed wire permutation (Chvátal §5 middle stage).
  `rowScrambleNetwork` uses empty comparators; relabeling is `wirePerm`.
-/

public import AKS.Chvatal.MatrixBridge
public import AKS.Sort.Depth
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Chvatal

open List

theorem matrixWire_col_lt_iff {m n : Nat} (hn : 0 < n) (r : Fin m) {j k : Fin n} :
    matrixWire m n r j < matrixWire m n r k ↔ j.val < k.val := by
  constructor
  · intro hlt
    have hval : r.val * n + j.val < r.val * n + k.val := Fin.mk_lt_mk.mp hlt
    exact Nat.add_lt_add_iff_left.mp hval
  · intro hjk
    exact Fin.mk_lt_mk.mpr (Nat.add_lt_add_iff_left.mpr hjk)

/-- Order embedding of column `j` within row `r`. -/
def rowWireEmbed (m n : Nat) (hn : 0 < n) (r : Fin m) : Fin n ↪o Fin (m * n) :=
  OrderEmbedding.ofStrictMono (fun j => matrixWire m n r j)
    fun {a b} hab => (matrixWire_col_lt_iff hn r).2 hab


/-- Row `r` stage: embed a local network at row wires (row-local by construction). -/
def rowEmbedNetwork (m n : Nat) (hn : 0 < n) (r : Fin m) (rowNet : ComparatorNetwork n) :
    ComparatorNetwork (m * n) :=
  rowNet.scatterEmbed (m * n) (rowWireEmbed m n hn r)

/-- Wire permutation for row-wise column scramble `σ` (row-major matrix layout). -/
def rowScrambleWirePerm (m n : Nat) (hn : 0 < n) (σ : Scramble m n) : Equiv.Perm (Fin (m * n)) where
  toFun w :=
    matrixWire m n (matrixRow m n hn w) (σ (matrixRow m n hn w) (matrixCol m n hn w))
  invFun w :=
    matrixWire m n (matrixRow m n hn w) ((σ (matrixRow m n hn w)).symm (matrixCol m n hn w))
  left_inv w := by
    dsimp only
    rw [(matrixWire_row_col hn
          (matrixRow m n hn w)
          (σ (matrixRow m n hn w) (matrixCol m n hn w))).1,
      (matrixWire_row_col hn
          (matrixRow m n hn w)
          (σ (matrixRow m n hn w) (matrixCol m n hn w))).2,
      Equiv.symm_apply_apply]
    exact matrixWire_matrixRow_col hn w
  right_inv w := by
    dsimp only
    rw [(matrixWire_row_col hn
          (matrixRow m n hn w)
          ((σ (matrixRow m n hn w)).symm (matrixCol m n hn w))).1,
      (matrixWire_row_col hn
          (matrixRow m n hn w)
          ((σ (matrixRow m n hn w)).symm (matrixCol m n hn w))).2,
      Equiv.apply_symm_apply]
    exact matrixWire_matrixRow_col hn w

theorem rowScrambleWirePerm_apply (m n : Nat) (hn : 0 < n) (σ : Scramble m n) (r : Fin m)
    (j : Fin n) :
    rowScrambleWirePerm m n hn σ (matrixWire m n r j) = matrixWire m n r (σ r j) := by
  dsimp [rowScrambleWirePerm]
  rw [(matrixWire_row_col hn r j).1, (matrixWire_row_col hn r j).2]

theorem rowScrambleWirePerm_perm_on_matrixWire (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    ∀ (r : Fin m) (j : Fin n),
      rowScrambleWirePerm m n hn σ (matrixWire m n r j) = matrixWire m n r (σ r j) :=
  rowScrambleWirePerm_apply m n hn σ



/-- Row scramble stage: fixed wire relabeling (no comparators). -/
def rowScrambleRowNet (m n : Nat) (hn : 0 < n) (r : Fin m) (_π : Equiv.Perm (Fin n)) :
    ComparatorNetwork (m * n) :=
  rowEmbedNetwork m n hn r (⟨[]⟩ : ComparatorNetwork n)

/-- Full matrix row-scramble witness for scramble `σ`. -/
def rowScrambleNetwork (m n : Nat) (hn : 0 < n) (σ : Scramble m n) : RowScrambleNetwork m n σ where
  net :=
    ⟨List.finRange m |>.flatMap fun r : Fin m =>
      (rowScrambleRowNet m n hn r (σ r)).comparators⟩
  wirePerm := rowScrambleWirePerm m n hn σ
  perm_on_matrixWire := rowScrambleWirePerm_perm_on_matrixWire m n hn σ
  row_local := by
    intro c hc
    simp [rowScrambleRowNet, rowEmbedNetwork, ComparatorNetwork.scatterEmbed, List.mem_flatMap,
      List.mem_map, List.mem_nil_iff] at hc
  comparators_eq_nil := by
    simp [rowScrambleRowNet, rowEmbedNetwork, ComparatorNetwork.scatterEmbed]


theorem rowScrambleNetwork_comparators_eq_nil (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    (rowScrambleNetwork m n hn σ).net.comparators = [] := by
  simp [rowScrambleNetwork, rowScrambleRowNet, rowEmbedNetwork, ComparatorNetwork.scatterEmbed]



/-! **`RowScrambleCorrect` for general `n` (fixed wire permutation). -/

theorem RowScrambleCorrect.of_rowScrambleNetwork {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ)
    (hcol : IdealColumnSort m n hn colSort) :
    RowScrambleCorrect m n hn σ colSort rowScramble := by
  have hperm := rowScramble.perm_on_matrixWire
  refine ⟨fun c r j => ?_⟩
  let v := monotoneMatrixBool (m := m) (n := n) hn c
  have hcol' : colSort.net.exec v = v :=
    IdealColumnSort.exec_eq_of_columnMonotoneInput hn colSort hcol v
      (ColumnMonotoneInput_monotoneMatrixBool hn c)
  have hwire :
      rowScramble.wirePerm.symm (matrixWire m n r j) =
        matrixWire m n r ((σ r).symm j) := by
    apply rowScramble.wirePerm.injective
    rw [Equiv.apply_symm_apply, hperm r ((σ r).symm j)]
    simp [Equiv.symm_apply_apply]
  have hmid :
      sortScrambleMiddleExec colSort rowScramble v (matrixWire m n r j) =
        v (matrixWire m n r ((σ r).symm j)) := by
    calc
      sortScrambleMiddleExec colSort rowScramble v (matrixWire m n r j)
          = _root_.permuteWireValues rowScramble.wirePerm.symm (colSort.net.exec v)
              (matrixWire m n r j) := by
            rw [sortScrambleMiddleExec, RowScrambleNetwork.wiredExec_eq_perm_of_nil rowScramble
              rowScramble.comparators_eq_nil (colSort.net.exec v)]
      _ = colSort.net.exec v (rowScramble.wirePerm.symm (matrixWire m n r j)) := rfl
      _ = v (matrixWire m n r ((σ r).symm j)) := by rw [hcol', hwire]
  rw [hmid, monotoneMatrixBool_matrixWire]
  constructor
  · intro hj
    refine Finset.mem_image.mpr ⟨(σ r).symm j, hj, Equiv.apply_symm_apply _ _⟩
  · intro hj
    obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
    simpa [Equiv.symm_apply_apply] using hj0

theorem RowScrambleCorrect.rowScrambleNetwork_columnSortNetwork {m n : Nat} (hn : 0 < n)
    (σ : Scramble m n) :
    RowScrambleCorrect m n hn σ (columnSortNetwork m n hn)
      (rowScrambleNetwork m n hn σ) :=
  RowScrambleCorrect.of_rowScrambleNetwork hn σ (columnSortNetwork m n hn)
    (rowScrambleNetwork m n hn σ) (idealColumnSort_columnSortNetwork m n hn)

theorem IdealColumnSort.pack_colSort {m n : Nat} {hn : 0 < n} {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) :
    IdealColumnSort m n hn pack.colSort := by
  show IdealColumnSort m n hn (columnSortNetwork m n hn)
  exact idealColumnSort_columnSortNetwork m n hn

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
