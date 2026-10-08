module
/-
  Column-local comparator networks on the matrix wire layout: sorting with `false < true`
  does not increase the number of `true` wires among rows strictly above a cut.
-/

public import AKS.Chvatal.MatrixBridge
public import AKS.Sort.Displaced

@[expose] public section

namespace Chvatal

open Finset

private def aboveBottomRow {m n : Nat} (hn : 0 < n) (i : Nat) (w : Fin (m * n)) : Prop :=
  (matrixRow m n hn w).val < m - i

private theorem row_of_matrixWire {m n : Nat} (hn : 0 < n) (r : Fin m) (j : Fin n) :
    matrixRow m n hn (matrixWire m n r j) = r :=
  (matrixWire_row_col hn r j).1

/-- One column-local comparator does not increase above-bottom `true` counts. -/
theorem matrixOnesCountInRegion_apply_le {m n : Nat} (hn : 0 < n) (i : Nat)
    (c : Comparator (m * n))
    (hcol : ∃ j r s, c.i = matrixWire m n r j ∧ c.j = matrixWire m n s j)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn (c.apply v) i ≤ matrixOnesCountInRegion hn v i := by
  classical
  by_cases hle : v c.i ≤ v c.j
  · rw [Comparator.apply_eq_of_le c v hle]
  · push_neg at hle
    obtain ⟨j, r, s, hri, hsj⟩ := hcol
    have hrs : r.val < s.val :=
      (matrixWire_row_lt_iff hn j).mp (by rw [← hri, ← hsj]; exact c.h)
    have hlt : v c.j < v c.i := by
      revert hle; cases v c.i <;> cases v c.j <;> simp
    have hvi : v c.i = true := by
      revert hlt; cases v c.i <;> cases v c.j <;> simp
    have hsw : ∀ q, c.apply v q = v (Equiv.swap c.i c.j q) :=
      fun q => Comparator.apply_eq_swap c v hlt q
    have hrow_i : matrixRow m n hn c.i = r := by rw [hri]; exact row_of_matrixWire hn r j
    have hrow_j : matrixRow m n hn c.j = s := by rw [hsj]; exact row_of_matrixWire hn s j
    by_cases hbot : s.val < m - i
    · have htop : r.val < m - i := lt_trans hrs hbot
      apply le_of_eq
      apply Finset.card_nbij' (Equiv.swap c.i c.j) (Equiv.swap c.i c.j)
      · intro w hw
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨?_, ?_⟩
        · by_cases hwi : w = c.i
          · rw [hwi, Equiv.swap_apply_left, hrow_j]; exact hbot
          · by_cases hwj : w = c.j
            · rw [hwj, Equiv.swap_apply_right, hrow_i]; exact htop
            · rw [Equiv.swap_apply_of_ne_of_ne hwi hwj]; exact hw.1
        · rw [hsw w] at hw; simpa [Equiv.swap_apply_self] using hw.2
      · intro w hw
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨?_, ?_⟩
        · by_cases hwi : w = c.i
          · rw [hwi, Equiv.swap_apply_left, hrow_j]; exact hbot
          · by_cases hwj : w = c.j
            · rw [hwj, Equiv.swap_apply_right, hrow_i]; exact htop
            · rw [Equiv.swap_apply_of_ne_of_ne hwi hwj]; exact hw.1
        · rw [hsw (Equiv.swap c.i c.j w), Equiv.swap_apply_self]; exact hw.2
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
    · push_neg at hbot
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rw [hsw w] at hw
      by_cases hwi : w = c.i
      · subst hwi; exact hvi
      · by_cases hwj : w = c.j
        · subst hwj; rw [Equiv.swap_apply_right, hrow_j] at hw; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hwi hwj] at hw; exact hw.2

theorem matrixOnesCountInRegion_exec_le {m n : Nat} (hn : 0 < n) (i : Nat)
    (net : ComparatorNetwork (m * n)) (hcol : ColumnLocalNetwork m n net)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn (net.exec v) i ≤ matrixOnesCountInRegion hn v i := by
  rcases net with ⟨cs⟩
  induction cs generalizing v with
  | nil => simp [ComparatorNetwork.exec]
  | cons c cs ih =>
    have htail : ColumnLocalNetwork m n ⟨cs⟩ := fun c' hc' =>
      hcol c' (List.mem_cons_of_mem c hc')
    simp only [ComparatorNetwork.exec, List.foldl_cons]
    exact le_trans (ih (c.apply v) htail)
      (matrixOnesCountInRegion_apply_le hn i c (hcol c (by simp [List.mem_cons])) v)

namespace IdealColumnSort

theorem matrixOnesCountAboveBottom_le {m n : Nat} (hn : 0 < n) {i : Nat} (_him : i ≤ m)
    (colSort : ColumnSortNetwork m n) (_hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountAboveBottom hn colSort.net v i ≤ matrixOnesCountInRegion hn v i := by
  rw [matrixOnesCountAboveBottom_eq_inRegion]
  exact matrixOnesCountInRegion_exec_le hn i colSort.net colSort.col_local v

theorem matrixOnesCountAboveBottom_le_of_exec {m n : Nat} (hn : 0 < n) {i : Nat} (_him : i ≤ m)
    (colSort : ColumnSortNetwork m n) (_hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountAboveBottom hn colSort.net (colSort.net.exec v) i ≤
      matrixOnesCountAboveBottom hn colSort.net v i := by
  rw [matrixOnesCountAboveBottom_eq_inRegion, matrixOnesCountAboveBottom_eq_inRegion]
  exact matrixOnesCountInRegion_exec_le hn i colSort.net colSort.col_local (colSort.net.exec v)

end IdealColumnSort

theorem idealColumnSort_matrixOnesCountAboveBottom_le {m n : Nat} (hn : 0 < n) {i : Nat} (him : i ≤ m)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountAboveBottom hn colSort.net v i ≤ matrixOnesCountInRegion hn v i :=
  IdealColumnSort.matrixOnesCountAboveBottom_le hn him colSort hcol v

theorem MiddleStageSecondColSortHyp.of_idealColumnSort {m n : Nat} (hn : 0 < n) :
    MiddleStageSecondColSortHyp m n hn :=
  fun colSort hcol v i him =>
    IdealColumnSort.matrixOnesCountAboveBottom_le_of_exec hn him colSort hcol v

theorem matrixIntrusionCountB_le_middleThresholdOnesCount {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (_hi1 : 1 ≤ i) (him : i ≤ m) :
    matrixIntrusionCountB pack.net v i ≤
      matrixOnesCountInRegion hn
        (pack.rowScramble.net.exec
          (pack.colSort.net.exec (fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)))) i := by
  rw [matrixIntrusionCountB_eq_matrixOnesCountAboveBottom hn pack.net v i him]
  let u : Fin (m * n) → Bool := fun w =>
    largestKeyThreshold01 (m := m) (n := n) i (v w)
  rw [matrixOnesCountAboveBottom_eq_inRegion]
  calc
    matrixOnesCountInRegion hn (pack.net.exec u) i
    _ = matrixOnesCountInRegion hn
          (pack.colSort.net.exec (pack.rowScramble.net.exec (pack.colSort.net.exec u))) i := by
      rw [SortScrambleSortPack.exec_eq pack u]
    _ ≤ matrixOnesCountInRegion hn (pack.rowScramble.net.exec (pack.colSort.net.exec u)) i :=
      IdealColumnSort.matrixOnesCountAboveBottom_le hn him pack.colSort hcol
        (pack.rowScramble.net.exec (pack.colSort.net.exec u))

/-- Residual: middle monotone count is bounded by combinatorial `onesAboveBottom` at each level.

For decode we need `intrusion ≤ onesAboveBottom` at each level. The direct route (wire-index
keys): after the second column sort, above-bottom count equals `onesAboveBottom` via
`(scrambledColSum - i)_+` on sorted columns — not the antisandwich
`middleMonotoneOneCount ≤ onesAboveBottom` (pre-sort middle count can exceed
`onesAboveBottom`; see `onesAboveBottom_le_middleMonotoneOneCountAboveBottom` for the
other direction). Target lemma:
`matrixIntrusionCountB_le_onesAboveBottom_atLevel_of_keysAreWireIndices` in `MatrixBridge`.
`MiddleStageDecodeHyp` now uses per-level `∃ c` (see `MatrixBridge`). -/
def MiddleStageCountLeOnesAboveBottomHyp (m n : Nat) (hn : 0 < n) : Prop :=
  ∀ {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (_hcol : IdealColumnSort m n hn pack.colSort)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (_hi1 : 1 ≤ i) (him : i ≤ m),
    middleMonotoneOneCountAboveBottom hn pack (monotoneColumnSumsAtLevel hn pack.colSort v i) i ≤
      onesAboveBottom (monotoneColumnSumsAtLevel hn pack.colSort v i) σ i

private theorem matrixRow_val_eq_zero_of_m_eq_one {n : Nat} (hn : 0 < n) (w : Fin (1 * n)) :
    (matrixRow 1 n hn w).val = 0 := by
  rw [matrixRow_val]
  have hwlt : w.val < n := by simpa [one_mul] using w.isLt
  exact Nat.div_eq_of_lt hwlt

/-- No rows strictly above the bottom block when `m ≤ 1` and `1 ≤ i ≤ m`. -/
private theorem middleMonotoneOneCountAboveBottom_eq_zero_of_m_le_one {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m) (hm : m ≤ 1) :
    middleMonotoneOneCountAboveBottom hn pack c i = 0 := by
  rw [RowScrambleCorrect.middleMonotoneOneCountAboveBottom_eq_scrambledOnes hn pack _hrow c i]
  unfold scrambledOnesInAboveBottomRows
  have hm0 : m = 0 ∨ m = 1 := by omega
  rcases hm0 with rfl | hm1
  · exfalso; omega
  · subst hm1
    have hi : i = 1 := by omega
    rw [show i = 1 from hi]
    have hfilter :
        (Finset.univ.filter fun w : Fin (1 * n) =>
            (matrixRow 1 n hn w).val < 1 - 1 ∧
              matrixCol 1 n hn w ∈ scrambledRowOnes c σ (matrixRow 1 n hn w)) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, matrixRow_val_eq_zero_of_m_eq_one hn w,
        show (1 : Nat) - 1 = 0 from rfl, Nat.lt_irrefl 0, false_and, Finset.notMem_empty, iff_false]
    rw [hfilter, Finset.card_empty]

theorem MiddleStageCountLeOnesAboveBottomHyp.of_m_le_one {m n : Nat} (hn : 0 < n) (hm : m ≤ 1) :
    MiddleStageCountLeOnesAboveBottomHyp m n hn := by
  intro σ pack _hcol hrow v i _hi1 him
  have h0 :=
    middleMonotoneOneCountAboveBottom_eq_zero_of_m_le_one hn (pack := pack) hrow
      (monotoneColumnSumsAtLevel hn pack.colSort v i) i _hi1 him hm
  rw [h0]
  exact Nat.zero_le _

theorem MiddleStageCountLeOnesAboveBottomHyp.of_zero_rows (n : Nat) (hn : 0 < n) :
    MiddleStageCountLeOnesAboveBottomHyp 0 n hn :=
  MiddleStageCountLeOnesAboveBottomHyp.of_m_le_one hn (by omega)

/-- If middle and `onesAboveBottom` coincide at each level, the decode-side count bound holds. -/
theorem MiddleStageCountLeOnesAboveBottomHyp.of_onesAboveBottom_eq_middle
    {m n : Nat} (hn : 0 < n)
    (heq :
      ∀ {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
        (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
        (v : Equiv.Perm (Fin (m * n))) (i : Nat) (_hi1 : 1 ≤ i) (him : i ≤ m),
        onesAboveBottom (monotoneColumnSumsAtLevel hn pack.colSort v i) σ i =
          middleMonotoneOneCountAboveBottom hn pack
            (monotoneColumnSumsAtLevel hn pack.colSort v i) i) :
    MiddleStageCountLeOnesAboveBottomHyp m n hn := by
  intro σ pack _hcol hrow v i hi1 him
  rw [← heq (σ := σ) (pack := pack) hrow v i hi1 him]

/-- Bundled first-sort marking obligations for a single level (Chvátal §6 rank/threshold step). -/
structure IdealRowMarkingAtLevel (m n : Nat) (hn : 0 < n) (colSort : ColumnSortNetwork m n)
    (iLevel : Nat) where
  marking_eq_monotone : FirstSortMarkingEqMonotone m n hn colSort iLevel
  marking_agrees_threshold : FirstSortMarkingAgreesThreshold m n hn colSort iLevel
  marking_to_middle_count : MiddleStageMarkingToMiddleCountHyp m n hn iLevel

theorem IdealRowMarkingAtLevel.of_firstSortMarking {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (iLevel : Nat)
    (hmark : FirstSortMarkingEqMonotone m n hn colSort iLevel)
    (hagree : FirstSortMarkingAgreesThreshold m n hn colSort iLevel) :
    IdealRowMarkingAtLevel m n hn colSort iLevel where
  marking_eq_monotone := hmark
  marking_agrees_threshold := hagree
  marking_to_middle_count := MiddleStageMarkingToMiddleCountHyp.of_firstSortMarking hn iLevel

/-- Per-level decode step (Chvátal §6): intrusion → middle threshold count → `onesAboveBottom`. -/
theorem matrixIntrusionCountB_le_onesAboveBottom_atLevel {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hmarkMono : FirstSortMarkingEqMonotone m n hn pack.colSort i)
    (hmarkAgree : FirstSortMarkingAgreesThreshold m n hn pack.colSort i)
    (hmarkLevel : MiddleStageMarkingToMiddleCountHyp m n hn i)
    (hcount : MiddleStageCountLeOnesAboveBottomHyp m n hn)
    (v : Equiv.Perm (Fin (m * n))) :
    matrixIntrusionCountB pack.net v i ≤
      onesAboveBottom (monotoneColumnSumsAtLevel hn pack.colSort v i) σ i := by
  let c := monotoneColumnSumsAtLevel hn pack.colSort v i
  set u := fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)
  calc
    matrixIntrusionCountB pack.net v i
        ≤ matrixOnesCountInRegion hn
            (pack.rowScramble.net.exec (pack.colSort.net.exec u)) i :=
      matrixIntrusionCountB_le_middleThresholdOnesCount hn pack hcol v i hi1 him
    _ = matrixOnesCountInRegion hn (pack.middleExec u) i :=
      (SortScrambleSortPack.middleExec_threshold_region_eq_rowNet hn pack i u).symm
    _ = middleMonotoneOneCountAboveBottom hn pack c i :=
      hmarkLevel (σ := σ) (pack := pack) hcol _hrow hmarkMono hmarkAgree v him
    _ ≤ onesAboveBottom c σ i := hcount (σ := σ) (pack := pack) hcol _hrow v i hi1 him

/-- Marking bundle at every level `1 ≤ i ≤ m`. -/
def IdealRowMarkingHyp (m n : Nat) (hn : 0 < n) : Prop :=
  ∀ {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (_hcol : IdealColumnSort m n hn pack.colSort)
    (_hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m),
    IdealRowMarkingAtLevel m n hn pack.colSort i

theorem matrixIntrusionCountB_le_onesAboveBottom_atLevel_of_idealRowMarking
    {m n : Nat} (hn : 0 < n) {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hmark : IdealRowMarkingAtLevel m n hn pack.colSort i)
    (hcount : MiddleStageCountLeOnesAboveBottomHyp m n hn)
    (v : Equiv.Perm (Fin (m * n))) :
    matrixIntrusionCountB pack.net v i ≤
      onesAboveBottom (monotoneColumnSumsAtLevel hn pack.colSort v i) σ i :=
  matrixIntrusionCountB_le_onesAboveBottom_atLevel hn pack i hi1 him hcol hrow
    hmark.marking_eq_monotone hmark.marking_agrees_threshold hmark.marking_to_middle_count
    hcount v

/-- When `m ≤ 1`, only level `i = 1` occurs and a single column-sum encoding works for decode. -/
private theorem packSemanticIntrusionCountB_eq_zero_of_m_eq_one {n : Nat} (hn : 0 < n)
    {σ : Scramble 1 n} (pack : SortScrambleSortPack 1 n hn σ)
    (_hcol : IdealColumnSort 1 n hn pack.colSort)
    (_hrow : RowScrambleCorrect 1 n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (1 * n))) :
    packSemanticIntrusionCountB hn pack v 1 = 0 := by
  unfold packSemanticIntrusionCountB matrixOnesCountInRegion
  have hempty :
      (Finset.univ.filter fun w : Fin (1 * n) =>
          (matrixRow 1 n hn w).val < 1 - 1 ∧
            (pack.semanticExec fun w => largestKeyThreshold01 (m := 1) (n := n) 1 (v w)) w = true) =
        ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, matrixRow_val_eq_zero_of_m_eq_one hn w,
      show (1 : Nat) - 1 = 0 from rfl, Nat.lt_irrefl 0, false_and, Finset.notMem_empty, iff_false]
  rw [hempty, Finset.card_empty]

theorem MiddleStageDecodeHyp.of_ideal_row_marking_of_m_le_one {m n : Nat} (hn : 0 < n) (hm : m ≤ 1)
    (_hsecond : MiddleStageSecondColSortHyp m n hn)
    (_hmark : IdealRowMarkingHyp m n hn)
    (_hcount : MiddleStageCountLeOnesAboveBottomHyp m n hn) :
    MiddleStageDecodeHyp m n hn where
  decode σ pack hcol hrow v i hi1 him := by
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · exact ⟨fun _j => 0, by omega⟩
    · have hi : i = 1 := by omega
      subst hi
      refine ⟨monotoneColumnSumsAtLevel hn pack.colSort v 1, ?_⟩
      rw [packSemanticIntrusionCountB_eq_zero_of_m_eq_one hn pack hcol hrow v]
      exact Nat.zero_le _

theorem MiddleStageDecodeHyp.of_ideal_row_marking (m n : Nat) (hn : 0 < n) (hm : m ≤ 1)
    (hmark : IdealRowMarkingHyp m n hn)
    (hcount : MiddleStageCountLeOnesAboveBottomHyp m n hn) :
    MiddleStageDecodeHyp m n hn :=
  MiddleStageDecodeHyp.of_ideal_row_marking_of_m_le_one hn hm
    (MiddleStageSecondColSortHyp.of_idealColumnSort hn) hmark hcount

end Chvatal
