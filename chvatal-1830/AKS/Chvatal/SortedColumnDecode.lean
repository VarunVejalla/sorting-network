module
/-
  Column-monotone `Bool` decode: above-bottom counts are `∑ⱼ (colSumⱼ - i)₊`.
  With `IdealColumnSort` + `RowScrambleCorrect`, matrix Property B intrusion equals
  combinatorial `onesAboveBottom` for the post–first-sort column sums of the threshold
  marking — discharging `MiddleStageDecodeHyp` for general `m` and every permutation.

  Property F: top-`j` key marking at fringe depth `f` gives the same `onesAboveBottom`
  route, then `onesAboveBottom_le_onesAboveHalfFringe_univ` discharges
  `MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble`. Closing
  `FringePropertyFClosingHyp.of_idealColumnSort_rowScramble` uses `j < f` from
  `δ_F · n < 1` (paper §7 loop) and zero above-bottom at level `f`.
-/

public import AKS.Chvatal.MatrixBridge
public import AKS.Chvatal.RowScramble
public import AKS.Halver.Defs
public import AKS.Misc.Fin

@[expose] public section

namespace Chvatal

open Finset

/-- Number of `true` wires in column `j`. -/
def matrixColumnTrueCount {m n : Nat} (hn : 0 < n) (j : Fin n) (v : Fin (m * n) → Bool) : Nat :=
  (Finset.univ.filter fun r : Fin m => v (matrixWire m n r j) = true).card

private theorem matrixColumnTrueCount_eq_sum {m n : Nat} (hn : 0 < n) (j : Fin n)
    (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount hn j v =
      ∑ r : Fin m, if v (matrixWire m n r j) = true then (1 : Nat) else 0 := by
  unfold matrixColumnTrueCount
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun r => v (matrixWire m n r j) = true)
    (f := fun _ => (1 : Nat)), Finset.sum_const, Nat.nsmul_eq_mul, mul_one]

/-- `true` count in column `j` among rows strictly above the bottom `i` rows. -/
def matrixColumnOnesAboveBottom {m n : Nat} (hn : 0 < n) (j : Fin n) (v : Fin (m * n) → Bool)
    (i : Nat) : Nat :=
  (Finset.univ.filter fun r : Fin m =>
      r.val < m - i ∧ v (matrixWire m n r j) = true).card

/-- For a column-monotone `Bool` column, above-bottom count is `(colSum - i)` (Nat truncating). -/
theorem matrixColumnOnesAboveBottom_eq_sub {m n : Nat} (hn : 0 < n) (j : Fin n)
    (v : Fin (m * n) → Bool) (i : Nat) (_him : i ≤ m)
    (hmono : ∀ {r s : Fin m}, r ≤ s → v (matrixWire m n r j) ≤ v (matrixWire m n s j)) :
    matrixColumnOnesAboveBottom hn j v i = matrixColumnTrueCount hn j v - i := by
  classical
  set col : Fin m → Bool := fun r => v (matrixWire m n r j)
  have hcolMono : Monotone col := fun r s hrs => hmono hrs
  set falseSet := Finset.univ.filter fun r : Fin m => col r = false
  obtain ⟨hfalse, htrue⟩ := Monotone.bool_pattern_at_card col hcolMono
  set k := falseSet.card
  have hs : matrixColumnTrueCount hn j v = m - k := by
    unfold matrixColumnTrueCount
    have htrueCard :
        (Finset.univ.filter fun r : Fin m => col r = true).card = m - k := by
      have hpart :
          (Finset.univ.filter fun r : Fin m => col r = true).card + falseSet.card = m := by
        have hf : Finset.univ.filter (fun r : Fin m => ¬ col r = true) = falseSet := by
          ext r; simp [falseSet]
        have hcardFalse :
            falseSet.card =
              (Finset.univ.filter fun r : Fin m => ¬ col r = true).card := by
          rw [hf]
        calc
          (Finset.univ.filter fun r : Fin m => col r = true).card + falseSet.card
              = (Finset.univ.filter fun r : Fin m => col r = true).card +
                  (Finset.univ.filter fun r : Fin m => ¬ col r = true).card := by
                rw [hcardFalse]
          _ = (Finset.univ : Finset (Fin m)).card := by
                rw [← Finset.card_filter_add_card_filter_not (fun r : Fin m => col r = true)
                  (s := Finset.univ)]
          _ = m := by rw [Finset.card_univ, Fintype.card_fin]
      have : (Finset.univ.filter fun r : Fin m => col r = true).card + k = m := by
        simpa [k] using hpart
      omega
    simpa [col] using htrueCard
  have hkLeM : k ≤ m :=
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  unfold matrixColumnOnesAboveBottom
  have hfilter :
      (Finset.univ.filter fun r : Fin m => r.val < m - i ∧ col r = true) =
        Finset.univ.filter fun r : Fin m => k ≤ r.val ∧ r.val < m - i := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hr, ht⟩
      refine ⟨?_, hr⟩
      by_contra hk; push_neg at hk
      rw [hfalse r hk] at ht; exact absurd ht (by decide)
    · intro ⟨hk, hr⟩
      exact ⟨hr, htrue r hk⟩
  rw [hfilter, hs]
  by_cases hki : m - i ≤ k
  · have hempty :
        (Finset.univ.filter fun r : Fin m => k ≤ r.val ∧ r.val < m - i) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro ⟨hk, hr⟩
      omega
    rw [hempty, Finset.card_empty]
    have : m - k ≤ i := by omega
    exact (Nat.sub_eq_zero_of_le this).symm
  · push_neg at hki
    by_cases hmi : m - i < m
    · set rLo : Fin m := ⟨k, Nat.lt_of_lt_of_le hki (Nat.sub_le m i)⟩
      set rHi : Fin m := ⟨m - i, hmi⟩
      have hIco :
          (Finset.univ.filter fun r : Fin m => k ≤ r.val ∧ r.val < m - i) =
            Finset.Ico rLo rHi := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico, Fin.le_def, Fin.lt_def,
          rLo, rHi]
      rw [hIco, Fin.card_Ico]
      simp only [rLo, rHi, Fin.val_mk]
      omega
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [Nat.sub_zero] at hfilter hki ⊢
      have hrange :
          (Finset.univ.filter fun r : Fin m => k ≤ r.val ∧ r.val < m) =
            Finset.univ.filter fun r : Fin m => k ≤ r.val := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hk, _⟩; exact hk
        · intro hk; exact ⟨hk, r.isLt⟩
      rw [hrange, card_filter_val_ge m k hkLeM]

/-- Region true-count splits as a sum over columns. -/
theorem matrixOnesCountInRegion_eq_sum_columnOnesAboveBottom {m n : Nat} (hn : 0 < n) (i : Nat)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn v i =
      ∑ j : Fin n, matrixColumnOnesAboveBottom hn j v i := by
  classical
  have hcard :
      matrixOnesCountInRegion hn v i =
        (Finset.univ.filter fun p : Fin m × Fin n =>
            p.1.val < m - i ∧ v (matrixWire m n p.1 p.2) = true).card := by
    unfold matrixOnesCountInRegion
    symm
    apply Finset.card_bij (fun p _ => matrixWire m n p.1 p.2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨hr, ht⟩ := hp
      exact ⟨by simpa [matrixWire_row_col hn] using hr, ht⟩
    · intro p _ q _ h
      exact Prod.ext (matrixWire_injective hn h).1 (matrixWire_injective hn h).2
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      obtain ⟨hr, ht⟩ := hw
      refine ⟨(matrixRow m n hn w, matrixCol m n hn w), ?_, matrixWire_matrixRow_col hn w⟩
      simp only [matrixWire_matrixRow_col hn w]
      exact And.intro hr ht
  have hsum :
      (Finset.univ.filter fun p : Fin m × Fin n =>
          p.1.val < m - i ∧ v (matrixWire m n p.1 p.2) = true).card =
        ∑ j : Fin n, matrixColumnOnesAboveBottom hn j v i := by
    unfold matrixColumnOnesAboveBottom
    set pairs :=
      Finset.univ.filter fun p : Fin m × Fin n =>
        p.1.val < m - i ∧ v (matrixWire m n p.1 p.2) = true
    set colsAll : Finset (Fin n) := Finset.univ
    have hEq :
        pairs =
          colsAll.biUnion fun j =>
            (Finset.univ.filter fun r : Fin m =>
                r.val < m - i ∧ v (matrixWire m n r j) = true).image fun r => (r, j) := by
      ext p
      simp only [pairs, colsAll, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro ⟨hr, ht⟩
        exact ⟨p.2, p.1, ⟨hr, ht⟩, rfl⟩
      · intro h
        obtain ⟨j, r, ⟨hr, ht⟩, heq⟩ := h
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨hr, ht⟩
    have hinj (j : Fin n) :
        Set.InjOn (fun r : Fin m => (r, j)) (Finset.univ.filter fun r : Fin m =>
          r.val < m - i ∧ v (matrixWire m n r j) = true) := by
      intro r₁ _ r₂ _ h
      exact (Prod.ext_iff.mp h).1
    have hdisj :
        Set.PairwiseDisjoint (colsAll : Set (Fin n)) fun j =>
          (Finset.univ.filter fun r : Fin m =>
              r.val < m - i ∧ v (matrixWire m n r j) = true).image fun r => (r, j) := by
      intro j₁ _ j₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
      obtain ⟨_, _, h₁⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, h₂⟩ := Finset.mem_image.mp hp₂
      exact (Prod.ext_iff.mp h₁).2.trans (Prod.ext_iff.mp h₂).2.symm
    rw [hEq, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun j _ => Finset.card_image_of_injOn (hinj j)
  exact hcard.trans hsum

private theorem swap_matrixWire_row {m n : Nat} (hn : 0 < n) (j : Fin n) (r s t : Fin m) :
    Equiv.swap (matrixWire m n r j) (matrixWire m n s j) (matrixWire m n t j) =
      matrixWire m n (Equiv.swap r s t) j := by
  by_cases ht : t = r
  · subst ht; simp [Equiv.swap_apply_left]
  · by_cases ht' : t = s
    · subst ht'; simp [Equiv.swap_apply_right]
    · have h1 : matrixWire m n t j ≠ matrixWire m n r j := by
        intro h; exact ht (matrixWire_injective hn h).1
      have h2 : matrixWire m n t j ≠ matrixWire m n s j := by
        intro h; exact ht' (matrixWire_injective hn h).1
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne ht ht']

/-- One column-local comparator preserves the true-count in every column. -/
private theorem matrixColumnTrueCount_apply_eq {m n : Nat} (hn : 0 < n) (j : Fin n)
    (c : Comparator (m * n))
    (hcol : ∃ j' r s, c.i = matrixWire m n r j' ∧ c.j = matrixWire m n s j')
    (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount hn j (c.apply v) = matrixColumnTrueCount hn j v := by
  classical
  obtain ⟨j', r, s, hri, hsj⟩ := hcol
  by_cases hj : j' = j
  · rw [hj] at hri hsj
    by_cases hle : v c.i ≤ v c.j
    · rw [Comparator.apply_eq_of_le c v hle]
    · push_neg at hle
      have hlt : v c.j < v c.i := by
        revert hle; cases v c.i <;> cases v c.j <;> simp
      have hsw : ∀ q, c.apply v q = v (Equiv.swap c.i c.j q) :=
        fun q => Comparator.apply_eq_swap c v hlt q
      have hrs : r.val < s.val :=
        (matrixWire_row_lt_iff hn j).mp (by rw [← hri, ← hsj]; exact c.h)
      set colApplyTrue :=
        Finset.univ.filter fun t : Fin m => c.apply v (matrixWire m n t j) = true
      set colValueTrue :=
        Finset.univ.filter fun t : Fin m => v (matrixWire m n t j) = true
      unfold matrixColumnTrueCount
      refine (Finset.card_nbij (i := fun t => Equiv.swap r s t) (hi := ?_) (i_inj := ?_) (i_surj := ?_)).symm
      · intro a ha
        have hva : v (matrixWire m n a j) = true := by
          simpa [colValueTrue, Finset.mem_filter, Finset.mem_univ, true_and] using ha
        have happly : c.apply v (matrixWire m n (Equiv.swap r s a) j) = true := by
          rw [hsw, hri, hsj, swap_matrixWire_row hn j r s (Equiv.swap r s a),
            Equiv.swap_apply_self, hva]
        simpa [colApplyTrue, Finset.mem_filter, Finset.mem_univ, true_and] using happly
      · intro a₁ _ a₂ _ h
        exact (Equiv.swap r s).injective h
      · intro b hb
        have happly : c.apply v (matrixWire m n b j) = true := by
          simpa [colApplyTrue, Finset.mem_filter, Finset.mem_univ, true_and] using hb
        refine ⟨Equiv.swap r s b, ?_, ?_⟩
        · have : v (matrixWire m n (Equiv.swap r s b) j) = true := by
            have h := happly
            rw [hsw] at h
            rw [hri, hsj] at h
            rwa [← swap_matrixWire_row hn j r s b]
          simpa [colValueTrue, Finset.mem_filter, Finset.mem_univ, true_and] using this
        · exact Equiv.swap_apply_self r s b
  · have hwire_ne (t : Fin m) :
        matrixWire m n t j ≠ c.i ∧ matrixWire m n t j ≠ c.j := by
      constructor
      · intro h
        rw [hri] at h
        exact hj ((matrixWire_injective hn h).2.symm)
      · intro h
        rw [hsj] at h
        exact hj ((matrixWire_injective hn h).2.symm)
    unfold matrixColumnTrueCount
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨hne1, hne2⟩ := hwire_ne t
    by_cases hle : v c.i ≤ v c.j
    · rw [Comparator.apply_eq_of_le c v hle]
    · push_neg at hle
      have hlt : v c.j < v c.i := by
        revert hle; cases v c.i <;> cases v c.j <;> simp
      rw [Comparator.apply_eq_swap c v hlt, Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- Column-local networks preserve per-column true counts. -/
theorem matrixColumnTrueCount_exec_eq {m n : Nat} (hn : 0 < n) (j : Fin n)
    (net : ComparatorNetwork (m * n)) (hcol : ColumnLocalNetwork m n net)
    (v : Fin (m * n) → Bool) :
    matrixColumnTrueCount hn j (net.exec v) = matrixColumnTrueCount hn j v := by
  rcases net with ⟨cs⟩
  induction cs generalizing v with
  | nil => simp [ComparatorNetwork.exec]
  | cons c cs ih =>
    have htail : ColumnLocalNetwork m n ⟨cs⟩ := fun c' hc' =>
      hcol c' (List.mem_cons_of_mem c hc')
    simp only [ComparatorNetwork.exec, List.foldl_cons]
    have hfold :
        List.foldl (fun acc c' => c'.apply acc) (c.apply v) cs =
          ({ comparators := cs } : ComparatorNetwork (m * n)).exec (c.apply v) := rfl
    rw [hfold, ih (c.apply v) htail]
    exact matrixColumnTrueCount_apply_eq hn j c (hcol c (by simp [List.mem_cons])) v

/-- After an ideal column sort, region count equals `∑ⱼ (colSumⱼ - i)`. -/
theorem matrixOnesCountInRegion_colSort_eq_sum_columnSub {m n : Nat} (hn : 0 < n) (i : Nat)
    (him : i ≤ m) (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn (colSort.net.exec v) i =
      ∑ j : Fin n, (matrixColumnTrueCount hn j v - i) := by
  have hcm : ColumnMonotoneInput m n hn (colSort.net.exec v) :=
    IdealColumnSort.exec_columnMonotoneInput hn colSort hcol v
  calc
    matrixOnesCountInRegion hn (colSort.net.exec v) i
        = ∑ j : Fin n, matrixColumnOnesAboveBottom hn j (colSort.net.exec v) i :=
      matrixOnesCountInRegion_eq_sum_columnOnesAboveBottom hn i (colSort.net.exec v)
    _ = ∑ j : Fin n, (matrixColumnTrueCount hn j (colSort.net.exec v) - i) := by
      refine Finset.sum_congr rfl fun j _ =>
        matrixColumnOnesAboveBottom_eq_sub hn j (colSort.net.exec v) i him
          (fun hrs => hcm j hrs)
    _ = ∑ j : Fin n, (matrixColumnTrueCount hn j v - i) := by
      refine Finset.sum_congr rfl fun j _ => by
        rw [matrixColumnTrueCount_exec_eq hn j colSort.net colSort.col_local v]

/-- Column sums of a Boolean matrix, as a `MonotoneColumnSums` witness. -/
def monotoneColumnSumsOfBool {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) :
    MonotoneColumnSums m n :=
  fun (j : Fin n) =>
    ⟨matrixColumnTrueCount hn j v,
      by
        have hle : matrixColumnTrueCount hn j v ≤ m := by
          unfold matrixColumnTrueCount
          exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
        exact Nat.lt_succ_of_le hle⟩

theorem monotoneMatrixBool_eq_of_columnMonotone {m n : Nat} (hn : 0 < n)
    (v : Fin (m * n) → Bool) (hcm : ColumnMonotoneInput m n hn v) :
    v = monotoneMatrixBool hn (monotoneColumnSumsOfBool hn v) := by
  classical
  refine ColumnMonotoneInput.eq_of_matrixWire_eq hn hcm
      (ColumnMonotoneInput_monotoneMatrixBool hn _) fun r j => ?_
  set c := monotoneColumnSumsOfBool hn v
  set col : Fin m → Bool := fun r' => v (matrixWire m n r' j)
  have hmono : Monotone col := fun a b hab => hcm j hab
  set falseSet := Finset.univ.filter fun r' : Fin m => col r' = false
  obtain ⟨hfalse, htrue⟩ := Monotone.bool_pattern_at_card col hmono
  set k := falseSet.card
  have hpart : (Finset.univ.filter fun r' => col r' = true).card + falseSet.card = m := by
      have hf : Finset.univ.filter (fun r' : Fin m => ¬ col r' = true) = falseSet := by
        ext r'; simp [falseSet]
      have hcardFalse :
          falseSet.card =
            (Finset.univ.filter (fun r' : Fin m => ¬ col r' = true)).card := by
        rw [hf]
      calc
        (Finset.univ.filter fun r' => col r' = true).card + falseSet.card
            = (Finset.univ.filter fun r' => col r' = true).card +
                (Finset.univ.filter (fun r' : Fin m => ¬ col r' = true)).card := by
              rw [hcardFalse]
        _ = (Finset.univ : Finset (Fin m)).card := by
              rw [← Finset.card_filter_add_card_filter_not (fun r' : Fin m => col r' = true)
                (s := Finset.univ)]
        _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  have hmc : matrixColumnTrueCount hn j v = m - k := by
    unfold matrixColumnTrueCount
    have hfilt :
        Finset.univ.filter (fun r' : Fin m => v (matrixWire m n r' j) = true) =
          Finset.univ.filter (fun r' : Fin m => col r' = true) := by
      ext r'; simp [col]
    rw [hfilt]
    have : (Finset.univ.filter fun r' => col r' = true).card + k = m := by
      simpa [k] using hpart
    omega
  have hc : (c j).val = m - k := by
    dsimp [c, monotoneColumnSumsOfBool, matrixColumnTrueCount]
    exact hmc
  by_cases hv : v (matrixWire m n r j) = true
  · have hkrow : k ≤ r.val := by
      by_contra hkrow; push_neg at hkrow
      exact absurd (hfalse r hkrow) (by simpa [col] using hv)
    have hle : m - r.val ≤ (c j).val := by rw [hc]; exact Nat.sub_le_sub_left hkrow m
    simp [monotoneMatrixBool, matrixWire_row_col hn r j, decide_eq_true_iff,
      mem_monotoneRowOnes_iff, hv, hle]
  · have hv' : v (matrixWire m n r j) = false := by
      cases h : v (matrixWire m n r j) <;> simp_all
    have hkrow : r.val < k := by
      by_contra hkrow; push_neg at hkrow
      exact absurd (htrue r hkrow) (by simpa [col] using hv')
    have hlt : (c j).val < m - r.val := by rw [hc]; omega
    have hnin : j ∉ monotoneRowOnes c r := by
      rw [mem_monotoneRowOnes_iff]; exact not_le.mpr hlt
    simp [monotoneMatrixBool, matrixWire_row_col hn r j, hnin, hv']

theorem scrambledColSum_eq_matrixColumnTrueCount_of_rowScramble {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (c : MonotoneColumnSums m n) (j : Fin n) :
    scrambledColSum c σ j =
      matrixColumnTrueCount hn j (pack.middleExec (monotoneMatrixBool hn c)) := by
  classical
  set mid := pack.middleExec (monotoneMatrixBool hn c)
  unfold scrambledColSum
  have hsum :
      (∑ r : Fin m, if j ∈ scrambledRowOnes c σ r then 1 else 0) =
        ∑ r : Fin m, if mid (matrixWire m n r j) = true then 1 else 0 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    have hiff := hrow.maps_scramble c r j
    have hmid :
        mid (matrixWire m n r j) = true ↔ j ∈ scrambledRowOnes c σ r := by
      dsimp [mid, SortScrambleSortPack.middleExec]
      exact hiff
    by_cases h : j ∈ scrambledRowOnes c σ r <;>
      simp [h, hmid, matrixWire_row_col hn r j, ↓reduceIte]
  rw [hsum, matrixColumnTrueCount_eq_sum hn j mid]

/-- After the full pack on a Boolean marking, region count equals `onesAboveBottom`. -/
theorem matrixOnesCountInRegion_pack_eq_onesAboveBottom {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Fin (m * n) → Bool) (i : Nat) (him : i ≤ m) :
    matrixOnesCountInRegion hn (pack.colSort.net.exec (pack.middleExec v)) i =
      onesAboveBottom (monotoneColumnSumsOfBool hn (pack.colSort.net.exec v)) σ i := by
  set u1 := pack.colSort.net.exec v
  set c := monotoneColumnSumsOfBool hn u1
  have hcm : ColumnMonotoneInput m n hn u1 :=
    IdealColumnSort.exec_columnMonotoneInput hn pack.colSort hcol v
  have hu1 : u1 = monotoneMatrixBool hn c := monotoneMatrixBool_eq_of_columnMonotone hn u1 hcm
  have hmb_cm : ColumnMonotoneInput m n hn (monotoneMatrixBool hn c) :=
    ColumnMonotoneInput_monotoneMatrixBool hn c
  have hfix_mb :
      pack.colSort.net.exec (monotoneMatrixBool hn c) = monotoneMatrixBool hn c :=
    IdealColumnSort.exec_eq_of_columnMonotoneInput hn pack.colSort hcol _ hmb_cm
  have hmid_v :
      pack.middleExec v = pack.middleExec (monotoneMatrixBool hn c) := by
    rw [SortScrambleSortPack.middle_exec_eq, SortScrambleSortPack.middle_exec_eq,
      show pack.colSort.net.exec v = pack.colSort.net.exec (monotoneMatrixBool hn c) by
        calc pack.colSort.net.exec v = u1 := rfl
          _ = monotoneMatrixBool hn c := hu1
          _ = pack.colSort.net.exec (monotoneMatrixBool hn c) := hfix_mb.symm]
  rw [hmid_v]
  have hregion :
      matrixOnesCountInRegion hn
          (pack.colSort.net.exec (pack.middleExec (monotoneMatrixBool hn c))) i =
        ∑ j : Fin n, (matrixColumnTrueCount hn j
            (pack.middleExec (monotoneMatrixBool hn c)) - i) :=
    matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i him pack.colSort hcol _
  rw [hregion]
  unfold onesAboveBottom
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← scrambledColSum_eq_matrixColumnTrueCount_of_rowScramble hn pack hrow c j]


/-- Semantic decode: region after `semanticExec` equals `onesAboveBottom`. -/
theorem matrixIntrusionCountB_semantic_eq_onesAboveBottom {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (him : i ≤ m) :
    matrixOnesCountInRegion hn
        (pack.semanticExec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)) i =
      onesAboveBottom
        (monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)))
        σ i := by
  set u := fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)
  simpa [SortScrambleSortPack.semanticExec] using
    matrixOnesCountInRegion_pack_eq_onesAboveBottom hn pack hcol hrow u i him

theorem packSemanticIntrusionCountB_eq_onesAboveBottom {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (i : Nat) (him : i ≤ m) :
    packSemanticIntrusionCountB hn pack v i =
      onesAboveBottom
        (monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)))
        σ i :=
  matrixIntrusionCountB_semantic_eq_onesAboveBottom hn pack hcol hrow v i him

/-- General `m`, `n`: semantic Property B decode (middle stage uses `wirePerm`). -/
theorem MiddleStageDecodeHyp.of_idealColumnSort_rowScramble {m n : Nat} (hn : 0 < n) :
    MiddleStageDecodeHyp m n hn where
  decode := fun σ pack hcol hrow v i _hi1 him => by
    refine ⟨monotoneColumnSumsOfBool hn
        (pack.colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)), ?_⟩
    exact le_of_eq (packSemanticIntrusionCountB_eq_onesAboveBottom hn pack hcol hrow v i him)

theorem HasPackSemanticPropertyB.of_combinatorial {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hComb : HasCombinatorialPropertyB σ epsB) :
    HasPackSemanticPropertyB hn pack epsB := by
  rw [HasPackSemanticPropertyB_iff]
  intro v i hi1 him
  rw [packSemanticIntrusionCountB_eq_onesAboveBottom hn pack hcol hrow v i him]
  exact hComb
      (monotoneColumnSumsOfBool hn
        (pack.colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w)))
      i hi1 him

theorem HasPackSemanticPropertyB_canonical_of_combinatorial {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (σ : Scramble m n) (hComb : HasCombinatorialPropertyB σ epsB) :
    HasMatrixPropertyB_exec m n hn (canonicalSortScrambleSortPack m n hn σ) epsB :=
  HasPackSemanticPropertyB.of_combinatorial hn (canonicalSortScrambleSortPack m n hn σ)
    (idealColumnSort_columnSortNetwork m n hn)
    (RowScrambleCorrect.rowScrambleNetwork_columnSortNetwork hn σ) hComb

/-- Combinatorial Property B on `σ` ⇒ semantic matrix Property B on the canonical pack. -/
theorem combinatorialPropertyB_implies_matrixB_exec_canonical {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (σ : Scramble m n) (hComb : HasCombinatorialPropertyB σ epsB) :
    HasMatrixPropertyB_exec m n hn (canonicalSortScrambleSortPack m n hn σ) epsB :=
  HasPackSemanticPropertyB_canonical_of_combinatorial hn σ hComb

theorem CombinatorialToMatrixObligationB.of_columnSortNetwork_rowScramble {m n : Nat} {epsB : ℝ}
    (hn : 0 < n)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    CombinatorialToMatrixObligationB m n hn epsB :=
  CombinatorialToMatrixObligationB.of_idealColumnSort_rowScrambleCorrect_decodeHyp hn hcol hrow
    (MiddleStageDecodeHyp.of_idealColumnSort_rowScramble hn)

theorem MatrixBridgeBResidual.of_columnSortNetwork_rowScramble_discharged {m n : Nat} {hn : 0 < n}
    {epsB : ℝ}
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    MatrixBridgeBResidual m n hn epsB :=
  MatrixBridgeBResidual.of_columnSortNetwork_rowScramble
    (MiddleStageDecodeHyp.of_idealColumnSort_rowScramble hn) hcol hrow

/-- When `wirePerm = 1`, semantic execution matches `pack.net` (comparator middle stage). -/
theorem MiddleStageDecodeHyp.of_idealColumnSort_rowScramble_of_wirePerm_one {m n : Nat}
    (hn : 0 < n)
    (hπ : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      pack.rowScramble.wirePerm = 1) :
    MiddleStageDecodeHyp m n hn :=
  MiddleStageDecodeHyp.of_idealColumnSort_rowScramble hn

/-! **Property F (fringe depth `f`, top-`j` keys)** -/

theorem matrixOnesCountInRegion_pack_eq_onesAboveBottom_f {m n f : Nat} (hn : 0 < n)
    (hfm : f ≤ m) {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (j : Nat) :
    matrixOnesCountInRegion hn
        (pack.colSort.net.exec
          (pack.middleExec
            (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))) f =
      onesAboveBottom
        (monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
        σ f := by
  set u1 := pack.colSort.net.exec
      (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  set c := monotoneColumnSumsOfBool hn u1
  have hcm : ColumnMonotoneInput m n hn u1 :=
    IdealColumnSort.exec_columnMonotoneInput hn pack.colSort hcol
      (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have hu1 : u1 = monotoneMatrixBool hn c := monotoneMatrixBool_eq_of_columnMonotone hn u1 hcm
  have hmb_cm : ColumnMonotoneInput m n hn (monotoneMatrixBool hn c) :=
    ColumnMonotoneInput_monotoneMatrixBool hn c
  have hfix_mb :
      pack.colSort.net.exec (monotoneMatrixBool hn c) = monotoneMatrixBool hn c :=
    IdealColumnSort.exec_eq_of_columnMonotoneInput hn pack.colSort hcol _ hmb_cm
  have hmid_v :
      pack.middleExec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) =
        pack.middleExec (monotoneMatrixBool hn c) := by
    rw [SortScrambleSortPack.middle_exec_eq, SortScrambleSortPack.middle_exec_eq,
      show pack.colSort.net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) =
          pack.colSort.net.exec (monotoneMatrixBool hn c) by
        calc pack.colSort.net.exec (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) = u1 := rfl
          _ = monotoneMatrixBool hn c := hu1
          _ = pack.colSort.net.exec (monotoneMatrixBool hn c) := hfix_mb.symm]
  rw [hmid_v]
  have hregion :
      matrixOnesCountInRegion hn
          (pack.colSort.net.exec (pack.middleExec (monotoneMatrixBool hn c))) f =
        ∑ col : Fin n, (matrixColumnTrueCount hn col
            (pack.middleExec (monotoneMatrixBool hn c)) - f) :=
    matrixOnesCountInRegion_colSort_eq_sum_columnSub hn f hfm pack.colSort hcol _
  rw [hregion]
  unfold onesAboveBottom
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [← scrambledColSum_eq_matrixColumnTrueCount_of_rowScramble hn pack hrow c col]

theorem packSemanticIntrusionCountF_eq_onesAboveBottom {m n f : Nat} (hn : 0 < n) (hfm : f ≤ m)
    {hf : Even f} {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (v : Equiv.Perm (Fin (m * n))) (j : Nat) :
    packSemanticIntrusionCountF hn pack v f j =
      onesAboveBottom
        (monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
        σ f := by
  unfold packSemanticIntrusionCountF
  simpa [SortScrambleSortPack.semanticExec] using
    matrixOnesCountInRegion_pack_eq_onesAboveBottom_f hn hfm pack hcol hrow v j

/-- General `m`, `n`: semantic fringe decode via `(colSum−f)₊` then `onesAboveHalfFringe` on `univ`. -/
theorem MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) {deltaF : ℝ} :
    MiddleStageFringeDecodeHyp m n f hf hn deltaF where
  decode := fun σ pack hcol hrow v j _hj _hjδ => by
    refine
      ⟨monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)),
        Finset.univ, ?_⟩
    calc packSemanticIntrusionCountF hn pack v f j
        = onesAboveBottom
            (monotoneColumnSumsOfBool hn
              (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
            σ f :=
          packSemanticIntrusionCountF_eq_onesAboveBottom (m := m) (n := n) (f := f) hn hfm
            (hf := hf) (σ := σ) (pack := pack) hcol hrow v j
      _ ≤ onesAboveHalfFringe hf
          (monotoneColumnSumsOfBool hn
            (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
          σ (Finset.univ : Finset (Fin n)) :=
        onesAboveBottom_le_onesAboveHalfFringe_univ hn
          (monotoneColumnSumsOfBool hn
            (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
          σ hfm

/-! **Top-`j` marking counts (Property F closing)** -/

private theorem nat_le_sum_of_sum_eq {ι : Type*} [Fintype ι] {f : ι → Nat} {T : Nat}
    (hsum : ∑ i : ι, f i = T) (i : ι) : f i ≤ T := by
  calc f i ≤ ∑ j : ι, f j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = T := hsum

private theorem card_topJKeys (N j : Nat) (_hjpos : 0 < j) (hj : j ≤ N) :
    (Finset.univ.filter fun k : Fin N => N - j ≤ k.val).card = j := by
  have hthresh : N - j ≤ N := Nat.sub_le _ _
  calc (Finset.univ.filter fun k : Fin N => N - j ≤ k.val).card
      = N - (N - j) := card_filter_val_ge N (N - j) hthresh
    _ = j := by omega

private theorem topJMarking_trueWireCount_eq {m n : Nat} (j : Nat) (hjpos : 0 < j) (hjmn : j ≤ m * n)
    (v : Equiv.Perm (Fin (m * n))) :
    (Finset.univ.filter fun w : Fin (m * n) =>
        largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true).card = j := by
  classical
  set topKeys : Finset (Fin (m * n)) :=
    Finset.univ.filter fun k : Fin (m * n) => m * n - j ≤ k.val
  have htopCard : topKeys.card = j := card_topJKeys (m * n) j hjpos hjmn
  have hcard :
      (Finset.univ.filter fun w : Fin (m * n) =>
          largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true).card = j := by
    have hset :
        (Finset.univ.filter fun w : Fin (m * n) => v w ∈ topKeys) = topKeys.image v.symm := by
      ext w
      constructor
      · intro hmem
        rcases Finset.mem_filter.mp hmem with ⟨_, htop⟩
        exact Finset.mem_image.mpr ⟨v w, htop, Equiv.symm_apply_apply v w⟩
      · intro hmem
        obtain ⟨k, htop, hvk⟩ := Finset.mem_image.mp hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
        have hw' : v w = k := by rw [← hvk, v.apply_symm_apply k]
        simpa [hw'] using htop
    have hfilterEq :
        (Finset.univ.filter fun w : Fin (m * n) =>
            largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true) =
          Finset.univ.filter fun w : Fin (m * n) => v w ∈ topKeys := by
      ext w
      simp [topKeys, largestKeyThresholdJ01, decide_eq_true_iff]
    calc (Finset.univ.filter fun w =>
            largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true).card
        = (Finset.univ.filter fun w : Fin (m * n) => v w ∈ topKeys).card := by rw [hfilterEq]
    _ = (topKeys.image v.symm).card := by rw [hset]
    _ = topKeys.card := Finset.card_image_of_injective _ v.symm.injective
    _ = j := htopCard
  exact hcard

private theorem sum_matrixColumnTrueCount_eq_trueWireCount {m n : Nat} (hn : 0 < n)
    (v : Fin (m * n) → Bool) :
    ∑ col : Fin n, matrixColumnTrueCount hn col v =
      (Finset.univ.filter fun w : Fin (m * n) => v w = true).card := by
  classical
  have hEq :
      (Finset.univ.filter fun w : Fin (m * n) => v w = true) =
        Finset.biUnion (Finset.univ : Finset (Fin n)) fun col =>
          (Finset.univ.filter fun r : Fin m => v (matrixWire m n r col) = true).image
            (fun r => matrixWire m n r col) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · intro hv
      refine ⟨matrixCol m n hn w, matrixRow m n hn w, ?_, matrixWire_matrixRow_col hn w⟩
      rw [matrixWire_matrixRow_col hn w]
      exact hv
    · intro ⟨col, r, hv, heq⟩
      rw [← heq]
      exact hv
  have hinj (col : Fin n) :
      Set.InjOn (fun r : Fin m => matrixWire m n r col)
        (Finset.univ.filter fun r : Fin m => v (matrixWire m n r col) = true) := by
    intro r₁ _ r₂ _ h
    exact (matrixWire_injective hn h).1
  have hdisj :
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fun col =>
        (Finset.univ.filter fun r : Fin m => v (matrixWire m n r col) = true).image
          (fun r => matrixWire m n r col) := by
    intro col₁ _ col₂ _ hne
    refine Finset.disjoint_left.mpr fun w hw hb => hne ?_
    obtain ⟨r₁, _, hr₁⟩ := Finset.mem_image.mp hw
    obtain ⟨r₂, _, hr₂⟩ := Finset.mem_image.mp hb
    exact (matrixWire_injective hn (hr₁.trans hr₂.symm)).2
  rw [hEq, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun col _ => ?_
  unfold matrixColumnTrueCount
  exact (Finset.card_image_of_injOn (hinj col)).symm

theorem totalColumnOnes_monotoneColumnSumsOfBool_eq_trueWireCount {m n : Nat} (hn : 0 < n)
    (v : Fin (m * n) → Bool) :
    totalColumnOnes (monotoneColumnSumsOfBool hn v) =
      (Finset.univ.filter fun w : Fin (m * n) => v w = true).card := by
  unfold totalColumnOnes monotoneColumnSumsOfBool
  rw [← sum_matrixColumnTrueCount_eq_trueWireCount hn v]

theorem totalColumnOnes_monotoneColumnSumsOfBool_colSort_exec_eq {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Fin (m * n) → Bool) :
    totalColumnOnes (monotoneColumnSumsOfBool hn (colSort.net.exec v)) =
      totalColumnOnes (monotoneColumnSumsOfBool hn v) := by
  unfold totalColumnOnes monotoneColumnSumsOfBool
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp
  exact matrixColumnTrueCount_exec_eq hn j colSort.net colSort.col_local v

theorem largestKeyThreshold01_trueWireCount_eq {m n : Nat} (hn : 0 < n) (i : Nat) (hi : 1 ≤ i)
    (him : i ≤ m) (v : Equiv.Perm (Fin (m * n))) :
    (Finset.univ.filter fun w : Fin (m * n) =>
        largestKeyThreshold01 (m := m) (n := n) i (v w) = true).card = i * n := by
  set j := i * n
  have hi0 : 0 < i := Nat.lt_of_lt_of_le (by decide : 0 < 1) hi
  have hjpos : 0 < j := by dsimp [j]; exact Nat.mul_pos hi0 hn
  have hjmn : j ≤ m * n := by dsimp [j]; exact Nat.mul_le_mul_right n him
  have hcard := topJMarking_trueWireCount_eq (m := m) (n := n) j hjpos hjmn v
  have hfilter :
      (Finset.univ.filter fun w : Fin (m * n) =>
          largestKeyThreshold01 (m := m) (n := n) i (v w) = true) =
        (Finset.univ.filter fun w : Fin (m * n) =>
          largestKeyThresholdJ01 (m := m) (n := n) j (v w) = true) := by
    ext w
    simp [largestKeyThreshold01, largestKeyThresholdJ01, isAmongLargestKeysBlock, j]
  rw [hfilter, hcard]

/-- Decode column sums after ideal column sort at level `i`: total mass `i·n` (avg row ones `= i`). -/
theorem totalColumnOnes_decodeColumnSums_atLevel_eq {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (i : Nat) (hi : 1 ≤ i) (him : i ≤ m) (v : Equiv.Perm (Fin (m * n))) :
    totalColumnOnes
        (monotoneColumnSumsOfBool hn
          (colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w))) =
      i * n := by
  rw [totalColumnOnes_monotoneColumnSumsOfBool_colSort_exec_eq hn colSort hcol]
  rw [totalColumnOnes_monotoneColumnSumsOfBool_eq_trueWireCount hn]
  exact largestKeyThreshold01_trueWireCount_eq hn i hi him v

theorem totalColumnOnesLeLevel_decodeColumnSums_atLevel {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m) (v : Equiv.Perm (Fin (m * n))) :
    TotalColumnOnesLeLevel m n i
        (monotoneColumnSumsOfBool hn
          (colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w))) := by
  dsimp [TotalColumnOnesLeLevel]
  rw [totalColumnOnes_decodeColumnSums_atLevel_eq hn colSort hcol i hi1 him v]
  exact Nat.le_of_eq (Nat.mul_comm i n)

theorem HasPackSemanticPropertyB.of_combinatorial_onPipeline {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (hrow : RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hComb : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasPackSemanticPropertyB hn pack epsB := by
  rw [HasPackSemanticPropertyB_iff]
  intro v i hi1 him
  set c := monotoneColumnSumsOfBool hn
      (pack.colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) i (v w))
  rw [packSemanticIntrusionCountB_eq_onesAboveBottom hn pack hcol hrow v i him]
  exact hComb c i (totalColumnOnesLeLevel_decodeColumnSums_atLevel hn pack.colSort hcol i hi1 him v)
    hi1 him

theorem HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline {m n : Nat} {epsB : ℝ}
    (hn : 0 < n) (σ : Scramble m n) (hComb : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasMatrixPropertyB_exec m n hn (canonicalSortScrambleSortPack m n hn σ) epsB :=
  HasPackSemanticPropertyB.of_combinatorial_onPipeline hn (canonicalSortScrambleSortPack m n hn σ)
    (idealColumnSort_columnSortNetwork m n hn)
    (RowScrambleCorrect.rowScrambleNetwork_columnSortNetwork hn σ) hComb

theorem totalColumnOnes_decodeColumnSums_atLevel_one_eq {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Equiv.Perm (Fin (m * n))) (him : 1 ≤ m) :
    totalColumnOnes
        (monotoneColumnSumsOfBool hn
          (colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) 1 (v w))) =
      n := by
  simpa [Nat.one_mul] using
    totalColumnOnes_decodeColumnSums_atLevel_eq hn colSort hcol 1 (by decide) him v

theorem avgRowOnes_decodeColumnSums_atLevel_one_eq {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Equiv.Perm (Fin (m * n))) (him : 1 ≤ m) :
    avgRowOnes
        (monotoneColumnSumsOfBool hn
          (colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) 1 (v w))) =
      (1 : ℝ) := by
  set c := monotoneColumnSumsOfBool hn
      (colSort.net.exec fun w => largestKeyThreshold01 (m := m) (n := n) 1 (v w))
  have htotal := totalColumnOnes_decodeColumnSums_atLevel_one_eq hn colSort hcol v him
  exact avgRowOnes_eq_one_of_totalColumnOnes_eq_n hn c htotal

theorem combinatorialPropertyB_onPipeline_implies_matrixB_exec_canonical {m n : Nat} {epsB : ℝ}
    (hn : 0 < n) (σ : Scramble m n) (hComb : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasMatrixPropertyB_exec m n hn (canonicalSortScrambleSortPack m n hn σ) epsB :=
  HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hn σ hComb

private theorem columnSum_eq_card_rows {m n : Nat} (c : MonotoneColumnSums m n) (j : Fin n) :
    (c j).val =
      (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r).card := by
  classical
  set k := (c j).val
  by_cases hk0 : k = 0
  · rw [hk0]
    have hempty :
        (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_monotoneRowOnes_iff,
        Finset.notMem_empty, iff_false]
      intro hle
      have : r.val < m := r.isLt
      omega
    simp [hempty]
  · have hkm : k ≤ m := Nat.lt_succ_iff.mp (c j).isLt
    set rMin : Fin m := ⟨m - k, by omega⟩
    have hfilter :
        Finset.univ.filter (fun r : Fin m => j ∈ monotoneRowOnes c r) =
          Finset.univ.filter fun r' : Fin m => rMin ≤ r' := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_monotoneRowOnes_iff]
      rw [Fin.mk_le_mk]
      omega
    rw [hfilter, card_filter_row_ge rMin]
    have hrMin : rMin.val = m - k := rfl
    calc k = m - (m - k) := (Nat.sub_sub_self hkm).symm
      _ = m - rMin.val := by rw [hrMin]

private theorem sum_colSum_eq_sum_rowOnes {m n : Nat} (c : MonotoneColumnSums m n) :
    ∑ j : Fin n, (c j).val = ∑ r : Fin m, (monotoneRowOnes c r).card := by
  classical
  calc ∑ j : Fin n, (c j).val
      = ∑ j : Fin n,
          (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r).card := by
          refine Finset.sum_congr rfl fun j _ => columnSum_eq_card_rows c j
    _ = ∑ j : Fin n, ∑ r : Fin m, if j ∈ monotoneRowOnes c r then 1 else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter]
    _ = ∑ r : Fin m, ∑ j : Fin n, if j ∈ monotoneRowOnes c r then 1 else 0 := Finset.sum_comm
    _ = ∑ r : Fin m, (monotoneRowOnes c r).card := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_filter (s := Finset.univ)
            (p := fun j : Fin n => j ∈ monotoneRowOnes c r) (f := fun _ => (1 : Nat))]
          simp [Finset.sum_ite, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem sum_scrambledColSum_eq_sum_colSum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) :
    ∑ j : Fin n, scrambledColSum c σ j = ∑ j : Fin n, (c j).val := by
  classical
  have hrow (r : Fin m) :
      (scrambledRowOnes c σ r).card = (monotoneRowOnes c r).card := by
    rw [scrambledRowOnes]
    exact Finset.card_image_of_injective _ (σ r).injective
  calc ∑ j : Fin n, scrambledColSum c σ j
      = onesInColumns c σ Finset.univ := (onesInColumns_eq_sum_colSums c σ Finset.univ).symm
    _ = ∑ r : Fin m, rowHit c Finset.univ r (σ r) := onesInColumns_eq_sum_rowHit c Finset.univ σ
    _ = ∑ r : Fin m, (scrambledRowOnes c σ r).card := by
          refine Finset.sum_congr rfl fun r _ => by
            simp [rowHit, scrambledRowOnes, Finset.inter_univ]
    _ = ∑ r : Fin m, (monotoneRowOnes c r).card := by
          refine Finset.sum_congr rfl fun r _ => hrow r
    _ = ∑ j : Fin n, (c j).val := (sum_colSum_eq_sum_rowOnes c).symm

theorem sum_topJ_colSums_eq_j {m n : Nat} (hn : 0 < n)
    (colSort : ColumnSortNetwork m n) (hcol : IdealColumnSort m n hn colSort)
    (v : Equiv.Perm (Fin (m * n))) (j : Nat) (hjpos : 0 < j) (hjmn : j ≤ m * n) :
    ∑ col : Fin n,
        (monotoneColumnSumsOfBool hn
            (colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) col).val =
      j := by
  set u := fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)
  set c := monotoneColumnSumsOfBool hn (colSort.net.exec u)
  have hsum := sum_matrixColumnTrueCount_eq_trueWireCount hn u
  have hj := topJMarking_trueWireCount_eq j hjpos hjmn v
  calc ∑ col : Fin n, (c col).val
      = ∑ col : Fin n, matrixColumnTrueCount hn col (colSort.net.exec u) := by
        refine Finset.sum_congr rfl fun col _ => ?_
        simp [c, monotoneColumnSumsOfBool, matrixColumnTrueCount]
    _ = ∑ col : Fin n, matrixColumnTrueCount hn col u := by
        refine Finset.sum_congr rfl fun col _ =>
          matrixColumnTrueCount_exec_eq hn col colSort.net colSort.col_local u
    _ = j := by rw [hsum, hj]

theorem scrambledColSum_le_j_of_topJMarking {m n : Nat} (hn : 0 < n)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hcol : IdealColumnSort m n hn pack.colSort)
    (v : Equiv.Perm (Fin (m * n))) (j : Nat) (hjpos : 0 < j) (hjmn : j ≤ m * n) (col : Fin n) :
    scrambledColSum
        (monotoneColumnSumsOfBool hn
          (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)))
        σ col ≤ j := by
  set c := monotoneColumnSumsOfBool hn
      (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have hsum := sum_scrambledColSum_eq_sum_colSum c σ
  have htotal := sum_topJ_colSums_eq_j hn pack.colSort hcol v j hjpos hjmn
  rw [← hsum] at htotal
  exact nat_le_sum_of_sum_eq (ι := Fin n) (f := fun col' => scrambledColSum c σ col') htotal col

/-- Closing F-bridge: decode + `j < f` (from `δ_F·n < 1`) ⇒ semantic `< ε_F·j`. -/
theorem FringePropertyFClosingHyp.of_idealColumnSort_rowScramble {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    FringePropertyFClosingHyp m n f hn hf hfm deltaF epsF := by
  intro σ pack _hComb v j hj hjδ _c _S _hle
  have hjf := j_lt_f_of_le_deltaF_mul hfpos hdeltaFn hjδ
  have hjmn : j ≤ m * n :=
    le_trans (Nat.le_of_lt hjf) (Nat.le_trans hfm (Nat.le_mul_of_pos_right m hn))
  have heq :=
    packSemanticIntrusionCountF_eq_onesAboveBottom (m := m) (n := n) (f := f) hn hfm (hf := hf)
      (σ := σ) (pack := pack) (hcol σ pack) (hrow σ pack) v j
  set cMark := monotoneColumnSumsOfBool hn
      (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have hzero : onesAboveBottom cMark σ f = 0 :=
    onesAboveBottom_eq_zero_of_scrambledColSum_lt cMark σ f fun col =>
      Nat.lt_of_le_of_lt
        (scrambledColSum_le_j_of_topJMarking hn pack (hcol σ pack) v j hj hjmn col)
        hjf
  rw [heq, hzero, Nat.cast_zero]
  exact mul_pos hepsF (by exact_mod_cast hj)

theorem HasPackSemanticPropertyF.of_combinatorial_and_fringeClose {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) {deltaF epsF : ℝ}
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    (hdecode : MiddleStageFringeDecodeHyp m n f hf hn deltaF)
    (hclose : FringePropertyFClosingHyp m n f hn hf hfm deltaF epsF)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hComb : HasCombinatorialPropertyF hf σ deltaF epsF) :
    HasPackSemanticPropertyF hn pack f hfm deltaF epsF :=
  (CombinatorialToMatrixObligationF.of_fringeDecodeHyp_and_close (m := m) (n := n) (f := f)
      (hf := hf) (hfm := hfm) (deltaF := deltaF) (epsF := epsF) hn hcol hrow hdecode hclose).matrixF
    σ pack hComb

theorem CombinatorialToMatrixObligationF.of_columnSortNetwork_rowScramble {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    CombinatorialToMatrixObligationF m n f hn hf hfm deltaF epsF :=
  CombinatorialToMatrixObligationF.of_fringeDecodeHyp_and_close (m := m) (n := n) (f := f)
    (hf := hf) (hfm := hfm) (deltaF := deltaF) (epsF := epsF) hn hcol hrow
    (MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble (m := m) (n := n) (f := f) (hf := hf)
      hn hfm (deltaF := deltaF))
    (FringePropertyFClosingHyp.of_idealColumnSort_rowScramble (m := m) (n := n) (f := f) (hf := hf)
      hn hfm hfpos (deltaF := deltaF) (epsF := epsF) hdeltaFn hepsF hcol hrow)

theorem MatrixBridgeFResidual.of_columnSortNetwork_rowScramble_discharged {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    MatrixBridgeFResidual m n f hf hn hfm deltaF epsF where
  ideal_column_sort := hcol
  row_scramble_correct := hrow
  middle_stage_fringe_decode :=
    MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble (m := m) (n := n) (f := f) (hf := hf)
      hn hfm (deltaF := deltaF)
  fringe_property_f_close :=
    FringePropertyFClosingHyp.of_idealColumnSort_rowScramble (m := m) (n := n) (f := f) (hf := hf)
      hn hfm hfpos (deltaF := deltaF) (epsF := epsF) hdeltaFn hepsF hcol hrow

theorem CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {epsB deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble) :
    CombinatorialToMatrixObligation m n f hn hf hfm epsB deltaF epsF :=
  CombinatorialToMatrixObligation.of_split
    (CombinatorialToMatrixObligationB.of_columnSortNetwork_rowScramble hn hcol hrow)
    (CombinatorialToMatrixObligationF.of_columnSortNetwork_rowScramble hn hfm hfpos hdeltaFn hepsF hcol
      hrow)

theorem deltaF_mul_n_lt_one_params7_n16 :
    (invariant7.deltaF : ℝ) * (16 : ℝ) < 1 := by
  unfold invariant7
  norm_num

theorem deltaF_mul_n_lt_one_invariant7 {n : Nat}
    (hn : (invariant7.deltaF : ℝ) * (n : ℝ) < 1) :
    (invariant7.deltaF : ℝ) * (n : ℝ) < 1 :=
  hn

theorem CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble_all_packs
    {m n f : Nat} {hf : Even f} (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f)
    {epsB deltaF epsF : ℝ} (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF) :
    CombinatorialToMatrixObligation m n f hn hf hfm epsB deltaF epsF :=
  CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble hn hfm hfpos hdeltaFn hepsF
    (IdealColumnSort.all_packs hn) (RowScrambleCorrect.all_packs_forall hn)

theorem CombinatorialToMatrixObligation.of_params7_m100_n16_bridge {f : Nat} {hf : Even f}
    (hfm : f ≤ 100) (hfpos : 0 < f) {epsB deltaF epsF : ℝ} (hepsF : 0 < epsF)
    (hdeltaF : deltaF = invariant7.deltaF) :
    CombinatorialToMatrixObligation 100 16 f (by norm_num : 0 < 16) hf hfm epsB deltaF epsF := by
  subst hdeltaF
  exact CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble_all_packs
    (by norm_num : 0 < 16) hfm hfpos deltaF_mul_n_lt_one_params7_n16 hepsF

theorem CombinatorialToMatrixObligation.of_invariant7_geometry_bridge {g : ScrambleGeometry}
    {f : Nat} {hf : Even f} (hfm : f ≤ g.m) (hfpos : 0 < f) {epsB deltaF epsF : ℝ}
    (hepsF : 0 < epsF) (hdeltaF : deltaF = invariant7.deltaF)
    (hdeltaFn : (invariant7.deltaF : ℝ) * (g.n : ℝ) < 1) :
    CombinatorialToMatrixObligation g.m g.n f (scrambleGeometry_hn g) hf hfm epsB deltaF epsF := by
  subst hdeltaF
  exact CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble_all_packs
    (scrambleGeometry_hn g) hfm hfpos hdeltaFn hepsF

/-! **Semantic F without combinatorial F** (`δ_F·n < 1` closing ignores `hComb`) -/

/-- Under `δ_F·n < 1`, semantic Property F holds for every pack (no combinatorial F needed). -/
theorem HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn {m n f : Nat}
    {hf : Even f} (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ) :
    HasPackSemanticPropertyF hn pack f hfm deltaF epsF := by
  rw [HasPackSemanticPropertyF_iff]
  intro v j hj hjδ
  have hjf := j_lt_f_of_le_deltaF_mul hfpos hdeltaFn hjδ
  have hjmn : j ≤ m * n :=
    le_trans (Nat.le_of_lt hjf) (Nat.le_trans hfm (Nat.le_mul_of_pos_right m hn))
  have heq :=
    packSemanticIntrusionCountF_eq_onesAboveBottom (m := m) (n := n) (f := f) hn hfm (hf := hf)
      (σ := σ) (pack := pack) (hcol σ pack) (hrow σ pack) v j
  set cMark := monotoneColumnSumsOfBool hn
      (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have hzero : onesAboveBottom cMark σ f = 0 :=
    onesAboveBottom_eq_zero_of_scrambledColSum_lt cMark σ f fun col =>
      Nat.lt_of_le_of_lt
        (scrambledColSum_le_j_of_topJMarking hn pack (hcol σ pack) v j hj hjmn col)
        hjf
  rw [heq, hzero, Nat.cast_zero]
  exact mul_pos hepsF (by exact_mod_cast hj)

/-- Canonical pack: semantic F from `δ_F·n < 1` alone. -/
theorem HasPackSemanticPropertyF_canonical_of_deltaFn {m n f : Nat} {hf : Even f}
    (hn : 0 < n) (hfm : f ≤ m) (hfpos : 0 < f) {deltaF epsF : ℝ}
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hepsF : 0 < epsF) (σ : Scramble m n) :
    HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm deltaF epsF :=
  HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn (hf := hf) hn hfm hfpos
    hdeltaFn hepsF (IdealColumnSort.all_packs hn) (RowScrambleCorrect.all_packs_forall hn)
    (canonicalSortScrambleSortPack m n hn σ)

end Chvatal
