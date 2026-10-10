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

/-- The false-set cardinality is a `0*1*` witness for a monotone Boolean sequence. -/
lemma Monotone.bool_pattern_at_card {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    let k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
    (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
      (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  dsimp only
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_def]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega

/-! **Network Cast** -/

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

/-- After column sort, the region count equals `∑ⱼ (colSumⱼ - i)`. -/
theorem matrixOnesCountInRegion_colSort_eq_sum_columnSub {m n : Nat} (hn : 0 < n) (i : Nat)
    (him : i ≤ m) (v : Fin (m * n) → Bool) :
    matrixOnesCountInRegion hn ((columnSortNetwork m n hn).exec v) i =
      ∑ j : Fin n, (matrixColumnTrueCount hn j v - i) := by
  rw [matrixOnesCountInRegion_eq_sum_columnOnesAboveBottom]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [matrixColumnOnesAboveBottom_eq_sub hn j _ i him fun hrs => columnSortNetwork_columnMonotone hn v j hrs,
    matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn)]

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
  rw [Bool.eq_iff_iff, monotoneMatrixBool_matrixWire, mem_monotoneRowOnes_iff]
  show _ ↔ m - r.val ≤ matrixColumnTrueCount hn j v
  unfold matrixColumnTrueCount
  have hr := r.isLt
  constructor
  · intro h
    have hsub : Finset.Ici r ⊆ Finset.univ.filter fun s => v (matrixWire m n s j) = true :=
      fun s hs => by
        simpa using Bool.le_iff_imp.mp (hcm j (Finset.mem_Ici.mp hs)) h
    simpa using Finset.card_le_card hsub
  · intro h
    by_contra hf
    have hsub : (Finset.univ.filter fun s => v (matrixWire m n s j) = true) ⊆ Finset.Ioi r :=
      fun s hs => by
        by_contra hs'
        exact hf (Bool.le_iff_imp.mp (hcm j (not_lt.mp (Finset.mem_Ioi.not.mp hs')))
          (Finset.mem_filter.mp hs).2)
    have := Finset.card_le_card hsub
    simp at this
    omega

theorem scrambledColSum_eq_matrixColumnTrueCount {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (c : MonotoneColumnSums m n) (j : Fin n) :
    scrambledColSum c σ j =
      matrixColumnTrueCount hn j (monotoneMatrixBool hn c ∘ (rowScrambleWirePerm m n hn σ).symm) := by
  classical
  unfold scrambledColSum
  rw [matrixColumnTrueCount_eq_sum hn j]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h : (monotoneMatrixBool hn c ∘ (rowScrambleWirePerm m n hn σ).symm) (matrixWire m n r j) =
      true ↔ j ∈ scrambledRowOnes c σ r := by
    simp only [Function.comp, rowScrambleWirePerm_symm_apply, decide_eq_true_iff,
      monotoneMatrixBool_matrixWire, scrambledRowOnes, Finset.mem_image]
    exact ⟨fun hj => ⟨_, hj, Equiv.apply_symm_apply _ _⟩, fun ⟨j0, hj0, e⟩ => by
      simpa [← e] using hj0⟩
  simp only [h]

/-- After the semantic map on a Boolean marking, the region count at level `i ≤ m` is the
combinatorial `onesAboveBottom` of the post-first-sort column sums (Property B and F decode). -/
theorem matrixOnesCountInRegion_semanticExec {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (v : Fin (m * n) → Bool) (i : Nat) (him : i ≤ m) :
    matrixOnesCountInRegion hn (semanticExec hn σ v) i =
      onesAboveBottom (monotoneColumnSumsOfBool hn ((columnSortNetwork m n hn).exec v)) σ i := by
  set c := monotoneColumnSumsOfBool hn ((columnSortNetwork m n hn).exec v)
  have hu1 : (columnSortNetwork m n hn).exec v = monotoneMatrixBool hn c :=
    monotoneMatrixBool_eq_of_columnMonotone hn _ (columnSortNetwork_columnMonotone hn v)
  rw [semanticExec, matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i him]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scrambledColSum_eq_matrixColumnTrueCount hn σ c j, hu1]

/-! **Top-`j` marking counts (Property F closing)** -/

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

theorem totalColumnOnes_colSort_exec_eq {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) :
    totalColumnOnes (monotoneColumnSumsOfBool hn ((columnSortNetwork m n hn).exec v)) =
      (Finset.univ.filter fun w : Fin (m * n) => v w = true).card := by
  unfold totalColumnOnes monotoneColumnSumsOfBool
  rw [← sum_matrixColumnTrueCount_eq_trueWireCount hn v]
  exact Finset.sum_congr rfl fun j _ =>
    matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn) v

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

theorem HasPackSemanticPropertyB.of_combinatorial_onPipeline {m n : Nat} {epsB : ℝ} (hn : 0 < n)
    (σ : Scramble m n) (hComb : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasPackSemanticPropertyB hn σ epsB := fun v i hi1 him => by
  rw [matrixOnesCountInRegion_semanticExec hn σ _ i him]
  refine hComb _ i ?_ hi1 him
  rw [totalColumnOnes_colSort_exec_eq, largestKeyThreshold01_trueWireCount_eq hn i hi1 him v,
    Nat.mul_comm]

theorem sum_topJ_colSums_eq_j {m n : Nat} (hn : 0 < n) (v : Equiv.Perm (Fin (m * n))) (j : Nat)
    (hjpos : 0 < j) (hjmn : j ≤ m * n) :
    totalColumnOnes (monotoneColumnSumsOfBool hn ((columnSortNetwork m n hn).exec
        fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))) = j := by
  rw [totalColumnOnes_colSort_exec_eq]
  exact topJMarking_trueWireCount_eq j hjpos hjmn v

end Chvatal
