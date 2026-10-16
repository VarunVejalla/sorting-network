import OddEvenMerge64

/-! Cross-layer invariant for merging unequal sorted runs. -/

namespace Chvatal.PacketAlignment

private theorem monotone_fin_of_adjacent_local {N : Nat} {α : Type} [Preorder α]
    (f : Fin N → α) (hN : 1 < N)
    (hstep : ∀ i : Fin (N - 1),
      f ⟨i.val, by have hi := i.isLt; omega⟩ ≤
        f ⟨i.val + 1, by have hi := i.isLt; omega⟩) :
    Monotone f := by
  let g : Nat → α := fun i => f ⟨min i (N - 1), by omega⟩
  have hg : ∀ i, g i ≤ g (i + 1) := by
    intro i
    by_cases hi : i < N - 1
    · have hnext : i + 1 ≤ N - 1 := by omega
      simpa [g, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hnext] using
        hstep ⟨i, hi⟩
    · have hi' : N - 1 ≤ i := by omega
      have hnext : N - 1 ≤ i + 1 := by omega
      simp [g, Nat.min_eq_right hi', Nat.min_eq_right hnext]
  have hmono : Monotone g := monotone_nat_of_le_succ hg
  intro a b hab
  have ha : min a.val (N - 1) = a.val := Nat.min_eq_left (by have := a.isLt; omega)
  have hb : min b.val (N - 1) = b.val := Nat.min_eq_left (by have := b.isLt; omega)
  simpa [g, ha, hb] using hmono (Fin.le_iff_val_le_val.mp hab)

/-- Interleave an even lane of length `L` and an odd lane of length `L-1`,
then compare each odd output with the next even output. -/
def unequalCorrectedInterleave {L : Nat} (hL : 2 ≤ L) {α : Type} [LinearOrder α]
    (E : Fin L → α) (O : Fin (L - 1) → α)
    (j : Fin (2 * L - 1)) : α := by
  have hj := j.isLt
  have hdiv : j.val % 2 + 2 * (j.val / 2) = j.val := Nat.mod_add_div _ _
  by_cases heven : j.val % 2 = 0
  · by_cases hz : j.val = 0
    · exact E ⟨0, by omega⟩
    · exact max (O ⟨j.val / 2 - 1, by omega⟩) (E ⟨j.val / 2, by omega⟩)
  · exact min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩)

/-- The uneven correction layer sorts whenever the two parity lanes are
sorted, the even lane is below the odd lane at matching ranks, and the odd
lane is below the even lane two ranks later. -/
theorem unequalCorrectedInterleave_sorted {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ (i : Nat) (hi : i + 1 < L),
      E ⟨i, by omega⟩ ≤ O ⟨i, by omega⟩)
    (hshift : ∀ (i : Nat) (hi : i + 2 < L),
      O ⟨i, by omega⟩ ≤ E ⟨i + 2, by omega⟩) :
    Monotone (unequalCorrectedInterleave hL E O) := by
  apply monotone_fin_of_adjacent_local _ (by omega)
  intro j
  have hj : j.val < 2 * L - 1 := by have := j.isLt; omega
  have hdiv : j.val % 2 + 2 * (j.val / 2) = j.val := by omega
  by_cases heven : j.val % 2 = 0
  · by_cases hz : j.val = 0
    · have hnext : j.val + 1 < 2 * L - 1 := by omega
      have hnextOdd : (j.val + 1) % 2 ≠ 0 := by omega
      have hE01 : E ⟨0, by omega⟩ ≤ E ⟨1, by omega⟩ := by
        apply hE
        exact Fin.mk_le_mk.mpr (by omega)
      have hEO0 := hEO 0 (by omega)
      have hcur : unequalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
          E ⟨0, by omega⟩ := by
        simp [unequalCorrectedInterleave, heven, hz]
      have hnextOut : unequalCorrectedInterleave hL E O ⟨j.val + 1, hnext⟩ =
          min (O ⟨0, by omega⟩) (E ⟨1, by omega⟩) := by
        have hq : (j.val + 1) / 2 = 0 := by omega
        simp [unequalCorrectedInterleave, hnextOdd, hq]
      rw [hcur, hnextOut]
      exact le_min hEO0 hE01
    · have hi : 0 < j.val / 2 := by omega
      have hji : j.val = 2 * (j.val / 2) := by omega
      have hnext : j.val + 1 < 2 * L - 1 := by omega
      have hnextOdd : (j.val + 1) % 2 ≠ 0 := by omega
      have hOstep : O ⟨j.val / 2 - 1, by omega⟩ ≤ O ⟨j.val / 2, by omega⟩ :=
        hO (Fin.mk_le_mk.mpr (by omega))
      have hEstep : E ⟨j.val / 2, by omega⟩ ≤ E ⟨j.val / 2 + 1, by omega⟩ :=
        hE (Fin.mk_le_mk.mpr (by omega))
      have hcross1 := hshift (j.val / 2 - 1) (by omega)
      have hcross2 := hEO (j.val / 2) (by omega)
      have hidx : (⟨j.val / 2 - 1 + 2, by omega⟩ : Fin L) = ⟨j.val / 2 + 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hidx] at hcross1
      have hcur : unequalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
          max (O ⟨j.val / 2 - 1, by omega⟩) (E ⟨j.val / 2, by omega⟩) := by
        simp [unequalCorrectedInterleave, heven, hz]
      have hnextOut : unequalCorrectedInterleave hL E O ⟨j.val + 1, hnext⟩ =
          min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
        have hq : (j.val + 1) / 2 = j.val / 2 := by omega
        simp [unequalCorrectedInterleave, hnextOdd, hq]
      rw [hcur, hnextOut]
      exact max_le (le_min hOstep hcross1) (le_min hcross2 hEstep)
  · have hnext : j.val + 1 < 2 * L - 1 := by omega
    have hnextEven : (j.val + 1) % 2 = 0 := by omega
    have hz : j.val + 1 ≠ 0 := by omega
    have hji : j.val = 2 * (j.val / 2) + 1 := by omega
    have hcur : unequalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
        min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
      simp [unequalCorrectedInterleave, heven]
    have hnextOut : unequalCorrectedInterleave hL E O ⟨j.val + 1, hnext⟩ =
        max (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
      have hq : (j.val + 1) / 2 = j.val / 2 + 1 := by omega
      simp [unequalCorrectedInterleave, hnextEven, hz, hq]
    rw [hcur, hnextOut]
    exact (min_le_left _ _).trans (le_max_left _ _)

/-- Number of entries in a monotone profile that meet a value threshold. -/
def unequalThresholdCount {N : Nat} {α : Type} [LinearOrder α]
    (f : Fin N → α) (t : α) : Nat := Fintype.card {i : Fin N // t ≤ f i}

private theorem unequalThresholdCount_lower {N : Nat} {α : Type}
    [LinearOrder α] (f : Fin N → α) (hf : Monotone f)
    (i : Fin N) (t : α) (hit : t ≤ f i) :
    N - i.val ≤ unequalThresholdCount f t := by
  classical
  let emb : Fin (N - i.val) → {j : Fin N // t ≤ f j} := fun k =>
    ⟨⟨i.val + k.val, by have hk := k.isLt; omega⟩,
      hit.trans (hf (Fin.mk_le_mk.mpr (by omega)))⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun x : {j : Fin N // t ≤ f j} => x.1.val) hab
    dsimp [emb] at hv
    omega
  have hcard := Fintype.card_le_of_injective emb hemb
  simpa [unequalThresholdCount] using hcard

private theorem unequalThresholdCount_upper {N : Nat} {α : Type}
    [LinearOrder α] (f : Fin N → α) (hf : Monotone f)
    (i : Fin N) (t : α) (below : f i < t) :
    unequalThresholdCount f t ≤ N - (i.val + 1) := by
  classical
  let emb : {j : Fin N // t ≤ f j} → Fin (N - (i.val + 1)) := fun j =>
    ⟨j.1.val - (i.val + 1), by
      have hafter : i.val < j.1.val := by
        by_contra hnot
        have hjle : j.1.val ≤ i.val := by omega
        have hji : j.1 ≤ i := Fin.mk_le_mk.mpr hjle
        have hmono := hf hji
        exact (not_le_of_gt below) (j.2.trans hmono)
      have hj := j.1.isLt
      omega⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val hab
    have ha : i.val < a.1.val := by
      by_contra hnot
      have hai : a.1 ≤ i := Fin.mk_le_mk.mpr (by omega : a.1.val ≤ i.val)
      have hmono := hf hai
      exact (not_le_of_gt below) (a.2.trans hmono)
    have hb : i.val < b.1.val := by
      by_contra hnot
      have hbi : b.1 ≤ i := Fin.mk_le_mk.mpr (by omega : b.1.val ≤ i.val)
      have hmono := hf hbi
      exact (not_le_of_gt below) (b.2.trans hmono)
    dsimp [emb] at hv
    omega
  have hcard := Fintype.card_le_of_injective emb hemb
  simpa [unequalThresholdCount] using hcard

/-- A threshold-count gap of one on both sides gives the two cross-rank
inequalities required by the unequal correction layer. -/
theorem unequal_cross_bounds_of_threshold_gap {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEcount : ∀ t, unequalThresholdCount E t ≤ unequalThresholdCount O t + 1)
    (hOcount : ∀ t, unequalThresholdCount O t ≤ unequalThresholdCount E t + 1) :
    (∀ (i : Nat) (hi : i + 1 < L),
      E ⟨i, by omega⟩ ≤ O ⟨i, by omega⟩) ∧
    (∀ (i : Nat) (hi : i + 2 < L),
      O ⟨i, by omega⟩ ≤ E ⟨i + 2, by omega⟩) := by
  constructor
  · intro i hi
    let e : Fin L := ⟨i, by omega⟩
    let o : Fin (L - 1) := ⟨i, by omega⟩
    by_contra hnot
    have hbad : O o < E e := lt_of_not_ge hnot
    have hlow := unequalThresholdCount_lower E hE e (E e) le_rfl
    have hupp := unequalThresholdCount_upper O hO o (E e) hbad
    have hcount := hEcount (E e)
    simp [unequalThresholdCount, e, o] at hlow hupp hcount
    omega
  · intro i hi
    let o : Fin (L - 1) := ⟨i, by omega⟩
    let e : Fin L := ⟨i + 2, by omega⟩
    by_contra hnot
    have hbad : E e < O o := lt_of_not_ge hnot
    have hlow := unequalThresholdCount_lower O hO o (O o) le_rfl
    have hupp := unequalThresholdCount_upper E hE e (O o) hbad
    have hcount := hOcount (O o)
    simp [unequalThresholdCount, e, o] at hlow hupp hcount
    omega

/-- The one-layer correction used after merging parity lanes of lengths `L`
and `L-1`. Comparator `i` joins odd wire `2*i+1` to its following even wire
`2*i+2`; these pairs are disjoint. -/
def unequalCorrectionComparator {L : Nat} (hL : 2 ≤ L)
    (i : Fin (L - 1)) : Comparator (2 * L - 1) :=
  ⟨⟨2 * i.val + 1, by have hi := i.isLt; omega⟩,
   ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩,
   Fin.mk_lt_mk.mpr (by omega)⟩

def unequalCorrectionLayer {L : Nat} (hL : 2 ≤ L) :
    ComparatorNetwork (2 * L - 1) where
  comparators := (List.finRange (L - 1)).map (unequalCorrectionComparator hL)

theorem unequalCorrectionLayer_parallel {L : Nat} (hL : 2 ≤ L) :
    IsParallelLayer (unequalCorrectionLayer hL).comparators := by
  unfold IsParallelLayer unequalCorrectionLayer
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {i j} hij => ?_
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  simp only [Comparator.overlaps, Fin.ext_iff]
  simp only [unequalCorrectionComparator]
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem unequalCorrectionLayer_depth_le {L : Nat} (hL : 2 ≤ L) :
    (unequalCorrectionLayer hL).depth ≤ 1 := by
  apply depth_le_of_decomposition (unequalCorrectionLayer hL)
    [(unequalCorrectionLayer hL).comparators]
  constructor
  · simp only [List.mem_singleton]
    intro layer hlayer
    simpa [hlayer] using unequalCorrectionLayer_parallel hL
  · simp

def unequalInterleave {L : Nat} {α : Type} (E : Fin L → α)
    (O : Fin (L - 1) → α) : Fin (2 * L - 1) → α := fun j =>
  if h : j.val % 2 = 0 then E ⟨j.val / 2, by have hj := j.isLt; omega⟩
  else O ⟨j.val / 2, by
    have hj := j.isLt
    have hm := Nat.mod_lt j.val (by decide : 0 < 2)
    have hmod : j.val % 2 = 1 := by omega
    have hdiv : j.val % 2 + 2 * (j.val / 2) = j.val := Nat.mod_add_div _ _
    have hj' : 2 * (j.val / 2) + 1 = j.val := by omega
    have hjlt : j.val < 2 * (L - 1) := by omega
    have hdivle : 2 * (j.val / 2) ≤ j.val := by rw [← hdiv]; omega
    have hjbound : j.val / 2 < L - 1 := by omega
    exact hjbound⟩

theorem unequalInterleave_odd {L : Nat} (hL : 2 ≤ L)
    {α : Type} (E : Fin L → α) (O : Fin (L - 1) → α)
    (i : Fin (L - 1)) :
    unequalInterleave E O ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ = O i := by
  have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
  unfold unequalInterleave
  simp only [dif_neg hodd]
  apply congrArg O
  apply Fin.ext
  simp
  omega

theorem unequalInterleave_even_succ {L : Nat} (hL : 2 ≤ L)
    {α : Type} (E : Fin L → α) (O : Fin (L - 1) → α)
    (i : Fin (L - 1)) :
    unequalInterleave E O ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ =
      E ⟨i.val + 1, by have hi := i.isLt; omega⟩ := by
  have heven : (2 * i.val + 2) % 2 = 0 := by omega
  unfold unequalInterleave
  simp only [dif_pos heven]
  apply congrArg E
  apply Fin.ext
  simp

private theorem unequal_foldl_parallel_at {n : Nat} {α : Type} [LinearOrder α]
    (cs : List (Comparator n)) (hpar : IsParallelLayer cs)
    (c : Comparator n) (hc : c ∈ cs) (v : Fin n → α) (p : Fin n)
    (hp : p = c.i ∨ p = c.j) :
    cs.foldl (fun acc c => c.apply acc) v p = c.apply v p := by
  induction cs generalizing v with
  | nil => simp at hc
  | cons d ds ih =>
    rcases List.pairwise_cons.mp hpar with ⟨hhead, htail⟩
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · have houtside : ∀ e ∈ ds, p ≠ e.i ∧ p ≠ e.j := by
        intro e he
        rcases hp with hp | hp
        · subst p
          exact ⟨fun h => hhead e he (Or.inl h),
            fun h => hhead e he (Or.inr (Or.inl h))⟩
        · subst p
          exact ⟨fun h => hhead e he (Or.inr (Or.inr (Or.inl h))),
            fun h => hhead e he (Or.inr (Or.inr (Or.inr h)))⟩
      simp only [List.foldl_cons]
      rw [foldl_comparators_outside ds (Comparator.apply c v) p houtside]
    · have hdc : ¬ d.overlaps c := hhead c hc
      have hdi : c.i ≠ d.i ∧ c.i ≠ d.j := by
        constructor <;> intro h
        · exact hdc (Or.inl h.symm)
        · exact hdc (Or.inr (Or.inr (Or.inl h.symm)))
      have hdj : c.j ≠ d.i ∧ c.j ≠ d.j := by
        constructor <;> intro h
        · exact hdc (Or.inr (Or.inl h.symm))
        · exact hdc (Or.inr (Or.inr (Or.inr h.symm)))
      simp only [List.foldl_cons]
      rw [ih htail hc (Comparator.apply d v)]
      rcases hp with rfl | rfl <;> simp [Comparator.apply, hdi, hdj]

/-- The actual correction network sends each odd wire to the minimum of its
odd-lane value and the following even-lane value. -/
theorem unequalCorrectionLayer_exec_odd {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α)
    (i : Fin (L - 1)) :
    (unequalCorrectionLayer hL).exec (unequalInterleave E O)
      ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ =
        min (O i) (E ⟨i.val + 1, by have hi := i.isLt; omega⟩) := by
  let c := unequalCorrectionComparator hL i
  have hc : c ∈ (unequalCorrectionLayer hL).comparators := by
    simp [unequalCorrectionLayer, c]
  have hleft : c.i = ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [c, unequalCorrectionComparator]
  have hright : c.j = ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [c, unequalCorrectionComparator]
  have hvalLeft : (unequalInterleave E O)
      ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ = O i :=
    unequalInterleave_odd hL E O i
  have hvalRight : (unequalInterleave E O)
      ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ =
        E ⟨i.val + 1, by have hi := i.isLt; omega⟩ :=
    unequalInterleave_even_succ hL E O i
  have hrun := unequal_foldl_parallel_at _ (unequalCorrectionLayer_parallel hL)
    c hc (unequalInterleave E O) c.i (Or.inl rfl)
  rw [hleft] at hrun
  have hji : c.j ≠ c.i := ne_of_gt c.h
  simpa [ComparatorNetwork.exec, c, Comparator.apply, hji, hleft, hright,
    hvalLeft, hvalRight] using hrun

/-- The even wire after each correction comparator receives the matching
maximum. -/
theorem unequalCorrectionLayer_exec_even {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α)
    (i : Fin (L - 1)) :
    (unequalCorrectionLayer hL).exec (unequalInterleave E O)
      ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ =
        max (O i) (E ⟨i.val + 1, by have hi := i.isLt; omega⟩) := by
  let c := unequalCorrectionComparator hL i
  have hc : c ∈ (unequalCorrectionLayer hL).comparators := by
    simp [unequalCorrectionLayer, c]
  have hleft : c.i = ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [c, unequalCorrectionComparator]
  have hright : c.j = ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [c, unequalCorrectionComparator]
  have hvalLeft : (unequalInterleave E O)
      ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ = O i :=
    unequalInterleave_odd hL E O i
  have hvalRight : (unequalInterleave E O)
      ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ =
        E ⟨i.val + 1, by have hi := i.isLt; omega⟩ :=
    unequalInterleave_even_succ hL E O i
  have hrun := unequal_foldl_parallel_at _ (unequalCorrectionLayer_parallel hL)
    c hc (unequalInterleave E O) c.j (Or.inr rfl)
  rw [hright] at hrun
  have hji : c.j ≠ c.i := ne_of_gt c.h
  simpa [ComparatorNetwork.exec, c, Comparator.apply, hji, hleft, hright,
    hvalLeft, hvalRight] using hrun

theorem unequalCorrectionLayer_exec_first {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α) :
    (unequalCorrectionLayer hL).exec (unequalInterleave E O)
      (⟨0, by omega⟩ : Fin (2 * L - 1)) = E ⟨0, by omega⟩ := by
  let z : Fin (2 * L - 1) := ⟨0, by omega⟩
  have houtside : ∀ c ∈ (unequalCorrectionLayer hL).comparators,
      z ≠ c.i ∧ z ≠ c.j := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
    have hilt := i.isLt
    simp only [unequalCorrectionComparator]
    constructor <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp [z] at hv <;> omega
  have hkeep := foldl_comparators_outside (unequalCorrectionLayer hL).comparators
    (unequalInterleave E O) z houtside
  simpa [ComparatorNetwork.exec, unequalInterleave, z] using hkeep

/-- The concrete correction network's full output is the min/max interleave
of the two sorted parity lanes. -/
theorem unequalCorrectionLayer_exec_eq {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α) :
    (unequalCorrectionLayer hL).exec (unequalInterleave E O) =
      unequalCorrectedInterleave hL E O := by
  funext j
  have hj := j.isLt
  by_cases hz : j.val = 0
  · have hj0 : j = (⟨0, by omega⟩ : Fin (2 * L - 1)) := Fin.ext hz
    rw [hj0]
    simpa [unequalCorrectedInterleave] using unequalCorrectionLayer_exec_first hL E O
  · by_cases heven : j.val % 2 = 0
    · let i : Fin (L - 1) := ⟨j.val / 2 - 1, by omega⟩
      have hdiv := Nat.mod_add_div j.val 2
      have hq : j.val / 2 = i.val + 1 := by
        rw [heven] at hdiv
        have hpos : 0 < j.val / 2 := by omega
        change j.val / 2 = (j.val / 2 - 1) + 1
        omega
      have hdecomp : j.val = 2 * i.val + 2 := by rw [heven] at hdiv; omega
      have hq' : (2 * i.val + 2) / 2 = i.val + 1 := by omega
      have hji : j = ⟨2 * i.val + 2, by have hi := i.isLt; omega⟩ :=
        Fin.ext (by simp; exact hdecomp)
      rw [hji]
      have hrun := unequalCorrectionLayer_exec_even hL E O i
      simpa [unequalCorrectedInterleave, heven, hz, hq'] using hrun
    · let i : Fin (L - 1) := ⟨j.val / 2, by omega⟩
      have hq : j.val / 2 = i.val := rfl
      have hmod : j.val % 2 = 1 := by
        have hm := Nat.mod_lt j.val (by decide : 0 < 2)
        omega
      have hdecomp : j.val = 2 * i.val + 1 := by
        have hdiv := Nat.mod_add_div j.val 2
        rw [hmod] at hdiv
        omega
      have hq' : (2 * i.val + 1) / 2 = i.val := by omega
      have hji : j = ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ :=
        Fin.ext (by simp; exact hdecomp)
      rw [hji]
      have hrun := unequalCorrectionLayer_exec_odd hL E O i
      simpa [unequalCorrectedInterleave, heven, hq'] using hrun

/-- The actual unequal correction layer sorts whenever its two monotone
parity lanes have threshold counts within one at every value. -/
theorem unequalCorrectionLayer_sorts_of_threshold_gap {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E : Fin L → α) (O : Fin (L - 1) → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEcount : ∀ t, unequalThresholdCount E t ≤ unequalThresholdCount O t + 1)
    (hOcount : ∀ t, unequalThresholdCount O t ≤ unequalThresholdCount E t + 1) :
    Monotone ((unequalCorrectionLayer hL).exec (unequalInterleave E O)) := by
  rw [unequalCorrectionLayer_exec_eq]
  exact unequalCorrectedInterleave_sorted hL E O hE hO
    (unequal_cross_bounds_of_threshold_gap hL E O hE hO hEcount hOcount).1
    (unequal_cross_bounds_of_threshold_gap hL E O hE hO hEcount hOcount).2

end Chvatal.PacketAlignment
