import AKS.Bitonic.Sorts

set_option maxRecDepth 10000

open ComparatorNetwork

namespace Chvatal.PacketAlignment

/-- Comparator execution is monotone in the input values, coordinate by coordinate.
This is the key relation between the even and odd recursive submerges. -/
theorem exec_mono_input {n : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork n) {v w : Fin n → α}
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, net.exec v i ≤ net.exec w i := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v w with
  | nil => exact hvw
  | cons c cs ih =>
      apply ih
      intro i
      simp only [Comparator.apply]
      by_cases hi : i = c.i
      · subst i
        simp only [↓reduceIte]
        exact min_le_min (hvw c.i) (hvw c.j)
      · by_cases hj : i = c.j
        · subst i
          simp only [if_neg hi, ↓reduceIte]
          exact max_le_max (hvw c.i) (hvw c.j)
        · simp only [if_neg hi, if_neg hj]
          exact hvw i

/-- Values on the wires immediately before and after one correction comparator. -/
def correctedLeft {α : Type} [LinearOrder α]
    (E O : Nat → α) (i : Nat) : α :=
  if i = 0 then E 0 else max (O (i - 1)) (E i)

def correctedRight {α : Type} [LinearOrder α]
    (E O : Nat → α) (i : Nat) : α := min (O i) (E (i + 1))
/-- The odd-even correction layer leaves an ordered pair when parity outputs
satisfy the usual same-rank and shifted cross-rank inequalities. -/
theorem correction_pair_ordered {α : Type} [LinearOrder α]
    (E O : Nat → α) (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ i, E i ≤ O i)
    (hshift : ∀ i, 0 < i → O (i - 1) ≤ E (i + 1)) :
    ∀ i, correctedLeft E O i ≤ correctedRight E O i := by
  intro i
  by_cases hi : i = 0
  · subst i
    simp [correctedLeft, correctedRight]
    exact ⟨hEO 0, hE (by omega)⟩
  · simp only [correctedLeft, correctedRight, if_neg hi]
    apply max_le
    · exact le_min (hO (by omega)) (hshift i (by omega))
    · exact le_min (hEO i) (hE (by omega))

/-- Consecutive corrected pairs are ordered because the middle comparator
places a minimum before its matching maximum. -/
theorem correction_pairs_interleave {α : Type} [LinearOrder α]
    (E O : Nat → α) :
    ∀ i, correctedRight E O i ≤ correctedLeft E O (i + 1) := by
  intro i
  simp [correctedLeft, correctedRight]

/-- The corrected parity outputs form a monotone sequence when each corrected
pair is ordered and consecutive pairs interleave. -/
theorem correction_output_monotone {α : Type} [LinearOrder α]
    (E O : Nat → α) (hpair : ∀ i, correctedLeft E O i ≤ correctedRight E O i)
    (hbetween : ∀ i, correctedRight E O i ≤ correctedLeft E O (i + 1)) :
    Monotone (fun j : Nat =>
      if j % 2 = 0 then correctedLeft E O (j / 2)
      else correctedRight E O (j / 2)) := by
  intro a b hab
  have hstep : ∀ n, (if n % 2 = 0 then correctedLeft E O (n / 2)
      else correctedRight E O (n / 2)) ≤
      (if (n + 1) % 2 = 0 then correctedLeft E O ((n + 1) / 2)
      else correctedRight E O ((n + 1) / 2)) := by
    intro n
    by_cases hn : n % 2 = 0
    · have hnext : (n + 1) % 2 = 1 := by omega
      rw [if_pos hn, if_neg (by omega)]
      have hdiv : (n + 1) / 2 = n / 2 := by omega
      rw [hdiv]
      exact hpair (n / 2)
    · have hnext : (n + 1) % 2 = 0 := by omega
      rw [if_neg hn, if_pos hnext]
      have hdiv : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [hdiv]
      exact hbetween (n / 2)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have heq : a + Nat.succ d = (a + d) + 1 := by omega
    rw [heq]
    have hprev : a ≤ a + d := by omega
    exact (ih hprev).trans (hstep (a + d))

/-- Finite parity profiles extended by the last odd value satisfy the ideal
correction inequalities, including the otherwise unpaired terminal wire. -/
theorem correction_tail_extension_monotone {q : Nat} {α : Type}
    [LinearOrder α] (E O : Fin q → α) (hq : 0 < q)
    (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ i, E i ≤ O i)
    (hshift : ∀ (i : Fin q) (hi : 0 < i.val)
      (hb : i.val + 1 < q), O ⟨i.val - 1, by omega⟩ ≤ E ⟨i.val + 1, by omega⟩) :
    Monotone (fun j : Nat =>
      if j % 2 = 0 then
        correctedLeft (fun n => if hn : n < q then E ⟨n, hn⟩ else O ⟨q - 1, by omega⟩)
          (fun n => if hn : n < q then O ⟨n, hn⟩ else O ⟨q - 1, by omega⟩) (j / 2)
      else
        correctedRight (fun n => if hn : n < q then E ⟨n, hn⟩ else O ⟨q - 1, by omega⟩)
          (fun n => if hn : n < q then O ⟨n, hn⟩ else O ⟨q - 1, by omega⟩) (j / 2)) := by
  let e : Nat → α := fun n => if hn : n < q then E ⟨n, hn⟩ else O ⟨q - 1, by omega⟩
  let o : Nat → α := fun n => if hn : n < q then O ⟨n, hn⟩ else O ⟨q - 1, by omega⟩
  have he : Monotone e := by
    intro a b hab
    by_cases hb : b < q
    · have ha : a < q := by omega
      simp [e, ha, hb]
      exact hE (Fin.mk_le_mk.mpr hab)
    · by_cases ha : a < q
      · simp [e, ha, hb]
        apply (hE (Fin.mk_le_mk.mpr (show a ≤ q - 1 by omega))).trans
        exact hEO ⟨q - 1, by omega⟩
      · simp [e, ha, hb]
  have ho : Monotone o := by
    intro a b hab
    by_cases hb : b < q
    · have ha : a < q := by omega
      simp [o, ha, hb]
      exact hO (Fin.mk_le_mk.mpr hab)
    · by_cases ha : a < q
      · simp [o, ha, hb]
        exact hO (Fin.mk_le_mk.mpr (show a ≤ q - 1 by omega))
      · simp [o, ha, hb]
  have heo : ∀ n, e n ≤ o n := by
    intro n
    by_cases hn : n < q
    · simp [e, o, hn]
      exact hEO ⟨n, hn⟩
    · simp [e, o, hn]
  have hs : ∀ n, 0 < n → o (n - 1) ≤ e (n + 1) := by
    intro n hn
    by_cases hinside : n + 1 < q
    · have h := hshift ⟨n, by omega⟩ hn hinside
      have hprev : n - 1 < q := by omega
      simpa [e, o, hprev, hinside] using h
    · by_cases hnq : n < q
      · have hlast : n + 1 = q := by omega
        have htail : O ⟨n - 1, by omega⟩ ≤ O ⟨q - 1, by omega⟩ := by
          apply hO
          exact Fin.mk_le_mk.mpr (by omega)
        have hprev : n - 1 < q := by omega
        simpa [e, o, hnq, hlast, hprev] using htail
      · by_cases heq : n = q
        · subst n
          have hlast : q - 1 < q := by omega
          simp [e, o, hq, hlast, show ¬ q + 1 < q by omega,
            show ¬ q < q by omega]
        · have htail : n - 1 ≥ q := by omega
          simp [e, o, show ¬ n - 1 < q by omega,
            show ¬ n + 1 < q by omega]
  have hp := correction_pair_ordered e o he ho heo hs
  exact correction_output_monotone e o hp (correction_pairs_interleave e o)

/-- Number of true wires in a Boolean vector. -/
def boolTrueCount {n : Nat} (v : Fin n → Bool) : Nat :=
  Fintype.card {i : Fin n // v i = true}

/-- Reindexing a Boolean vector along a finite-index cast preserves its true
count. -/
theorem boolTrueCount_finCast {m n : Nat} (h : m = n) (v : Fin n → Bool) :
    boolTrueCount (fun i : Fin m => v (Fin.cast h i)) = boolTrueCount v := by
  let e : {i : Fin m // v (Fin.cast h i) = true} ≃ {j : Fin n // v j = true} := {
    toFun := fun i => ⟨Fin.cast h i.1, i.2⟩
    invFun := fun j => ⟨Fin.cast h.symm j.1, by simpa using j.2⟩
    left_inv := fun i => by
      apply Subtype.ext
      simp
    right_inv := fun j => by
      apply Subtype.ext
      simp
  }
  unfold boolTrueCount
  exact Fintype.card_congr e

/-- True entries in a concatenation split into the true entries of each run. -/
theorem boolTrueCount_append {m : Nat} (A B : Fin m → Bool) :
    boolTrueCount (Fin.append A B) = boolTrueCount A + boolTrueCount B := by
  let p : Fin m ⊕ Fin m → Prop
    | Sum.inl i => A i = true
    | Sum.inr i => B i = true
  have hp (s : Fin m ⊕ Fin m) : p s ↔ Fin.append A B (finSumFinEquiv s) = true := by
    cases s with
    | inl i => simp [p]
    | inr i =>
        change (B i = true) ↔ Fin.addCases A B (Fin.natAdd m i) = true
        rw [Fin.addCases_right]
  let e : {i : Fin (m + m) // Fin.append A B i = true} ≃
      (Sum ({i : Fin m // A i = true}) ({i : Fin m // B i = true})) :=
    (finSumFinEquiv.subtypeEquiv hp).symm.trans Equiv.subtypeSum
  unfold boolTrueCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr e

theorem boolTrueCount_halves {m : Nat} (v : Fin (m + m) → Bool) :
    boolTrueCount v = boolTrueCount (fun i : Fin m => v (Fin.castAdd m i)) +
      boolTrueCount (fun i : Fin m => v (Fin.natAdd m i)) := by
  let A := fun i : Fin m => v (Fin.castAdd m i)
  let B := fun i : Fin m => v (Fin.natAdd m i)
  have he : Fin.append A B = v := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  calc
    boolTrueCount v = boolTrueCount (Fin.append A B) := congrArg boolTrueCount he.symm
    _ = boolTrueCount A + boolTrueCount B := boolTrueCount_append A B

private def evenIndexFull (m : Nat) (i : Fin (m + m)) : Fin ((m + m) + (m + m)) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

private def oddIndexFull (m : Nat) (i : Fin (m + m)) : Fin ((m + m) + (m + m)) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

private def evenIndexRun (m : Nat) (i : Fin m) : Fin (m + m) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

private def oddIndexRun (m : Nat) (i : Fin m) : Fin (m + m) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- Even positions of two concatenated runs are the concatenation of their
individual even-position subsequences. -/
theorem evenProjection_append {m : Nat} (v : Fin ((m + m) + (m + m)) → Bool) :
    (fun i : Fin (m + m) => v (evenIndexFull m i)) =
      Fin.append
        (fun i : Fin m => v (Fin.castAdd (m + m) (evenIndexRun m i)))
        (fun i : Fin m => v (Fin.natAdd (m + m) (evenIndexRun m i))) := by
  funext i
  rcases hidx : finSumFinEquiv.symm i with j | j
  · have hi : i = Fin.castAdd m j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    subst i
    simp only [Fin.append_left]
    congr 1 <;> (apply Fin.ext <;> simp [evenIndexFull, evenIndexRun] <;> omega)
  · have hi : i = Fin.natAdd m j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    subst i
    simp only [Fin.append_right]
    congr 1 <;> (apply Fin.ext <;> simp [evenIndexFull, evenIndexRun] <;> omega)

/-- Odd positions of two concatenated runs split in the same way. -/
theorem oddProjection_append {m : Nat} (v : Fin ((m + m) + (m + m)) → Bool) :
    (fun i : Fin (m + m) => v (oddIndexFull m i)) =
      Fin.append
        (fun i : Fin m => v (Fin.castAdd (m + m) (oddIndexRun m i)))
        (fun i : Fin m => v (Fin.natAdd (m + m) (oddIndexRun m i))) := by
  funext i
  rcases hidx : finSumFinEquiv.symm i with j | j
  · have hi : i = Fin.castAdd m j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    subst i
    simp only [Fin.append_left]
    congr 1 <;> (apply Fin.ext <;> simp [oddIndexFull, oddIndexRun] <;> omega)
  · have hi : i = Fin.natAdd m j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    subst i
    simp only [Fin.append_right]
    congr 1 <;> (apply Fin.ext <;> simp [oddIndexFull, oddIndexRun] <;> omega)

theorem boolTrueCount_evenProjection_add {m : Nat}
    (v : Fin ((m + m) + (m + m)) → Bool) :
    boolTrueCount (fun i : Fin (m + m) => v (evenIndexFull m i)) =
      boolTrueCount (fun i : Fin m => v (Fin.castAdd (m + m) (evenIndexRun m i))) +
      boolTrueCount (fun i : Fin m => v (Fin.natAdd (m + m) (evenIndexRun m i))) := by
  rw [evenProjection_append, boolTrueCount_append]

theorem boolTrueCount_oddProjection_add {m : Nat}
    (v : Fin ((m + m) + (m + m)) → Bool) :
    boolTrueCount (fun i : Fin (m + m) => v (oddIndexFull m i)) =
      boolTrueCount (fun i : Fin m => v (Fin.castAdd (m + m) (oddIndexRun m i))) +
      boolTrueCount (fun i : Fin m => v (Fin.natAdd (m + m) (oddIndexRun m i))) := by
  rw [oddProjection_append, boolTrueCount_append]

private theorem monotone_evenIndexRun_count_le_odd {m : Nat}
    (v : Fin (m + m) → Bool) (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (evenIndexRun m i)) ≤
      boolTrueCount (fun i : Fin m => v (oddIndexRun m i)) := by
  change Fintype.card {i : Fin m // v (evenIndexRun m i) = true} ≤
    Fintype.card {i : Fin m // v (oddIndexRun m i) = true}
  apply Fintype.card_le_of_injective
    (fun i : {i : Fin m // v (evenIndexRun m i) = true} =>
      (⟨i.1, by
        have hpos : evenIndexRun m i.1 ≤ oddIndexRun m i.1 := by
          apply Fin.mk_le_mk.mpr
          simp [evenIndexRun, oddIndexRun]
        have h := hv hpos
        cases hv' : v (oddIndexRun m i.1) with
        | false =>
            have : (true : Bool) ≤ false := by simpa [i.2, hv'] using h
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) this)
        | true => simpa [hv']⟩ :
        {i : Fin m // v (oddIndexRun m i) = true}))
    (by
      intro i j hij
      have hval := congrArg
        (fun x : {i : Fin m // v (oddIndexRun m i) = true} => x.1.val) hij
      apply Subtype.ext
      exact Fin.ext (by simpa using hval))

private theorem monotone_oddIndexRun_count_le_even_add_one {m : Nat}
    (v : Fin (m + m) → Bool) (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (oddIndexRun m i)) ≤
      boolTrueCount (fun i : Fin m => v (evenIndexRun m i)) + 1 := by
  let f : {i : Fin m // v (oddIndexRun m i) = true} →
      ({i : Fin m // v (evenIndexRun m i) = true} ⊕ Unit) := fun i =>
    if hi : i.1.val + 1 < m then
      Sum.inl ⟨⟨i.1.val + 1, hi⟩, by
        have hpos : oddIndexRun m i.1 ≤ evenIndexRun m ⟨i.1.val + 1, hi⟩ := by
          apply Fin.mk_le_mk.mpr
          simp [oddIndexRun, evenIndexRun]
        have h := hv hpos
        cases hv' : v (evenIndexRun m ⟨i.1.val + 1, hi⟩) with
        | false =>
            have : (true : Bool) ≤ false := by simpa [i.2, hv'] using h
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) this)
        | true => simpa [hv']⟩
    else Sum.inr Unit.unit
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.1.val + 1 < m <;> by_cases hj : j.1.val + 1 < m
    · simp [f, hi, hj] at hij
      apply Subtype.ext
      exact Fin.ext hij
    · simp [f, hi, hj] at hij
    · simp [f, hi, hj] at hij
    · simp [f, hi, hj] at hij
      apply Subtype.ext
      exact Fin.ext (by have := i.1.isLt; have := j.1.isLt; omega)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, boolTrueCount] using hcard

/-- The two-run parity imbalance, now stated for the physical projections of
the concatenated input. -/
theorem concatenated_two_run_parity_count_gap {m : Nat}
    (v : Fin ((m + m) + (m + m)) → Bool)
    (hA : Monotone (fun i : Fin (m + m) => v (Fin.castAdd (m + m) i)))
    (hB : Monotone (fun i : Fin (m + m) => v (Fin.natAdd (m + m) i))) :
    boolTrueCount (fun i : Fin (m + m) => v (evenIndexFull m i)) ≤
        boolTrueCount (fun i : Fin (m + m) => v (oddIndexFull m i)) ∧
    boolTrueCount (fun i : Fin (m + m) => v (oddIndexFull m i)) ≤
        boolTrueCount (fun i : Fin (m + m) => v (evenIndexFull m i)) + 2 := by
  let A : Fin (m + m) → Bool := fun i => v (Fin.castAdd (m + m) i)
  let B : Fin (m + m) → Bool := fun i => v (Fin.natAdd (m + m) i)
  have hcounts :
      boolTrueCount (fun i : Fin m => A (evenIndexRun m i)) +
          boolTrueCount (fun i : Fin m => B (evenIndexRun m i)) ≤
        boolTrueCount (fun i : Fin m => A (oddIndexRun m i)) +
          boolTrueCount (fun i : Fin m => B (oddIndexRun m i)) ∧
      boolTrueCount (fun i : Fin m => A (oddIndexRun m i)) +
          boolTrueCount (fun i : Fin m => B (oddIndexRun m i)) ≤
        boolTrueCount (fun i : Fin m => A (evenIndexRun m i)) +
          boolTrueCount (fun i : Fin m => B (evenIndexRun m i)) + 2 := by
    constructor
    · exact Nat.add_le_add
        (monotone_evenIndexRun_count_le_odd A hA)
        (monotone_evenIndexRun_count_le_odd B hB)
    · calc
        _ ≤ (boolTrueCount (fun i : Fin m => A (evenIndexRun m i)) + 1) +
              (boolTrueCount (fun i : Fin m => B (evenIndexRun m i)) + 1) :=
          Nat.add_le_add
            (monotone_oddIndexRun_count_le_even_add_one A hA)
            (monotone_oddIndexRun_count_le_even_add_one B hB)
        _ = _ := by omega
  rw [boolTrueCount_evenProjection_add, boolTrueCount_oddProjection_add]
  simpa [A, B] using hcounts

/-- In two ascending runs, each even-position input to the recursive parity
submerge is no larger than the corresponding odd-position input. -/
theorem two_monotone_runs_even_le_odd {m : Nat} {α : Type} [Preorder α]
    (v : Fin ((m + m) + (m + m)) → α)
    (hA : Monotone (fun i : Fin (m + m) => v (Fin.castAdd (m + m) i)))
    (hB : Monotone (fun i : Fin (m + m) => v (Fin.natAdd (m + m) i))) :
    ∀ i : Fin (m + m), v (evenIndexFull m i) ≤ v (oddIndexFull m i) := by
  intro i
  by_cases hleft : i.val < m
  · let j : Fin m := ⟨i.val, hleft⟩
    have he : evenIndexFull m i = Fin.castAdd (m + m) (evenIndexRun m j) := by
      apply Fin.ext
      simp [evenIndexFull, evenIndexRun, j]
    have ho : oddIndexFull m i = Fin.castAdd (m + m) (oddIndexRun m j) := by
      apply Fin.ext
      simp [oddIndexFull, oddIndexRun, j]
    rw [he, ho]
    apply hA
    exact Fin.mk_le_mk.mpr (by simp [evenIndexRun, oddIndexRun])
  · let j : Fin m := ⟨i.val - m, by have := i.isLt; omega⟩
    have hi : i = Fin.natAdd m j := by
      apply Fin.ext
      simp [j]
      omega
    have he : evenIndexFull m i = Fin.natAdd (m + m) (evenIndexRun m j) := by
      apply Fin.ext
      simp [evenIndexFull, evenIndexRun, Fin.natAdd, j]
      omega
    have ho : oddIndexFull m i = Fin.natAdd (m + m) (oddIndexRun m j) := by
      apply Fin.ext
      simp [oddIndexFull, oddIndexRun, Fin.natAdd, j]
      omega
    rw [he, ho]
    apply hB
    exact Fin.mk_le_mk.mpr (by simp [evenIndexRun, oddIndexRun])

/-- Comparator monotonicity transports the pointwise order of the two parity
inputs to the corresponding outputs of any common recursive submerge. -/
theorem common_submerge_even_le_odd {m : Nat} {α : Type} [LinearOrder α]
    (v : Fin ((m + m) + (m + m)) → α) (net : ComparatorNetwork (m + m))
    (hA : Monotone (fun i : Fin (m + m) => v (Fin.castAdd (m + m) i)))
    (hB : Monotone (fun i : Fin (m + m) => v (Fin.natAdd (m + m) i))) :
    ∀ i : Fin (m + m),
      net.exec (fun j => v (evenIndexFull m j)) i ≤
        net.exec (fun j => v (oddIndexFull m j)) i := by
  apply exec_mono_input net
  exact two_monotone_runs_even_le_odd v hA hB

private theorem evenIndexFull_castAdd_eq {m : Nat} (i : Fin m) :
    evenIndexFull m (Fin.castAdd m i) =
      Fin.castAdd (m + m) (evenIndexRun m i) := by
  apply Fin.ext
  simp [evenIndexFull, evenIndexRun]

private theorem oddIndexFull_castAdd_eq {m : Nat} (i : Fin m) :
    oddIndexFull m (Fin.castAdd m i) =
      Fin.castAdd (m + m) (oddIndexRun m i) := by
  apply Fin.ext
  simp [oddIndexFull, oddIndexRun]

private theorem evenIndexFull_natAdd_eq {m : Nat} (i : Fin m) :
    evenIndexFull m (Fin.natAdd m i) =
      Fin.natAdd (m + m) (evenIndexRun m i) := by
  apply Fin.ext
  simp [evenIndexFull, evenIndexRun, Fin.natAdd]
  omega

private theorem oddIndexFull_natAdd_eq {m : Nat} (i : Fin m) :
    oddIndexFull m (Fin.natAdd m i) =
      Fin.natAdd (m + m) (oddIndexRun m i) := by
  apply Fin.ext
  simp [oddIndexFull, oddIndexRun, Fin.natAdd]
  omega

/-- Each parity projection of two sorted runs is itself a concatenation of
two sorted runs: the parity subsequences from each source run. -/
theorem two_monotone_runs_parity_segments_sorted {m : Nat} {α : Type}
    [Preorder α] (v : Fin ((m + m) + (m + m)) → α)
    (hA : Monotone (fun i : Fin (m + m) => v (Fin.castAdd (m + m) i)))
    (hB : Monotone (fun i : Fin (m + m) => v (Fin.natAdd (m + m) i))) :
    (Monotone (fun i : Fin m => v (evenIndexFull m (Fin.castAdd m i))) ∧
      Monotone (fun i : Fin m => v (evenIndexFull m (Fin.natAdd m i))) ∧
      Monotone (fun i : Fin m => v (oddIndexFull m (Fin.castAdd m i))) ∧
      Monotone (fun i : Fin m => v (oddIndexFull m (Fin.natAdd m i)))) := by
  have he : Monotone (evenIndexRun m) := by
    intro i j hij
    exact Fin.mk_le_mk.mpr (by simp [evenIndexRun]; omega)
  have ho : Monotone (oddIndexRun m) := by
    intro i j hij
    exact Fin.mk_le_mk.mpr (by simp [oddIndexRun]; omega)
  constructor
  · intro i j hij
    simpa only [evenIndexFull_castAdd_eq] using hA (he hij)
  constructor
  · intro i j hij
    simpa only [evenIndexFull_natAdd_eq] using hB (he hij)
  constructor
  · intro i j hij
    simpa only [oddIndexFull_castAdd_eq] using hA (ho hij)
  · intro i j hij
    simpa only [oddIndexFull_natAdd_eq] using hB (ho hij)

/-- Recursive-step interface: if a common network sorts every input made of
two monotone runs, then its even and odd parity submerges are monotone on any
input made of two monotone runs. -/
theorem recursive_parity_outputs_sorted {m : Nat} {α : Type} [LinearOrder α]
    (v : Fin ((m + m) + (m + m)) → α) (net : ComparatorNetwork (m + m))
    (hA : Monotone (fun i : Fin (m + m) => v (Fin.castAdd (m + m) i)))
    (hB : Monotone (fun i : Fin (m + m) => v (Fin.natAdd (m + m) i)))
    (ih : ∀ w : Fin (m + m) → α,
      (Monotone (fun i : Fin m => w (Fin.castAdd m i)) ∧
       Monotone (fun i : Fin m => w (Fin.natAdd m i))) →
      Monotone (net.exec w)) :
    Monotone (net.exec (fun i => v (evenIndexFull m i))) ∧
      Monotone (net.exec (fun i => v (oddIndexFull m i)) : Fin (m + m) → α) := by
  obtain ⟨heA, heB, hoA, hoB⟩ :=
    two_monotone_runs_parity_segments_sorted v hA hB
  exact ⟨ih _ ⟨heA, heB⟩, ih _ ⟨hoA, hoB⟩⟩

/-- Monotone Boolean sequences with pointwise `E ≤ O` and at most two extra
true entries in `O` cannot cross across a two-position shift. -/
theorem monotone_bool_shift_of_count_gap {n : Nat} (E O : Fin n → Bool)
    (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ j, E j ≤ O j)
    (hcount : boolTrueCount O ≤ boolTrueCount E + 2) :
    ∀ (i : Fin n) (hi : 0 < i.val) (hbound : i.val + 1 < n),
      O ⟨i.val - 1, by omega⟩ ≤ E ⟨i.val + 1, by omega⟩ := by
  intro i hi hbound
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let r : Fin n := ⟨i.val + 1, by omega⟩
  change O p ≤ E r
  by_cases hp : O p = true
  · by_cases hr : E r = false
    · have hcount3 : boolTrueCount E + 3 ≤ boolTrueCount O := by
        -- The three consecutive positions in O's true support are disjoint
        -- from E's support; all of E's support embeds pointwise into O's.
        have hsurplus : boolTrueCount E + 3 ≤ boolTrueCount O := by
          -- Continue with the explicit injection into O's true support.
          have hOp : O p = true := hp
          have hEr : E r = false := hr
          let loc (t : Fin 3) : Fin n := ⟨i.val - 1 + t.val, by
            have := t.isLt
            omega⟩
          have hloc_inj : Function.Injective loc := by
            intro t u htu
            apply Fin.ext
            have hv := congrArg Fin.val htu
            simp only [loc] at hv
            omega
          have hlocO (t : Fin 3) : O (loc t) = true := by
            have hle : p ≤ loc t := Fin.mk_le_mk.mpr (by omega)
            have h := hO hle
            cases hv : O (loc t) with
            | false => exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hOp, hv] using h))
            | true => rfl
          have hlocE (t : Fin 3) : E (loc t) = false := by
            have hle : loc t ≤ r := Fin.mk_le_mk.mpr (by omega)
            have h := hE hle
            cases hv : E (loc t) with
            | false => rfl
            | true => exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hv, hEr] using h))
          let f : {j : Fin n // E j = true} ⊕ Fin 3 → {j : Fin n // O j = true} :=
            Sum.elim
              (fun j => ⟨j.1, by
                have h := hEO j.1
                rw [j.2] at h
                cases hv : O j.1 with
                | false => exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hv] using h))
                | true => rfl⟩)
              (fun t => ⟨loc t, hlocO t⟩)
          have hf : Function.Injective f := by
            intro a b hab
            cases a with
            | inl x =>
              cases b with
              | inl y =>
                have hv := congrArg Subtype.val hab
                have hxy : x.1 = y.1 := Fin.ext (congrArg Fin.val hv)
                exact congrArg Sum.inl (Subtype.ext hxy)
              | inr t =>
                have hxt : x.1 = loc t := congrArg Subtype.val hab
                have hle : x.1 ≤ loc t := hxt ▸ le_rfl
                have h := hE hle
                rw [x.2, hlocE t] at h
                exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
            | inr t =>
              cases b with
              | inl y =>
                have hty : loc t = y.1 := congrArg Subtype.val hab
                have hle : y.1 ≤ loc t := hty.symm ▸ le_rfl
                have h := hE hle
                rw [y.2, hlocE t] at h
                exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
              | inr u =>
                have htu : loc t = loc u := congrArg Subtype.val hab
                exact congrArg Sum.inr (hloc_inj htu)
          have hcard := Fintype.card_le_of_injective f hf
          simpa [boolTrueCount] using hcard
        exact hsurplus
      have : False := by omega
      exact this.elim
    · have hr' : E r = true := by cases hv : E r <;> simp_all
      simp [hp, hr']
  · have hp' : O p = false := by cases hv : O p <;> simp_all
    simp [hp']

/-- Apply the Boolean threshold lemma to ordered-value sequences. A crossing
`O(i-1) > E(i+1)` is detected by thresholding at `O(i-1)`. -/
theorem monotone_value_shift_of_threshold_counts {n : Nat} {α : Type}
    [LinearOrder α] (E O : Fin n → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ j, E j ≤ O j)
    (hcounts : ∀ t : α,
      boolTrueCount (fun j => decide (t ≤ O j)) ≤
        boolTrueCount (fun j => decide (t ≤ E j)) + 2) :
    ∀ (i : Fin n) (hi : 0 < i.val) (hbound : i.val + 1 < n),
      O ⟨i.val - 1, by omega⟩ ≤ E ⟨i.val + 1, by omega⟩ := by
  intro i hi hbound
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let r : Fin n := ⟨i.val + 1, by omega⟩
  let EO : Fin n → Bool := fun j => decide (O p ≤ E j)
  let OO : Fin n → Bool := fun j => decide (O p ≤ O j)
  have hOO : Monotone OO := by
    intro a b hab
    by_cases ha : O p ≤ O a
    · have hb : O p ≤ O b := ha.trans (hO hab)
      simp [OO, ha, hb]
    · simp [OO, ha]
  have hEO' : Monotone EO := by
    intro a b hab
    by_cases ha : O p ≤ E a
    · have hb : O p ≤ E b := ha.trans (hE hab)
      simp [EO, ha, hb]
    · simp [EO, ha]
  have hpoint : ∀ j, EO j ≤ OO j := by
    intro j
    by_cases h : O p ≤ E j
    · have h' : O p ≤ O j := h.trans (hEO j)
      simp [EO, OO, h, h']
    · simp [EO, OO, h]
  have hbshift := monotone_bool_shift_of_count_gap EO OO hEO' hOO hpoint
    (hcounts (O p)) i hi hbound
  by_contra hshift
  have hlt : E r < O p := lt_of_not_ge hshift
  have hbad : OO p = true ∧ EO r = false := by
    constructor
    · simp [OO]
    · simp [EO, not_le_of_gt hlt]
  have h := hbshift
  rw [hbad.1, hbad.2] at h
  exact (by decide : ¬ ((true : Bool) ≤ false)) h

private theorem boolTrueCount_comp_perm {n : Nat} (v : Fin n → Bool)
    (ρ : Equiv.Perm (Fin n)) : boolTrueCount (v ∘ ρ) = boolTrueCount v := by
  unfold boolTrueCount
  exact Fintype.card_congr
    { toFun := fun i => ⟨ρ i.1, i.2⟩
      invFun := fun i => ⟨ρ.symm i.1, by simpa using i.2⟩
      left_inv := by intro i; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }

private theorem comparator_apply_eq_comp_perm {n : Nat} {α : Type} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), c.apply v = v ∘ ρ := by
  have hne := c.h.ne
  rcases le_total (v c.i) (v c.j) with h | h
  · refine ⟨1, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all
  · refine ⟨Equiv.swap c.i c.j, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

private theorem network_exec_eq_comp_perm {n : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), net.exec v = v ∘ ρ := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
      obtain ⟨ρ₁, h₁⟩ := comparator_apply_eq_comp_perm c v
      obtain ⟨ρ₂, h₂⟩ := ih (c.apply v)
      refine ⟨ρ₁ * ρ₂, ?_⟩
      change ComparatorNetwork.exec ⟨cs⟩ (c.apply v) = _
      rw [h₂, h₁]
      rfl

/-- Any comparator network only permutes its input values, so Boolean count is invariant. -/
theorem boolTrueCount_exec {n : Nat} (net : ComparatorNetwork n) (v : Fin n → Bool) :
    boolTrueCount (net.exec v) = boolTrueCount v := by
  obtain ⟨ρ, hρ⟩ := network_exec_eq_comp_perm net v
  rw [hρ]
  exact boolTrueCount_comp_perm v ρ

/-- Thresholding commutes with comparator-network execution. Each comparator's
min/max operation becomes Boolean conjunction/disjunction at a threshold. -/
theorem exec_threshold {n : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) (t : α) :
    net.exec (fun i => decide (t ≤ v i)) =
      fun i => decide (t ≤ net.exec v i) := by
  have hmin (a b : α) : decide (t ≤ min a b) =
      min (decide (t ≤ a)) (decide (t ≤ b)) := by
    simp [le_min_iff]
  have hmax (a b : α) : decide (t ≤ max a b) =
      max (decide (t ≤ a)) (decide (t ≤ b)) := by
    simp [le_max_iff]
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons]
      have hc : (fun i => decide (t ≤ c.apply v i)) =
          c.apply (fun i => decide (t ≤ v i)) := by
        funext i
        unfold Comparator.apply
        by_cases hi : i = c.i
        · subst i
          simp [hmin]
        · by_cases hj : i = c.j
          · subst i
            simp [hi, hmax]
          · simp [hi, hj]
      rw [← hc]
      exact ih (c.apply v)

def evenWire (m : Nat) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val, by omega⟩

def oddWire (m : Nat) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val + 1, by omega⟩

private def parityEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin (2 * m) where
  toFun := Sum.elim (evenWire m) (oddWire m)
  invFun j := if h : j.val % 2 = 0 then Sum.inl ⟨j.val / 2, by have := j.isLt; omega⟩
    else Sum.inr ⟨j.val / 2, by have := j.isLt; omega⟩
  left_inv s := by
    cases s with
    | inl i =>
      simp [evenWire]
    | inr i =>
      have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
      simp [oddWire, hodd, hdiv]
  right_inv j := by
    dsimp
    split <;> apply Fin.ext <;> dsimp [evenWire, oddWire] <;> omega

/-- The dealt lanes partition the input wires, so their counts add exactly. -/
theorem boolTrueCount_parity_sum {m : Nat} (v : Fin (2 * m) → Bool) :
    boolTrueCount (fun i => v (evenWire m i)) +
      boolTrueCount (fun i => v (oddWire m i)) = boolTrueCount v := by
  let p : Fin m ⊕ Fin m → Prop
    | Sum.inl i => v (evenWire m i) = true
    | Sum.inr i => v (oddWire m i) = true
  have hp (s : Fin m ⊕ Fin m) : p s ↔ v (parityEquiv m s) = true := by
    cases s <;> rfl
  let e : {j : Fin (2 * m) // v j = true} ≃
      ({i : Fin m // v (evenWire m i) = true} ⊕ {i : Fin m // v (oddWire m i) = true}) :=
    ((parityEquiv m).subtypeEquiv hp).symm.trans Equiv.subtypeSum
  unfold boolTrueCount
  rw [← Fintype.card_sum]
  exact (Fintype.card_congr e).symm

/-- In one monotone Boolean run, even positions have no more true entries
than odd positions. -/
theorem monotone_even_count_le_odd {m : Nat} (v : Fin (2 * m) → Bool)
    (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (evenWire m i)) ≤
      boolTrueCount (fun i : Fin m => v (oddWire m i)) := by
  change Fintype.card {i : Fin m // v (evenWire m i) = true} ≤
    Fintype.card {i : Fin m // v (oddWire m i) = true}
  apply Fintype.card_le_of_injective
    (fun i : {i : Fin m // v (evenWire m i) = true} =>
      (⟨i.1, by
        have hpos : evenWire m i.1 ≤ oddWire m i.1 := by
          apply Fin.mk_le_mk.mpr
          simp [evenWire, oddWire]
        have := hv hpos
        cases hval : v (oddWire m i.1) with
        | false =>
            have htf : true ≤ false := by simpa [i.2, hval] using this
            exact False.elim ((by decide : ¬ (true ≤ false)) htf)
        | true => simpa [hval]⟩ :
        {i : Fin m // v (oddWire m i) = true}))
    (by
      intro i j hij
      have hval := congrArg
        (fun x : {i : Fin m // v (oddWire m i) = true} => x.1.val) hij
      apply Subtype.ext
      exact Fin.ext (by simpa using hval))

/-- In one monotone Boolean run, odd positions have at most one more true
entry than even positions. The possible excess is only the final odd wire. -/
theorem monotone_odd_count_le_even_add_one {m : Nat} (v : Fin (2 * m) → Bool)
    (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (oddWire m i)) ≤
      boolTrueCount (fun i : Fin m => v (evenWire m i)) + 1 := by
  let f : {i : Fin m // v (oddWire m i) = true} →
      ({i : Fin m // v (evenWire m i) = true} ⊕ Unit) := fun i =>
    if hi : i.1.val + 1 < m then
      Sum.inl ⟨⟨i.1.val + 1, hi⟩, by
        have hpos : oddWire m i.1 ≤ evenWire m ⟨i.1.val + 1, hi⟩ := by
          apply Fin.mk_le_mk.mpr
          simp [oddWire, evenWire]
        have := hv hpos
        cases hval : v (evenWire m ⟨i.1.val + 1, hi⟩) with
        | false =>
            have htf : true ≤ false := by simpa [i.2, hval] using this
            exact False.elim ((by decide : ¬ (true ≤ false)) htf)
        | true => simpa [hval]⟩
    else Sum.inr Unit.unit
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.1.val + 1 < m <;>
      by_cases hj : j.1.val + 1 < m
    · simp [f, hi, hj] at hij
      apply Subtype.ext
      exact Fin.ext hij
    · simp [f, hi, hj] at hij
    · simp [f, hi, hj] at hij
    · simp [f, hi, hj] at hij
      apply Subtype.ext
      exact Fin.ext (by have := i.1.isLt; have := j.1.isLt; omega)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, boolTrueCount] using hcard

/-- A sorted Boolean union deals exact floor/ceiling true counts. Equivalently,
its zero counts are ceiling/floor, with the even lane receiving the ceiling. -/
theorem sorted_bool_parity_counts {m : Nat} (v : Fin (2 * m) → Bool)
    (hv : Monotone v) :
    boolTrueCount (fun i => v (evenWire m i)) = boolTrueCount v / 2 ∧
    boolTrueCount (fun i => v (oddWire m i)) = (boolTrueCount v + 1) / 2 := by
  have hsum := boolTrueCount_parity_sum v
  have hlo := monotone_even_count_le_odd v hv
  have hhi := monotone_odd_count_le_even_add_one v hv
  constructor <;> omega

/-- Across two ascending Boolean runs, concatenating their parity counts
changes the even/odd true count by at most two. -/
theorem two_monotone_runs_parity_count_gap {m : Nat}
    (A B : Fin (2 * m) → Bool) (hA : Monotone A) (hB : Monotone B) :
    boolTrueCount (fun i : Fin m => A (evenWire m i)) +
        boolTrueCount (fun i : Fin m => B (evenWire m i)) ≤
      boolTrueCount (fun i : Fin m => A (oddWire m i)) +
        boolTrueCount (fun i : Fin m => B (oddWire m i)) ∧
    boolTrueCount (fun i : Fin m => A (oddWire m i)) +
        boolTrueCount (fun i : Fin m => B (oddWire m i)) ≤
      boolTrueCount (fun i : Fin m => A (evenWire m i)) +
        boolTrueCount (fun i : Fin m => B (evenWire m i)) + 2 := by
  constructor
  · exact Nat.add_le_add (monotone_even_count_le_odd A hA)
      (monotone_even_count_le_odd B hB)
  · calc
      _ ≤ (boolTrueCount (fun i : Fin m => A (evenWire m i)) + 1) +
            (boolTrueCount (fun i : Fin m => B (evenWire m i)) + 1) :=
        Nat.add_le_add (monotone_odd_count_le_even_add_one A hA)
          (monotone_odd_count_le_even_add_one B hB)
      _ = _ := by omega

private def evenEmbed (k : Nat) : Fin (2 ^ (k + 1)) ↪o Fin (2 ^ (k + 2)) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val, by
      have hi := i.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      rw [hp]
      omega⟩)
    (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by omega))

private def oddEmbed (k : Nat) : Fin (2 ^ (k + 1)) ↪o Fin (2 ^ (k + 2)) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val + 1, by
      have hi := i.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      rw [hp]
      omega⟩)
    (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by omega))

theorem evenEmbed_eq_evenIndexFull (k : Nat) (i : Fin (2 ^ (k + 1))) :
    Fin.cast (by
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
      have hd : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      rw [hp, hd]
      omega) (evenEmbed k i) =
      evenIndexFull (2 ^ k) (Fin.cast (by
        rw [pow_succ]
        omega) i) := by
  apply Fin.ext
  simp [evenEmbed, evenIndexFull]

theorem oddEmbed_eq_oddIndexFull (k : Nat) (i : Fin (2 ^ (k + 1))) :
    Fin.cast (by
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
      have hd : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      rw [hp, hd]
      omega) (oddEmbed k i) =
      oddIndexFull (2 ^ k) (Fin.cast (by
        rw [pow_succ]
        omega) i) := by
  apply Fin.ext
  simp [oddEmbed, oddIndexFull]

private theorem evenEmbed_val (k : Nat) (i : Fin (2 ^ (k + 1))) :
    (evenEmbed k i).val = 2 * i.val := rfl

private theorem oddEmbed_val (k : Nat) (i : Fin (2 ^ (k + 1))) :
    (oddEmbed k i).val = 2 * i.val + 1 := rfl

private theorem evenEmbed_of_evenIndex (k : Nat)
    (j : Fin (2 ^ (k + 2))) (heven : j.val % 2 = 0) :
    evenEmbed k ⟨j.val / 2, by
      have hj := j.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        calc
          2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k + 1) := Nat.mul_comm _ _
      omega⟩ = j := by
  apply Fin.ext
  change 2 * (j.val / 2) = j.val
  omega

private theorem oddEmbed_of_oddIndex (k : Nat)
    (j : Fin (2 ^ (k + 2))) (hodd : j.val % 2 = 1) :
    oddEmbed k ⟨j.val / 2, by
      have hj := j.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        calc
          2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k + 1) := Nat.mul_comm _ _
      omega⟩ = j := by
  apply Fin.ext
  change 2 * (j.val / 2) + 1 = j.val
  omega
private def oddEvenCrossComparator (k : Nat) (i : Fin (2 ^ (k + 1) - 1)) :
    Comparator (2 ^ (k + 2)) :=
    ⟨⟨2 * i.val + 1, by
      have hi := i.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      rw [hp]
      omega⟩,
     ⟨2 * i.val + 2, by
      have hi := i.isLt
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      rw [hp]
      omega⟩,
     by exact Fin.mk_lt_mk.mpr (by omega)⟩

private def crossLane (k : Nat) (i : Fin (2 ^ (k + 1) - 1)) : Fin (2 ^ (k + 1)) :=
  ⟨i.val, by have hi := i.isLt; omega⟩

private def crossNextLane (k : Nat) (i : Fin (2 ^ (k + 1) - 1)) : Fin (2 ^ (k + 1)) :=
  ⟨i.val + 1, by have hi := i.isLt; omega⟩

private theorem crossComparator_odd_wire (k : Nat) (i : Fin (2 ^ (k + 1) - 1)) :
    (oddEvenCrossComparator k i).i = oddEmbed k (crossLane k i) := by
  apply Fin.ext
  simp [oddEvenCrossComparator, oddEmbed, crossLane]

private theorem crossComparator_next_even_wire (k : Nat)
    (i : Fin (2 ^ (k + 1) - 1)) :
    (oddEvenCrossComparator k i).j = evenEmbed k (crossNextLane k i) := by
  apply Fin.ext
  simp [oddEvenCrossComparator, evenEmbed, crossNextLane] <;> omega

private theorem crossComparator_previous_odd_wire (k : Nat)
    (i : Fin (2 ^ (k + 1) - 1)) :
    (oddEvenCrossComparator k i).i =
      oddEmbed k ⟨i.val, by have hi := i.isLt; omega⟩ := by
  apply Fin.ext
  simp [oddEvenCrossComparator, oddEmbed]

private def oddEvenCrossLayer (k : Nat) : ComparatorNetwork (2 ^ (k + 2)) where
  comparators := (List.finRange (2 ^ (k + 1) - 1)).map (oddEvenCrossComparator k)

private theorem oddEvenCrossLayer_parallel (k : Nat) :
    IsParallelLayer (oddEvenCrossLayer k).comparators := by
  unfold IsParallelLayer oddEvenCrossLayer
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {i j} hij => ?_
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  simp only [Comparator.overlaps, Fin.ext_iff]
  have hi := i.isLt
  have hj := j.isLt
  simp only [oddEvenCrossComparator]
  omega

/-- In a non-overlapping comparator layer, the value at a touched wire is the
result of its unique comparator applied to the original input. -/
private theorem foldl_parallel_at_comparator {n : Nat} {α : Type} [LinearOrder α]
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

/-- Each odd wire in the concrete cross layer is the minimum produced by its
unique correction comparator. -/
private theorem oddEvenCrossLayer_exec_left {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1) - 1)) :
    (oddEvenCrossLayer k).exec v (oddEvenCrossComparator k i).i =
      min (v (oddEvenCrossComparator k i).i) (v (oddEvenCrossComparator k i).j) := by
  let c := oddEvenCrossComparator k i
  have hc : c ∈ (oddEvenCrossLayer k).comparators := by
    simp [oddEvenCrossLayer, c]
  have h := foldl_parallel_at_comparator _ (oddEvenCrossLayer_parallel k)
    c hc v c.i (Or.inl rfl)
  simpa [ComparatorNetwork.exec, oddEvenCrossLayer, c, Comparator.apply] using h

/-- Each even wire after the first is the maximum produced by its unique
correction comparator. -/
private theorem oddEvenCrossLayer_exec_right {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1) - 1)) :
    (oddEvenCrossLayer k).exec v (oddEvenCrossComparator k i).j =
      max (v (oddEvenCrossComparator k i).i) (v (oddEvenCrossComparator k i).j) := by
  let c := oddEvenCrossComparator k i
  have hc : c ∈ (oddEvenCrossLayer k).comparators := by
    simp [oddEvenCrossLayer, c]
  have h := foldl_parallel_at_comparator _ (oddEvenCrossLayer_parallel k)
    c hc v c.j (Or.inr rfl)
  have hji : c.j ≠ c.i := ne_of_gt c.h
  simpa [ComparatorNetwork.exec, oddEvenCrossLayer, c, Comparator.apply, hji] using h

/-- In parity-wire notation, the correction sends each odd wire to the
minimum of that odd value and the following even value. -/
private theorem oddEvenCrossLayer_exec_odd {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1)))
    (hi : i.val + 1 < 2 ^ (k + 1)) :
    (oddEvenCrossLayer k).exec v (oddEmbed k i) =
      min (v (oddEmbed k i))
        (v (evenEmbed k ⟨i.val + 1, by have := i.isLt; omega⟩)) := by
  let j : Fin (2 ^ (k + 1) - 1) := ⟨i.val, by omega⟩
  have hj : crossLane k j = i := by apply Fin.ext; rfl
  have hj' : crossNextLane k j = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    apply Fin.ext
    rfl
  have hleft : (oddEvenCrossComparator k j).i = oddEmbed k i := by
    rw [crossComparator_odd_wire, hj]
  have hright : (oddEvenCrossComparator k j).j =
      evenEmbed k ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    rw [crossComparator_next_even_wire, hj']
  rw [← hleft, ← hright]
  exact oddEvenCrossLayer_exec_left v j

/-- In parity-wire notation, the correction sends each noninitial even wire
to the maximum of it and the preceding odd value. -/
private theorem oddEvenCrossLayer_exec_even {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1)))
    (hi : 0 < i.val) :
    (oddEvenCrossLayer k).exec v (evenEmbed k i) =
      max (v (oddEmbed k ⟨i.val - 1, by have := i.isLt; omega⟩))
        (v (evenEmbed k i)) := by
  let j : Fin (2 ^ (k + 1) - 1) := ⟨i.val - 1, by omega⟩
  have hj : crossLane k j = ⟨i.val - 1, by have := i.isLt; omega⟩ := by
    apply Fin.ext
    rfl
  have hj' : crossNextLane k j = i := by
    apply Fin.ext
    simp [crossNextLane, j]
    omega
  have hleft : (oddEvenCrossComparator k j).i =
      oddEmbed k ⟨i.val - 1, by have := i.isLt; omega⟩ := by
    rw [crossComparator_odd_wire, hj]
  have hright : (oddEvenCrossComparator k j).j = evenEmbed k i := by
    rw [crossComparator_next_even_wire, hj']
  rw [← hleft, ← hright]
  exact oddEvenCrossLayer_exec_right v j

private theorem oddEvenCrossLayer_exec_first {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) :
    (oddEvenCrossLayer k).exec v (0 : Fin (2 ^ (k + 2))) = v 0 := by
  unfold ComparatorNetwork.exec oddEvenCrossLayer
  apply foldl_comparators_outside
  intro c hc
  rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp [oddEvenCrossComparator] at hv
  · intro h
    have hv := congrArg Fin.val h
    simp [oddEvenCrossComparator] at hv

private theorem oddEvenCrossLayer_exec_last {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) :
    (oddEvenCrossLayer k).exec v
        ⟨2 ^ (k + 2) - 1, by
          have hp : 0 < 2 ^ (k + 2) := by positivity
          exact Nat.sub_lt hp (by decide)⟩ =
      v ⟨2 ^ (k + 2) - 1, by
          have hp : 0 < 2 ^ (k + 2) := by positivity
          exact Nat.sub_lt hp (by decide)⟩ := by
  unfold ComparatorNetwork.exec oddEvenCrossLayer
  apply foldl_comparators_outside
  intro c hc
  rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp [oddEvenCrossComparator] at hv
    have hq : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp [oddEvenCrossComparator] at hv
    have hq : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
    omega

private theorem monotone_fin_of_adjacent {N : Nat} {α : Type} [Preorder α]
    (f : Fin N → α) (hN : 1 < N)
    (hstep : ∀ i : Fin (N - 1),
      f ⟨i.val, by have hi := i.isLt; omega⟩ ≤
        f ⟨i.val + 1, by have hi := i.isLt; omega⟩) :
    Monotone f := by
  intro a b hab
  let g : Nat → α := fun n => f ⟨min n (N - 1), by omega⟩
  have hg : ∀ n, g n ≤ g (n + 1) := by
    intro n
    by_cases hn : n < N - 1
    · have hn' : n + 1 ≤ N - 1 := by omega
      simpa [g, Nat.min_eq_left (Nat.le_of_lt hn), Nat.min_eq_left hn'] using
        hstep ⟨n, hn⟩
    · have hn' : N - 1 ≤ n := by omega
      have hn'' : N - 1 ≤ n + 1 := by omega
      simp [g, Nat.min_eq_right hn', Nat.min_eq_right hn'']
  have hmono : Monotone g := monotone_nat_of_le_succ hg
  have ha : min a.val (N - 1) = a.val := Nat.min_eq_left (by have := a.isLt; omega)
  have hb : min b.val (N - 1) = b.val := Nat.min_eq_left (by have := b.isLt; omega)
  simpa [g, ha, hb] using hmono (Fin.le_iff_val_le_val.mp hab)

private theorem oddEvenCrossLayer_pair_ordered {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α)
    (hE : Monotone (fun i => v (evenEmbed k i)))
    (hO : Monotone (fun i => v (oddEmbed k i)))
    (hEO : ∀ i, v (evenEmbed k i) ≤ v (oddEmbed k i))
    (hshift : ∀ (i : Fin (2 ^ (k + 1))) (hi : 0 < i.val)
      (hb : i.val + 1 < 2 ^ (k + 1)),
      v (oddEmbed k ⟨i.val - 1, by omega⟩) ≤
        v (evenEmbed k ⟨i.val + 1, by omega⟩))
    (i : Fin (2 ^ (k + 1))) :
    (oddEvenCrossLayer k).exec v (evenEmbed k i) ≤
      (oddEvenCrossLayer k).exec v (oddEmbed k i) := by
  have hi := i.isLt
  by_cases hz : i.val = 0
  · have he0 : evenEmbed k i = 0 := by
      apply Fin.ext
      change 2 * i.val = 0
      omega
    have hb : i.val + 1 < 2 ^ (k + 1) := by
      have hp : 1 < 2 ^ (k + 1) := by rw [pow_succ]; have := Nat.two_pow_pos k; omega
      omega
    rw [he0, oddEvenCrossLayer_exec_first, oddEvenCrossLayer_exec_odd v i hb]
    have he : v 0 = v (evenEmbed k i) := congrArg v he0.symm
    rw [he]
    exact le_min (hEO i) (hE (Fin.mk_le_mk.mpr (by simp)))
  · rw [oddEvenCrossLayer_exec_even v i (by omega)]
    by_cases hb : i.val + 1 < 2 ^ (k + 1)
    · rw [oddEvenCrossLayer_exec_odd v i hb]
      exact max_le (le_min (hO (Fin.mk_le_mk.mpr (by simp <;> omega)))
        (hshift i (by omega) hb))
        (le_min (hEO i) (hE (Fin.mk_le_mk.mpr (by simp))))
    · have hlast : oddEmbed k i =
          ⟨2 ^ (k + 2) - 1, by
            have hp : 0 < 2 ^ (k + 2) := by positivity
            omega⟩ := by
        apply Fin.ext
        change 2 * i.val + 1 = 2 ^ (k + 2) - 1
        have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
        omega
      rw [hlast, oddEvenCrossLayer_exec_last]
      rw [← hlast]
      exact max_le (hO (Fin.mk_le_mk.mpr (by simp <;> omega))) (hEO i)

private theorem oddEvenCrossLayer_between {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1)))
    (hi : i.val + 1 < 2 ^ (k + 1)) :
    (oddEvenCrossLayer k).exec v (oddEmbed k i) ≤
      (oddEvenCrossLayer k).exec v (evenEmbed k ⟨i.val + 1, hi⟩) := by
  rw [oddEvenCrossLayer_exec_odd v i hi,
    oddEvenCrossLayer_exec_even v ⟨i.val + 1, hi⟩ (by simp)]
  have heq : (⟨(i.val + 1) - 1, by omega⟩ : Fin (2 ^ (k + 1))) = i := by
    apply Fin.ext
    simp
  simp only [Fin.val_mk, heq]
  exact (min_le_left _ _).trans (le_max_left _ _)

private theorem oddEvenCrossLayer_sorts_of_profile {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α)
    (hE : Monotone (fun i => v (evenEmbed k i)))
    (hO : Monotone (fun i => v (oddEmbed k i)))
    (hEO : ∀ i, v (evenEmbed k i) ≤ v (oddEmbed k i))
    (hshift : ∀ (i : Fin (2 ^ (k + 1))) (hi : 0 < i.val)
      (hb : i.val + 1 < 2 ^ (k + 1)),
      v (oddEmbed k ⟨i.val - 1, by omega⟩) ≤
        v (evenEmbed k ⟨i.val + 1, by omega⟩)) :
    Monotone ((oddEvenCrossLayer k).exec v) := by
  have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
  apply monotone_fin_of_adjacent _ (by have := Nat.two_pow_pos (k + 1); omega)
  intro j
  have hj := j.isLt
  let i : Fin (2 ^ (k + 1)) := ⟨j.val / 2, by omega⟩
  by_cases heven : j.val % 2 = 0
  · have hl : (⟨j.val, by omega⟩ : Fin (2 ^ (k + 2))) = evenEmbed k i := by
      apply Fin.ext
      change j.val = 2 * (j.val / 2)
      omega
    have hr : (⟨j.val + 1, by omega⟩ : Fin (2 ^ (k + 2))) = oddEmbed k i := by
      apply Fin.ext
      change j.val + 1 = 2 * (j.val / 2) + 1
      omega
    rw [hl, hr]
    exact oddEvenCrossLayer_pair_ordered v hE hO hEO hshift i
  · have hb : i.val + 1 < 2 ^ (k + 1) := by dsimp [i]; omega
    have hl : (⟨j.val, by omega⟩ : Fin (2 ^ (k + 2))) = oddEmbed k i := by
      apply Fin.ext
      change j.val = 2 * (j.val / 2) + 1
      omega
    have hr : (⟨j.val + 1, by omega⟩ : Fin (2 ^ (k + 2))) =
        evenEmbed k ⟨i.val + 1, hb⟩ := by
      apply Fin.ext
      change j.val + 1 = 2 * (j.val / 2 + 1)
      omega
    rw [hl, hr]
    exact oddEvenCrossLayer_between v i hb

private theorem oddEvenCrossLayer_depth_le (k : Nat) :
    (oddEvenCrossLayer k).depth ≤ 1 := by
  apply depth_le_of_decomposition (oddEvenCrossLayer k)
    [(oddEvenCrossLayer k).comparators]
  constructor
  · intro cs hcs
    have hcs' : cs = (oddEvenCrossLayer k).comparators := List.mem_singleton.mp hcs
    simpa [hcs'] using oddEvenCrossLayer_parallel k
  · simp

private theorem even_odd_images_disjoint (k : Nat)
    (i j : Fin (2 ^ (k + 1))) : evenEmbed k i ≠ oddEmbed k j := by
  intro h
  have hv := congrArg Fin.val h
  simp [evenEmbed, oddEmbed] at hv
  omega

/-- Batcher's odd-even merge for two ascending runs in concatenated order.
The even and odd submerges are scattered to their parity wires, followed by
the single layer comparing each odd wire with the next even wire. -/
def oddEvenMergeNet : (k : Nat) → ComparatorNetwork (2 ^ k)
  | 0 => ⟨[]⟩
  | 1 => ⟨[⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by norm_num⟩]⟩
  | k + 2 =>
      let e := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (evenEmbed k)
      let o := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (oddEmbed k)
      ⟨e.comparators ++ o.comparators ++ (oddEvenCrossLayer k).comparators⟩

/-- The two recursively embedded parity submerges, before the correction layer. -/
private def oddEvenFront (k : Nat) : ComparatorNetwork (2 ^ (k + 2)) :=
  let e := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (evenEmbed k)
  let o := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (oddEmbed k)
  ⟨e.comparators ++ o.comparators⟩

/-- The recursive merge consists of the parity front followed by correction. -/
theorem oddEvenMergeNet_exec_succ_succ {α : Type} [LinearOrder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α) :
    (oddEvenMergeNet (k + 2)).exec v =
      (oddEvenCrossLayer k).exec ((oddEvenFront k).exec v) := by
  let e := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (evenEmbed k)
  let o := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (oddEmbed k)
  have h := ComparatorNetwork.exec_append (⟨e.comparators ++ o.comparators⟩)
    (oddEvenCrossLayer k) v
  simpa [oddEvenMergeNet, oddEvenFront, e, o, List.append_assoc] using h

private theorem even_not_odd_range (k : Nat) (i : Fin (2 ^ (k + 1))) :
    (evenEmbed k i : Fin (2 ^ (k + 2))) ∉ Set.range (oddEmbed k) := by
  rintro ⟨j, h⟩
  exact even_odd_images_disjoint k i j h.symm

private theorem odd_not_even_range (k : Nat) (i : Fin (2 ^ (k + 1))) :
    (oddEmbed k i : Fin (2 ^ (k + 2))) ∉ Set.range (evenEmbed k) := by
  rintro ⟨j, h⟩
  exact even_odd_images_disjoint k j i h

/-- Before correction, the even wires contain exactly the recursive even-submerge output. -/
theorem oddEvenFront_exec_even {α : Type} [LinearOrder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1))) :
    (oddEvenFront k).exec v (evenEmbed k i) =
      (oddEvenMergeNet (k + 1)).exec (v ∘ evenEmbed k) i := by
  unfold oddEvenFront
  rw [ComparatorNetwork.exec_append]
  rw [ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ (even_not_odd_range k i)]
  exact ComparatorNetwork.scatterEmbed_exec_inside _ _ _ _ _

/-- Before correction, the odd wires contain exactly the recursive odd-submerge output. -/
theorem oddEvenFront_exec_odd {α : Type} [LinearOrder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α) (i : Fin (2 ^ (k + 1))) :
    (oddEvenFront k).exec v (oddEmbed k i) =
      (oddEvenMergeNet (k + 1)).exec (v ∘ oddEmbed k) i := by
  unfold oddEvenFront
  rw [ComparatorNetwork.exec_append]
  rw [ComparatorNetwork.scatterEmbed_exec_inside]
  congr 1
  funext j
  exact ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ (odd_not_even_range k j)

/-- Actual-network recursive induction step: if each parity input consists of
two sorted runs, and the level-`k+1` merge sorts every such pair, then both
parity outputs of the level-`k+2` front are sorted. -/
private theorem powPairSizeEq (k : Nat) :
    2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

private theorem powQuadSizeEq (k : Nat) :
    (2 ^ k + 2 ^ k) + (2 ^ k + 2 ^ k) = 2 ^ (k + 2) := by
  calc
    _ = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [powPairSizeEq k]
    _ = 2 ^ (k + 2) := powPairSizeEq (k + 1)

private theorem evenEmbed_eq_cast_evenIndexFull {k : Nat}
    (i : Fin (2 ^ (k + 1))) :
    Fin.cast (powQuadSizeEq k)
        (evenIndexFull (2 ^ k) (Fin.cast (powPairSizeEq k).symm i)) =
      evenEmbed k i := by
  apply Fin.ext
  simp [evenIndexFull, evenEmbed, Fin.cast]

private theorem oddEmbed_eq_cast_oddIndexFull {k : Nat}
    (i : Fin (2 ^ (k + 1))) :
    Fin.cast (powQuadSizeEq k)
        (oddIndexFull (2 ^ k) (Fin.cast (powPairSizeEq k).symm i)) =
      oddEmbed k i := by
  apply Fin.ext
  simp [oddIndexFull, oddEmbed, Fin.cast]

/-- The physical parity subsequences of two sorted runs have a true-count
gap of at most two, with the actual power-of-two wire indices. -/
theorem oddEven_parity_input_count_gap (k : Nat)
    (v : Fin (2 ^ (k + 2)) → Bool)
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    boolTrueCount (v ∘ evenEmbed k) ≤ boolTrueCount (v ∘ oddEmbed k) + 2 ∧
    boolTrueCount (v ∘ oddEmbed k) ≤ boolTrueCount (v ∘ evenEmbed k) + 2 := by
  let hsmall := powPairSizeEq k
  let hbig := powPairSizeEq (k + 1)
  let htotal := (congrArg (fun x => x + x) hsmall).trans hbig
  let w : Fin ((2 ^ k + 2 ^ k) + (2 ^ k + 2 ^ k)) → Bool :=
    fun i => v (Fin.cast htotal i)
  have hA' : Monotone (fun i : Fin (2 ^ k + 2 ^ k) =>
      w (Fin.castAdd (2 ^ k + 2 ^ k) i)) := by
    intro i j hij
    change v (Fin.cast htotal (Fin.castAdd (2 ^ k + 2 ^ k) i)) ≤
      v (Fin.cast htotal (Fin.castAdd (2 ^ k + 2 ^ k) j))
    have hi : Fin.cast htotal (Fin.castAdd (2 ^ k + 2 ^ k) i) =
        Fin.cast hbig (Fin.castAdd (2 ^ (k + 1)) (Fin.cast hsmall i)) := by
      apply Fin.ext
      simp [Fin.cast, Fin.castAdd, hsmall, hbig, htotal]
    have hj : Fin.cast htotal (Fin.castAdd (2 ^ k + 2 ^ k) j) =
        Fin.cast hbig (Fin.castAdd (2 ^ (k + 1)) (Fin.cast hsmall j)) := by
      apply Fin.ext
      simp [Fin.cast, Fin.castAdd, hsmall, hbig, htotal]
    rw [hi, hj]
    apply hA
    apply Fin.mk_le_mk.mpr
    have hv := Fin.mk_le_mk.mp hij
    simpa [Fin.cast] using hv
  have hB' : Monotone (fun i : Fin (2 ^ k + 2 ^ k) =>
      w (Fin.natAdd (2 ^ k + 2 ^ k) i)) := by
    intro i j hij
    change v (Fin.cast htotal (Fin.natAdd (2 ^ k + 2 ^ k) i)) ≤
      v (Fin.cast htotal (Fin.natAdd (2 ^ k + 2 ^ k) j))
    have hi : Fin.cast htotal (Fin.natAdd (2 ^ k + 2 ^ k) i) =
        Fin.cast hbig (Fin.natAdd (2 ^ (k + 1)) (Fin.cast hsmall i)) := by
      apply Fin.ext
      simp [Fin.cast, Fin.natAdd, hsmall, hbig, htotal]
    have hj : Fin.cast htotal (Fin.natAdd (2 ^ k + 2 ^ k) j) =
        Fin.cast hbig (Fin.natAdd (2 ^ (k + 1)) (Fin.cast hsmall j)) := by
      apply Fin.ext
      simp [Fin.cast, Fin.natAdd, hsmall, hbig, htotal]
    rw [hi, hj]
    apply hB
    apply Fin.mk_le_mk.mpr
    have hv := Fin.mk_le_mk.mp hij
    simpa [Fin.cast] using hv
  obtain ⟨hgapE, hgapO⟩ :=
    concatenated_two_run_parity_count_gap w hA' hB'
  have hcountE : boolTrueCount (v ∘ evenEmbed k) =
      boolTrueCount (fun j : Fin (2 ^ k + 2 ^ k) =>
        w (evenIndexFull (2 ^ k) j)) := by
    have hcast := boolTrueCount_finCast hsmall.symm
      (fun j : Fin (2 ^ k + 2 ^ k) => w (evenIndexFull (2 ^ k) j))
    have hfun : (fun i : Fin (2 ^ (k + 1)) => v (evenEmbed k i)) =
        (fun i => w (evenIndexFull (2 ^ k) (Fin.cast hsmall.symm i))) := by
      funext i
      change v (evenEmbed k i) = v (Fin.cast htotal
        (evenIndexFull (2 ^ k) (Fin.cast hsmall.symm i)))
      rw [← evenEmbed_eq_cast_evenIndexFull]
    change boolTrueCount (fun i => v (evenEmbed k i)) = _
    rw [hfun]
    exact hcast
  have hcountO : boolTrueCount (v ∘ oddEmbed k) =
      boolTrueCount (fun j : Fin (2 ^ k + 2 ^ k) =>
        w (oddIndexFull (2 ^ k) j)) := by
    have hcast := boolTrueCount_finCast hsmall.symm
      (fun j : Fin (2 ^ k + 2 ^ k) => w (oddIndexFull (2 ^ k) j))
    have hfun : (fun i : Fin (2 ^ (k + 1)) => v (oddEmbed k i)) =
        (fun i => w (oddIndexFull (2 ^ k) (Fin.cast hsmall.symm i))) := by
      funext i
      change v (oddEmbed k i) = v (Fin.cast htotal
        (oddIndexFull (2 ^ k) (Fin.cast hsmall.symm i)))
      rw [← oddEmbed_eq_cast_oddIndexFull]
    change boolTrueCount (fun i => v (oddEmbed k i)) = _
    rw [hfun]
    exact hcast
  constructor
  · rw [hcountE, hcountO]
    omega
  · rw [hcountO, hcountE]
    exact hgapO

private theorem evenEmbed_castAdd_eq {k : Nat} (i : Fin (2 ^ k)) :
    evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i)) =
      Fin.cast (powPairSizeEq (k + 1))
        (Fin.castAdd (2 ^ (k + 1))
          ⟨2 * i.val, by have hi := i.isLt; omega⟩) := by
  apply Fin.ext
  simp [evenEmbed, Fin.cast, Fin.castAdd]

private theorem oddEmbed_castAdd_eq {k : Nat} (i : Fin (2 ^ k)) :
    oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i)) =
      Fin.cast (powPairSizeEq (k + 1))
        (Fin.castAdd (2 ^ (k + 1))
          ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) := by
  apply Fin.ext
  simp [oddEmbed, Fin.cast, Fin.castAdd]

private theorem evenEmbed_natAdd_eq {k : Nat} (i : Fin (2 ^ k)) :
    evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)) =
      Fin.cast (powPairSizeEq (k + 1))
        (Fin.natAdd (2 ^ (k + 1))
          ⟨2 * i.val, by have hi := i.isLt; omega⟩) := by
  apply Fin.ext
  simp [evenEmbed, Fin.cast, Fin.natAdd]
  omega

private theorem oddEmbed_natAdd_eq {k : Nat} (i : Fin (2 ^ k)) :
    oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)) =
      Fin.cast (powPairSizeEq (k + 1))
        (Fin.natAdd (2 ^ (k + 1))
          ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) := by
  apply Fin.ext
  simp [oddEmbed, Fin.cast, Fin.natAdd]
  omega

/-- The four actual recursive inputs are sorted within each original source
run: each is just every other wire of that sorted run. -/
theorem oddEven_parity_inputs_sorted {α : Type} [Preorder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α)
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    (Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
     Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))) ∧
     Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
     Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) := by
  have heA : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) := by
    intro i j hij
    change v (evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ≤
      v (evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) j)))
    rw [evenEmbed_castAdd_eq, evenEmbed_castAdd_eq]
    apply hA
    exact Fin.mk_le_mk.mpr (by have := hij; simp; omega)
  have heB : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))) := by
    intro i j hij
    change v (evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))) ≤
      v (evenEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) j)))
    rw [evenEmbed_natAdd_eq, evenEmbed_natAdd_eq]
    apply hB
    exact Fin.mk_le_mk.mpr (by have := hij; simp; omega)
  have hoA : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) := by
    intro i j hij
    change v (oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ≤
      v (oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) j)))
    rw [oddEmbed_castAdd_eq, oddEmbed_castAdd_eq]
    apply hA
    exact Fin.mk_le_mk.mpr (by have := hij; simp; omega)
  have hoB : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))) := by
    intro i j hij
    change v (oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))) ≤
      v (oddEmbed k (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) j)))
    rw [oddEmbed_natAdd_eq, oddEmbed_natAdd_eq]
    apply hB
    exact Fin.mk_le_mk.mpr (by have := hij; simp; omega)
  exact ⟨heA, heB, hoA, hoB⟩

theorem oddEvenFront_recursive_outputs_sorted {α : Type} [LinearOrder α]
    (k : Nat) (v : Fin (2 ^ (k + 2)) → α)
    (ih : ∀ w : Fin (2 ^ (k + 1)) → α,
      (Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
       Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) →
      Monotone ((oddEvenMergeNet (k + 1)).exec w))
    (hEA : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))))
    (hEB : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ evenEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i))))
    (hOA : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))))
    (hOB : Monotone (fun i : Fin (2 ^ k) =>
      (v ∘ oddEmbed k) (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) :
    Monotone (fun i : Fin (2 ^ (k + 1)) =>
      (oddEvenFront k).exec v (evenEmbed k i)) ∧
    Monotone (fun i : Fin (2 ^ (k + 1)) =>
      (oddEvenFront k).exec v (oddEmbed k i)) := by
  constructor
  · have hs := ih (v ∘ evenEmbed k) ⟨hEA, hEB⟩
    have he : (fun i : Fin (2 ^ (k + 1)) =>
        (oddEvenFront k).exec v (evenEmbed k i)) =
        (oddEvenMergeNet (k + 1)).exec (v ∘ evenEmbed k) := by
      funext i
      exact oddEvenFront_exec_even k v i
    rw [he]
    exact hs
  · have hs := ih (v ∘ oddEmbed k) ⟨hOA, hOB⟩
    have ho : (fun i : Fin (2 ^ (k + 1)) =>
        (oddEvenFront k).exec v (oddEmbed k i)) =
        (oddEvenMergeNet (k + 1)).exec (v ∘ oddEmbed k) := by
      funext i
      exact oddEvenFront_exec_odd k v i
    rw [ho]
    exact hs

/-- The recursive front step for the actual network, with its four parity-run
premises discharged from the two sorted source runs. -/
theorem oddEvenFront_recursive_outputs_sorted_of_two_runs
    {α : Type} [LinearOrder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α)
    (ih : ∀ w : Fin (2 ^ (k + 1)) → α,
      (Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
       Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) →
      Monotone ((oddEvenMergeNet (k + 1)).exec w))
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    Monotone (fun i : Fin (2 ^ (k + 1)) =>
      (oddEvenFront k).exec v (evenEmbed k i)) ∧
    Monotone (fun i : Fin (2 ^ (k + 1)) =>
      (oddEvenFront k).exec v (oddEmbed k i)) := by
  obtain ⟨hEA, hEB, hOA, hOB⟩ := oddEven_parity_inputs_sorted k v hA hB
  exact oddEvenFront_recursive_outputs_sorted k v ih hEA hEB hOA hOB

/-- At every rank, the even recursive output is no larger than the odd one.
This follows by comparing their inputs within the same sorted source half and
then using monotonicity of comparator-network execution. -/
theorem oddEvenFront_same_rank_order {α : Type} [LinearOrder α] (k : Nat)
    (v : Fin (2 ^ (k + 2)) → α)
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    ∀ i : Fin (2 ^ (k + 1)),
      (oddEvenFront k).exec v (evenEmbed k i) ≤
        (oddEvenFront k).exec v (oddEmbed k i) := by
  intro i
  have hinput : ∀ j : Fin (2 ^ (k + 1)),
      (v ∘ evenEmbed k) j ≤ (v ∘ oddEmbed k) j := by
    intro j
    change v (evenEmbed k j) ≤ v (oddEmbed k j)
    by_cases hfirst : j.val < 2 ^ k
    · let r : Fin (2 ^ k) := ⟨j.val, hfirst⟩
      have hj : j = Fin.cast (powPairSizeEq k)
          (Fin.castAdd (2 ^ k) r) := by
        apply Fin.ext
        simp [Fin.cast, Fin.castAdd, r]
      rw [hj, evenEmbed_castAdd_eq, oddEmbed_castAdd_eq]
      apply hA
      exact Fin.mk_le_mk.mpr (by simp)
    · let r : Fin (2 ^ k) := ⟨j.val - 2 ^ k, by have := j.isLt; omega⟩
      have hj : j = Fin.cast (powPairSizeEq k)
          (Fin.natAdd (2 ^ k) r) := by
        apply Fin.ext
        simp [Fin.cast, Fin.natAdd, r]
        omega
      rw [hj, evenEmbed_natAdd_eq, oddEmbed_natAdd_eq]
      apply hB
      exact Fin.mk_le_mk.mpr (by simp)
  rw [oddEvenFront_exec_even, oddEvenFront_exec_odd]
  exact exec_mono_input (oddEvenMergeNet (k + 1)) hinput i

/-- With the recursive sorting hypothesis and the threshold count gap, the
actual front satisfies the shifted inequality required by correction. The
same-rank premise is discharged by `oddEvenFront_same_rank_order`. -/
theorem oddEvenFront_shift_of_two_runs {α : Type} [LinearOrder α]
    (k : Nat) (v : Fin (2 ^ (k + 2)) → α)
    (ih : ∀ w : Fin (2 ^ (k + 1)) → α,
      (Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
       Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) →
      Monotone ((oddEvenMergeNet (k + 1)).exec w))
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i))))
    (hcounts : ∀ t : α,
      boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (oddEmbed k i))) ≤
        boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (evenEmbed k i))) + 2) :
    ∀ (i : Fin (2 ^ (k + 1))) (hi : 0 < i.val)
      (hbound : i.val + 1 < 2 ^ (k + 1)),
      (oddEvenFront k).exec v (oddEmbed k ⟨i.val - 1, by omega⟩) ≤
        (oddEvenFront k).exec v (evenEmbed k ⟨i.val + 1, by omega⟩) := by
  obtain ⟨hE, hO⟩ :=
    oddEvenFront_recursive_outputs_sorted_of_two_runs k v ih hA hB
  exact monotone_value_shift_of_threshold_counts
    (fun i => (oddEvenFront k).exec v (evenEmbed k i))
    (fun i => (oddEvenFront k).exec v (oddEmbed k i))
    hE hO (oddEvenFront_same_rank_order k v hA hB) hcounts

/-- Count gaps in the two input parity subsequences pass through their
recursive submerges unchanged. -/
theorem oddEvenFront_preserves_parity_count_gap (k : Nat) (v : Fin (2 ^ (k + 2)) → Bool)
    (hEO : boolTrueCount (v ∘ evenEmbed k) ≤ boolTrueCount (v ∘ oddEmbed k) + 2)
    (hOE : boolTrueCount (v ∘ oddEmbed k) ≤ boolTrueCount (v ∘ evenEmbed k) + 2) :
    boolTrueCount (fun i => (oddEvenFront k).exec v (evenEmbed k i)) ≤
        boolTrueCount (fun i => (oddEvenFront k).exec v (oddEmbed k i)) + 2 ∧
    boolTrueCount (fun i => (oddEvenFront k).exec v (oddEmbed k i)) ≤
        boolTrueCount (fun i => (oddEvenFront k).exec v (evenEmbed k i)) + 2 := by
  have he : (fun i => (oddEvenFront k).exec v (evenEmbed k i)) =
      (oddEvenMergeNet (k + 1)).exec (v ∘ evenEmbed k) := by
    funext i
    exact oddEvenFront_exec_even k v i
  have ho : (fun i => (oddEvenFront k).exec v (oddEmbed k i)) =
      (oddEvenMergeNet (k + 1)).exec (v ∘ oddEmbed k) := by
    funext i
    exact oddEvenFront_exec_odd k v i
  rw [he, ho]
  simp only [boolTrueCount_exec]
  exact ⟨hEO, hOE⟩

/-- At every value threshold, the recursive front's odd output has at most
two more qualifying wires than its even output. This is the input parity
count gap, preserved by each recursive submerge and transported through
thresholding. -/
theorem oddEvenFront_threshold_count_gap {α : Type} [LinearOrder α]
    (k : Nat) (v : Fin (2 ^ (k + 2)) → α)
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    ∀ t : α,
      boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (oddEmbed k i))) ≤
        boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (evenEmbed k i))) + 2 := by
  intro t
  let b : Fin (2 ^ (k + 2)) → Bool := fun i => decide (t ≤ v i)
  have hbA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      b (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))) := by
    intro i j hij
    by_cases hi : t ≤ v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))
    · have hj : t ≤ v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) j)) :=
        hi.trans (hA hij)
      simp [b, hi, hj]
    · simp [b, hi]
  have hbB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      b (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i))) := by
    intro i j hij
    change decide (t ≤ v (Fin.cast (powPairSizeEq (k + 1))
        (Fin.natAdd (2 ^ (k + 1)) i))) ≤
      decide (t ≤ v (Fin.cast (powPairSizeEq (k + 1))
        (Fin.natAdd (2 ^ (k + 1)) j)))
    by_cases hi : t ≤ v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i))
    · have hj : t ≤ v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) j)) :=
        hi.trans (hB hij)
      rw [decide_eq_true hi, decide_eq_true hj]
    · rw [decide_eq_false hi]
      exact Bool.false_le _
  obtain ⟨hinputE, hinputO⟩ := oddEven_parity_input_count_gap k b hbA hbB
  obtain ⟨hfrontE, hfrontO⟩ :=
    oddEvenFront_preserves_parity_count_gap k b hinputE hinputO
  have hconvE : (fun i => (oddEvenFront k).exec b (evenEmbed k i)) =
      (fun i => decide (t ≤ (oddEvenFront k).exec v (evenEmbed k i))) := by
    funext i
    exact congrFun (exec_threshold (oddEvenFront k) v t) (evenEmbed k i)
  have hconvO : (fun i => (oddEvenFront k).exec b (oddEmbed k i)) =
      (fun i => decide (t ≤ (oddEvenFront k).exec v (oddEmbed k i))) := by
    funext i
    exact congrFun (exec_threshold (oddEvenFront k) v t) (oddEmbed k i)
  rw [← hconvE, ← hconvO]
  exact hfrontO

/-- The shifted parity inequality follows from the recursive sorting
hypothesis alone, for two sorted source runs: its same-rank and threshold
count premises are both supplied by the preceding lemmas. -/
theorem oddEvenFront_shift_from_two_runs {α : Type} [LinearOrder α]
    (k : Nat) (v : Fin (2 ^ (k + 2)) → α)
    (ih : ∀ w : Fin (2 ^ (k + 1)) → α,
      (Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
       Monotone (fun i : Fin (2 ^ k) =>
        w (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) →
      Monotone ((oddEvenMergeNet (k + 1)).exec w))
    (hA : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.castAdd (2 ^ (k + 1)) i))))
    (hB : Monotone (fun i : Fin (2 ^ (k + 1)) =>
      v (Fin.cast (powPairSizeEq (k + 1)) (Fin.natAdd (2 ^ (k + 1)) i)))) :
    ∀ (i : Fin (2 ^ (k + 1))) (hi : 0 < i.val)
      (hbound : i.val + 1 < 2 ^ (k + 1)),
      (oddEvenFront k).exec v (oddEmbed k ⟨i.val - 1, by omega⟩) ≤
        (oddEvenFront k).exec v (evenEmbed k ⟨i.val + 1, by omega⟩) := by
  exact oddEvenFront_shift_of_two_runs k v ih hA hB
    (oddEvenFront_threshold_count_gap k v hA hB)

/-- The value-level shifted inequality for the actual even and odd outputs
of the recursive front. The recursive merge proof only needs to establish
these three structural hypotheses and the threshold count bound. -/
theorem oddEvenFront_shift {k : Nat} {α : Type} [LinearOrder α]
    (v : Fin (2 ^ (k + 2)) → α)
    (hE : Monotone (fun i => (oddEvenFront k).exec v (evenEmbed k i)))
    (hO : Monotone (fun i => (oddEvenFront k).exec v (oddEmbed k i)))
    (hEO : ∀ i, (oddEvenFront k).exec v (evenEmbed k i) ≤
      (oddEvenFront k).exec v (oddEmbed k i))
    (hcounts : ∀ t : α,
      boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (oddEmbed k i))) ≤
        boolTrueCount (fun i => decide (t ≤ (oddEvenFront k).exec v (evenEmbed k i))) + 2) :
    ∀ (i : Fin (2 ^ (k + 1))) (hi : 0 < i.val)
      (hbound : i.val + 1 < 2 ^ (k + 1)),
      (oddEvenFront k).exec v (oddEmbed k ⟨i.val - 1, by omega⟩) ≤
        (oddEvenFront k).exec v (evenEmbed k ⟨i.val + 1, by omega⟩) := by
  exact monotone_value_shift_of_threshold_counts
    (fun i => (oddEvenFront k).exec v (evenEmbed k i))
    (fun i => (oddEvenFront k).exec v (oddEmbed k i))
    hE hO hEO hcounts


/-- Batcher's odd-even merge sorts every concatenation of two ascending runs.
This is correctness for the actual comparator network, at every power-of-two
width, with no assumption on the relative values of the two runs. -/
theorem oddEvenMergeNet_sorts_two_runs {α : Type} [LinearOrder α] :
    ∀ (k : Nat) (v : Fin (2 ^ (k + 1)) → α),
      (Monotone (fun i : Fin (2 ^ k) =>
        v (Fin.cast (powPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
       Monotone (fun i : Fin (2 ^ k) =>
        v (Fin.cast (powPairSizeEq k) (Fin.natAdd (2 ^ k) i)))) →
      Monotone ((oddEvenMergeNet (k + 1)).exec v) := by
  intro k
  induction k with
  | zero =>
    intro v _
    apply monotone_fin_of_adjacent _ (by norm_num)
    intro i
    have hiv : i.val = 0 := by have hi := i.isLt; norm_num at hi; omega
    simp [oddEvenMergeNet, ComparatorNetwork.exec, Comparator.apply, hiv]
  | succ k ih =>
    intro v h
    obtain ⟨hA, hB⟩ := h
    rw [oddEvenMergeNet_exec_succ_succ]
    obtain ⟨hE, hO⟩ := oddEvenFront_recursive_outputs_sorted_of_two_runs k v ih hA hB
    exact oddEvenCrossLayer_sorts_of_profile ((oddEvenFront k).exec v) hE hO
      (oddEvenFront_same_rank_order k v hA hB)
      (oddEvenFront_shift_from_two_runs k v ih hA hB)

/-- The odd-even merge has logarithmic depth: the two parity submerges are
wire-disjoint and the final correction is one parallel layer. -/
theorem oddEvenMergeNet_depth_le : ∀ k : Nat, (oddEvenMergeNet k).depth ≤ k
  | 0 => by simp [oddEvenMergeNet, ComparatorNetwork.depth]
  | 1 => by norm_num [oddEvenMergeNet, ComparatorNetwork.depth, depthStep]
  | k + 2 => by
      let e := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (evenEmbed k)
      let o := (oddEvenMergeNet (k + 1)).scatterEmbed (2 ^ (k + 2)) (oddEmbed k)
      let front : ComparatorNetwork (2 ^ (k + 2)) := ⟨e.comparators ++ o.comparators⟩
      have he : e.depth ≤ k + 1 :=
        (depth_scatterEmbed_le _ _ _).trans (oddEvenMergeNet_depth_le (k + 1))
      have ho : o.depth ≤ k + 1 :=
        (depth_scatterEmbed_le _ _ _).trans (oddEvenMergeNet_depth_le (k + 1))
      have hfront : front.depth ≤ k + 1 := by
        have hflat := depth_flatMap_disjoint [false, true]
          (fun b => if b then o.comparators else e.comparators) (k + 1)
          (by intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
              rcases hb with rfl | rfl <;> simp [ho, he])
          (by
            refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
            intro b hb
            have hb' : b = true := by simpa using hb
            subst b
            intro c hc d hd
            dsimp only [e, o, ComparatorNetwork.scatterEmbed] at hc hd
            rcases List.mem_map.mp hc with ⟨ce, -, hce⟩
            rcases List.mem_map.mp hd with ⟨cd, -, hcd⟩
            have hci : evenEmbed k ce.i = c.i := congrArg Comparator.i hce
            have hcj : evenEmbed k ce.j = c.j := congrArg Comparator.j hce
            have hdi : oddEmbed k cd.i = d.i := congrArg Comparator.i hcd
            have hdj : oddEmbed k cd.j = d.j := congrArg Comparator.j hcd
            have h1 := even_odd_images_disjoint k ce.i cd.i
            have h2 := even_odd_images_disjoint k ce.i cd.j
            have h3 := even_odd_images_disjoint k ce.j cd.i
            have h4 := even_odd_images_disjoint k ce.j cd.j
            change (c.i ≠ d.i ∧ c.i ≠ d.j) ∧ (c.j ≠ d.i ∧ c.j ≠ d.j)
            exact ⟨⟨fun h => h1 (hci.trans (h.trans hdi.symm)),
              fun h => h2 (hci.trans (h.trans hdj.symm))⟩,
              ⟨fun h => h3 (hcj.trans (h.trans hdi.symm)),
              fun h => h4 (hcj.trans (h.trans hdj.symm))⟩⟩)
        simpa [front] using hflat
      have htail := oddEvenCrossLayer_depth_le k
      have happend := depth_append_le front (oddEvenCrossLayer k)
      change (front.append (oddEvenCrossLayer k)).depth ≤ k + 2
      exact happend.trans (by omega)

theorem oddEvenMergeNet64_depth_le : (oddEvenMergeNet 6).depth ≤ 6 :=
  oddEvenMergeNet_depth_le 6

/-- Two ascending 32-wire runs are merged on their original increasing wire
order, with no reversal or wire permutation. -/
theorem oddEvenMergeNet64_sorts_two_runs {α : Type} [LinearOrder α]
    (v : Fin 64 → α)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    Monotone ((oddEvenMergeNet 6).exec v) := by
  apply oddEvenMergeNet_sorts_two_runs 5 v
  constructor
  · simpa using hA
  · simpa using hB

/-- A chosen, increasing 64-wire support admits the same six-layer merge
when its first and last 32 wires are ascending runs. -/
theorem oddEvenMergeNet64_scatter_sorts {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 64 ↪o Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin 32 => v (e (Fin.castAdd 32 i))))
    (hB : Monotone (fun i : Fin 32 => v (e (Fin.natAdd 32 i)))) :
    Monotone (fun i => ((oddEvenMergeNet 6).scatterEmbed N e).exec v (e i)) := by
  have hs := oddEvenMergeNet64_sorts_two_runs (v ∘ e) hA hB
  simpa only [ComparatorNetwork.scatterEmbed_exec_inside] using hs

theorem oddEvenMergeNet64_scatter_depth_le {N : Nat} (e : Fin 64 ↪o Fin N) :
    ((oddEvenMergeNet 6).scatterEmbed N e).depth ≤ 6 :=
  (depth_scatterEmbed_le _ _ _).trans oddEvenMergeNet64_depth_le

/-- The two parity output lanes are sorted packets. The wire designations
are fixed and independent of the values being merged. -/
theorem oddEvenMergeNet64_dealt_lanes_sorted {α : Type} [LinearOrder α]
    (v : Fin 64 → α)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    Monotone (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (evenWire 32 i)) ∧
    Monotone (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (oddWire 32 i)) := by
  have hs := oddEvenMergeNet64_sorts_two_runs v hA hB
  constructor
  · intro i j hij
    apply hs
    apply Fin.mk_le_mk.mpr
    change 2 * i.val ≤ 2 * j.val
    have hv := Fin.le_iff_val_le_val.mp hij
    omega
  · intro i j hij
    apply hs
    apply Fin.mk_le_mk.mpr
    change 2 * i.val + 1 ≤ 2 * j.val + 1
    have hv := Fin.le_iff_val_le_val.mp hij
    omega

/-- For every Boolean input made of two ascending runs, dealing the merged
output gives the odd lane at most one more true value than the even lane. -/
theorem oddEvenMergeNet64_dealt_count_gap (v : Fin 64 → Bool)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    boolTrueCount (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (evenWire 32 i)) ≤
      boolTrueCount (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (oddWire 32 i)) ∧
    boolTrueCount (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (oddWire 32 i)) ≤
      boolTrueCount (fun i : Fin 32 => (oddEvenMergeNet 6).exec v (evenWire 32 i)) + 1 := by
  have hs := oddEvenMergeNet64_sorts_two_runs v hA hB
  exact ⟨monotone_even_count_le_odd _ hs, monotone_odd_count_le_even_add_one _ hs⟩

theorem sorted64_even_odd_interleave {α : Type} [Preorder α]
    (w : Fin 64 → α) (hw : Monotone w) :
    ∀ i : Fin 31,
      w ⟨2 * i.val, by have := i.isLt; omega⟩ ≤
        w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ∧
      w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤
        w ⟨2 * i.val + 2, by have := i.isLt; omega⟩ := by
  intro i
  constructor <;> apply hw <;> simp <;> omega

theorem oddEvenMergeNet64_parity_profile {α : Type} [LinearOrder α]
    (v : Fin 64 → α)
    (hs : Monotone ((oddEvenMergeNet 6).exec v)) :
    ∀ i : Fin 31,
      (oddEvenMergeNet 6).exec v ⟨2 * i.val, by have := i.isLt; omega⟩ ≤
        (oddEvenMergeNet 6).exec v ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ∧
      (oddEvenMergeNet 6).exec v ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤
        (oddEvenMergeNet 6).exec v ⟨2 * i.val + 2, by have := i.isLt; omega⟩ :=
  sorted64_even_odd_interleave _ hs

def twoRunThreshold64 (a b : Fin 33) : Fin 64 → Bool := fun i =>
  if i.val < 32 then decide (a.val ≤ i.val)
  else decide (b.val ≤ i.val - 32)

end Chvatal.PacketAlignment
