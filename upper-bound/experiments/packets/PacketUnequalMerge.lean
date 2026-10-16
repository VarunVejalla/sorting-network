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

private theorem unequalBoolCount_append {m n : Nat} (A : Fin m → Bool)
    (B : Fin n → Bool) :
    boolTrueCount (Fin.append A B) = boolTrueCount A + boolTrueCount B := by
  let p : Fin m ⊕ Fin n → Prop
    | Sum.inl i => A i = true
    | Sum.inr j => B j = true
  have hp (s : Fin m ⊕ Fin n) :
      p s ↔ Fin.append A B (finSumFinEquiv s) = true := by
    cases s with
    | inl i => simp [p]
    | inr j =>
        change (B j = true) ↔ Fin.addCases A B (Fin.natAdd m j) = true
        rw [Fin.addCases_right]
  let e : {i : Fin (m + n) // Fin.append A B i = true} ≃
      Sum ({i : Fin m // A i = true}) ({j : Fin n // B j = true}) :=
    (finSumFinEquiv.subtypeEquiv hp).symm.trans Equiv.subtypeSum
  unfold boolTrueCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr e

private theorem decide_threshold_append {m n : Nat} {α : Type} [LinearOrder α]
    (A : Fin m → α) (B : Fin n → α) (t : α) :
    (fun i => decide (t ≤ Fin.append A B i)) =
      Fin.append (fun i => decide (t ≤ A i)) (fun i => decide (t ≤ B i)) := by
  funext i
  rcases hidx : finSumFinEquiv.symm i with j | j
  · have hi : i = Fin.castAdd n j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    rw [hi]
    simp only [Fin.append_left]
  · have hi : i = Fin.natAdd m j := by
      have h := congrArg finSumFinEquiv hidx
      simpa using h
    rw [hi]
    simp only [Fin.append_right]

private def unequalEvenIndex {m : Nat} (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val, by have hi := i.isLt; omega⟩

private def unequalOddIndex {m : Nat} (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩

private def unequalEvenIndexOddLength {m : Nat} (i : Fin m) :
    Fin (2 * m - 1) :=
  ⟨2 * i.val, by have hi := i.isLt; omega⟩

private def unequalOddIndexOddLength {m : Nat} (i : Fin (m - 1)) :
    Fin (2 * m - 1) :=
  ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩

/-- In a sorted Boolean run of odd length, the even lane has at most one more
true value than the odd lane; only the last even position can be unpaired. -/
private theorem oddLength_even_count_le_odd_add_one {m : Nat}
    (v : Fin (2 * m - 1) → Bool) (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (unequalEvenIndexOddLength i)) ≤
      boolTrueCount (fun i : Fin (m - 1) => v (unequalOddIndexOddLength i)) + 1 := by
  let f : {i : Fin m // v (unequalEvenIndexOddLength i) = true} →
      ({i : Fin (m - 1) // v (unequalOddIndexOddLength i) = true} ⊕ Unit) :=
    fun x => if hi : x.1.val + 1 < m then
      Sum.inl ⟨⟨x.1.val, by omega⟩, by
        have hp : unequalEvenIndexOddLength x.1 ≤
            unequalOddIndexOddLength ⟨x.1.val, by omega⟩ := by
          apply Fin.mk_le_mk.mpr
          simp [unequalEvenIndexOddLength, unequalOddIndexOddLength]
        have h := hv hp
        cases hval : v (unequalOddIndexOddLength ⟨x.1.val, by omega⟩) with
        | false =>
            have htf : true ≤ false := by simpa [x.2, hval] using h
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) htf)
        | true => simpa [hval]⟩
    else Sum.inr Unit.unit
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.1.val + 1 < m <;> by_cases hy : y.1.val + 1 < m
    · simp [f, hx, hy] at hxy
      apply Subtype.ext
      exact Fin.ext hxy
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
      apply Subtype.ext
      apply Fin.ext
      have hxlt := x.1.isLt
      have hylt := y.1.isLt
      omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, boolTrueCount] using hcard

/-- In a sorted Boolean run of odd length, every true odd position injects
into the following even position. -/
private theorem oddLength_odd_count_le_even {m : Nat}
    (v : Fin (2 * m - 1) → Bool) (hv : Monotone v) :
    boolTrueCount (fun i : Fin (m - 1) => v (unequalOddIndexOddLength i)) ≤
      boolTrueCount (fun i : Fin m => v (unequalEvenIndexOddLength i)) := by
  let f : {i : Fin (m - 1) // v (unequalOddIndexOddLength i) = true} →
      {i : Fin m // v (unequalEvenIndexOddLength i) = true} := fun x =>
    ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩, by
      have hp : unequalOddIndexOddLength x.1 ≤
          unequalEvenIndexOddLength ⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩ := by
        apply Fin.mk_le_mk.mpr
        simp [unequalOddIndexOddLength, unequalEvenIndexOddLength]
      have h := hv hp
      cases hval : v (unequalEvenIndexOddLength ⟨x.1.val + 1, by omega⟩) with
      | false =>
          have htf : true ≤ false := by simpa [x.2, hval] using h
          exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) htf)
      | true => simpa [hval]⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg (fun z : {i : Fin m // _} => z.1.val) hxy
    dsimp [f] at hv
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, boolTrueCount] using hcard

/-- For two sorted source runs of lengths `2m` and `2m-1`, their even and odd
parity projections have threshold counts within one. -/
theorem unequalSourceParityThresholdGap {m : Nat} {α : Type} [LinearOrder α]
    (A : Fin (2 * m) → α) (B : Fin (2 * m - 1) → α)
    (hA : Monotone A) (hB : Monotone B) :
    ∀ t : α,
      unequalThresholdCount
        (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
          (fun i : Fin m => B (unequalEvenIndexOddLength i))) t ≤
          unequalThresholdCount
            (Fin.append (fun i : Fin m => A (unequalOddIndex i))
              (fun i : Fin (m - 1) => B (unequalOddIndexOddLength i))) t + 1 ∧
      unequalThresholdCount
        (Fin.append (fun i : Fin m => A (unequalOddIndex i))
          (fun i : Fin (m - 1) => B (unequalOddIndexOddLength i))) t ≤
          unequalThresholdCount
            (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
              (fun i : Fin m => B (unequalEvenIndexOddLength i))) t + 1 := by
  intro t
  let a : Fin (2 * m) → Bool := fun i => decide (t ≤ A i)
  let b : Fin (2 * m - 1) → Bool := fun i => decide (t ≤ B i)
  have ha : Monotone a := by
    intro i j hij
    by_cases hi : t ≤ A i
    · have hj : t ≤ A j := hi.trans (hA hij)
      simp [a, hi, hj]
    · simp [a, hi]
  have hb : Monotone b := by
    intro i j hij
    by_cases hi : t ≤ B i
    · have hj : t ≤ B j := hi.trans (hB hij)
      simp [b, hi, hj]
    · simp [b, hi]
  have hAlo := monotone_even_count_le_odd a ha
  have hAhi := monotone_odd_count_le_even_add_one a ha
  have hAlo' :
      boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) ≤
        boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) := by
    change boolTrueCount (fun i : Fin m => a (evenWire m i)) ≤ _
    exact hAlo
  have hAhi' :
      boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) ≤
        boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) + 1 := by
    change boolTrueCount (fun i : Fin m => a (oddWire m i)) ≤ _
    exact hAhi
  have hBlo := oddLength_odd_count_le_even b hb
  have hBhi := oddLength_even_count_le_odd_add_one b hb
  have hconv (f : Fin (m + m) → α) :
      unequalThresholdCount f t = boolTrueCount (fun i => decide (t ≤ f i)) := by
    simp [unequalThresholdCount, boolTrueCount]
  have hconvOdd (f : Fin (m + (m - 1)) → α) :
      unequalThresholdCount f t = boolTrueCount (fun i => decide (t ≤ f i)) := by
    simp [unequalThresholdCount, boolTrueCount]
  rw [hconv, hconvOdd, decide_threshold_append, decide_threshold_append,
    unequalBoolCount_append, unequalBoolCount_append]
  change
    boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) +
      boolTrueCount (fun i : Fin m => b (unequalEvenIndexOddLength i)) ≤
      boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) +
        boolTrueCount (fun i : Fin (m - 1) => b (unequalOddIndexOddLength i)) + 1 ∧
    boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) +
      boolTrueCount (fun i : Fin (m - 1) => b (unequalOddIndexOddLength i)) ≤
      boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) +
        boolTrueCount (fun i : Fin m => b (unequalEvenIndexOddLength i)) + 1
  constructor
  · have hsum := Nat.add_le_add hAlo' hBhi
    omega
  · have hsum := Nat.add_le_add hAhi' hBlo
    omega

/-- For two even-length sorted source runs, their even and odd projections
have equal length. The even lane's threshold count is never larger, and the
odd lane can exceed it by at most two (one unmatched terminal odd position
per source run). This is the profile invariant for the outer even/even
stages of the 63-run tail. -/
theorem evenSourceParityThresholdGap {m n : Nat} {α : Type} [LinearOrder α]
    (A : Fin (2 * m) → α) (B : Fin (2 * n) → α)
    (hA : Monotone A) (hB : Monotone B) :
    ∀ t : α,
      unequalThresholdCount
        (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
          (fun i : Fin n => B (unequalEvenIndex i))) t ≤
          unequalThresholdCount
            (Fin.append (fun i : Fin m => A (unequalOddIndex i))
              (fun i : Fin n => B (unequalOddIndex i))) t ∧
      unequalThresholdCount
        (Fin.append (fun i : Fin m => A (unequalOddIndex i))
          (fun i : Fin n => B (unequalOddIndex i))) t ≤
          unequalThresholdCount
            (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
              (fun i : Fin n => B (unequalEvenIndex i))) t + 2 := by
  intro t
  let a : Fin (2 * m) → Bool := fun i => decide (t ≤ A i)
  let b : Fin (2 * n) → Bool := fun i => decide (t ≤ B i)
  have ha : Monotone a := by
    intro i j hij
    by_cases hi : t ≤ A i
    · have hj : t ≤ A j := hi.trans (hA hij)
      simp [a, hi, hj]
    · simp [a, hi]
  have hb : Monotone b := by
    intro i j hij
    by_cases hi : t ≤ B i
    · have hj : t ≤ B j := hi.trans (hB hij)
      simp [b, hi, hj]
    · simp [b, hi]
  have hAlo := monotone_even_count_le_odd a ha
  have hAhi := monotone_odd_count_le_even_add_one a ha
  have hBlo := monotone_even_count_le_odd b hb
  have hBhi := monotone_odd_count_le_even_add_one b hb
  have hconv (f : Fin (m + n) → α) :
      unequalThresholdCount f t = boolTrueCount (fun i => decide (t ≤ f i)) := by
    simp [unequalThresholdCount, boolTrueCount]
  have hgapE := hconv (Fin.append
    (fun i : Fin m => A (unequalEvenIndex i))
    (fun i : Fin n => B (unequalEvenIndex i)))
  have hgapO := hconv (Fin.append
    (fun i : Fin m => A (unequalOddIndex i))
    (fun i : Fin n => B (unequalOddIndex i)))
  rw [hgapE, hgapO, decide_threshold_append, decide_threshold_append,
    unequalBoolCount_append, unequalBoolCount_append]
  have hAlo' : boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) ≤
      boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) := by
    change boolTrueCount (fun i : Fin m => a (evenWire m i)) ≤ _
    exact hAlo
  have hAhi' : boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) ≤
      boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) + 1 := by
    change boolTrueCount (fun i : Fin m => a (oddWire m i)) ≤ _
    exact hAhi
  have hBlo' : boolTrueCount (fun i : Fin n => b (unequalEvenIndex i)) ≤
      boolTrueCount (fun i : Fin n => b (unequalOddIndex i)) := by
    change boolTrueCount (fun i : Fin n => b (evenWire n i)) ≤ _
    exact hBlo
  have hBhi' : boolTrueCount (fun i : Fin n => b (unequalOddIndex i)) ≤
      boolTrueCount (fun i : Fin n => b (unequalEvenIndex i)) + 1 := by
    change boolTrueCount (fun i : Fin n => b (oddWire n i)) ≤ _
    exact hBhi
  change
    boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) +
      boolTrueCount (fun i : Fin n => b (unequalEvenIndex i)) ≤
        boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) +
          boolTrueCount (fun i : Fin n => b (unequalOddIndex i)) ∧
    boolTrueCount (fun i : Fin m => a (unequalOddIndex i)) +
      boolTrueCount (fun i : Fin n => b (unequalOddIndex i)) ≤
        boolTrueCount (fun i : Fin m => a (unequalEvenIndex i)) +
          boolTrueCount (fun i : Fin n => b (unequalEvenIndex i)) + 2
  exact ⟨Nat.add_le_add hAlo' hBlo', by
    have hsum := Nat.add_le_add hAhi' hBhi'
    omega⟩

/-- Comparator networks preserve the number of entries above every threshold.
This is the profile-level form of the fact that a comparator only permutes
its input values. -/
theorem unequalThresholdCount_exec {N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork N) (v : Fin N → α) (t : α) :
    unequalThresholdCount (net.exec v) t = unequalThresholdCount v t := by
  have hconv (f : Fin N → α) :
      unequalThresholdCount f t = boolTrueCount (fun i => decide (t ≤ f i)) := by
    simp [unequalThresholdCount, boolTrueCount]
  rw [hconv, hconv, ← boolTrueCount_exec net (fun i => decide (t ≤ v i)),
    exec_threshold]

/-- Applying independent networks to two lanes preserves a unit threshold-
count gap between their rank profiles. No sorting hypothesis on the networks
is needed here; only the permutation semantics of comparator networks. -/
theorem unequalThresholdGap_exec {M N : Nat} {α : Type} [LinearOrder α]
    (netE : ComparatorNetwork M) (netO : ComparatorNetwork N)
    (E : Fin M → α) (O : Fin N → α)
    (hgap : ∀ t : α,
      unequalThresholdCount E t ≤ unequalThresholdCount O t + 1 ∧
      unequalThresholdCount O t ≤ unequalThresholdCount E t + 1) :
    ∀ t : α,
      unequalThresholdCount (netE.exec E) t ≤
        unequalThresholdCount (netO.exec O) t + 1 ∧
      unequalThresholdCount (netO.exec O) t ≤
        unequalThresholdCount (netE.exec E) t + 1 := by
  intro t
  rw [unequalThresholdCount_exec, unequalThresholdCount_exec]
  exact hgap t

/-- Reindexing a profile along the canonical equivalence between equal-sized
`Fin` types does not change its threshold counts. -/
theorem unequalThresholdCount_cast {M N : Nat} (h : N = M)
    {α : Type} [LinearOrder α] (f : Fin M → α) (t : α) :
    unequalThresholdCount (fun i : Fin N => f (Fin.cast h i)) t =
      unequalThresholdCount f t := by
  classical
  let e : {i : Fin N // t ≤ f (Fin.cast h i)} ≃ {i : Fin M // t ≤ f i} := {
    toFun := fun i => ⟨Fin.cast h i.1, i.2⟩
    invFun := fun i => ⟨Fin.cast h.symm i.1, by simpa using i.2⟩
    left_inv := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      simp
    right_inv := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      simp
  }
  unfold unequalThresholdCount
  exact Fintype.card_congr e

private theorem unequalMonotone_cast {M N : Nat} (h : N = M)
    {α : Type} [Preorder α] (f : Fin M → α) (hf : Monotone f) :
    Monotone (fun i : Fin N => f (Fin.cast h i)) := by
  intro i j hij
  apply hf
  apply Fin.mk_le_mk.mpr
  have hij' : i.val ≤ j.val := Fin.mk_le_mk.mp hij
  simpa using hij'

/-- The recursive parity split has lane sizes `m+m` and `m+(m-1)`, while
the interleave/correction interface uses `2*m` and `2*m-1`. This theorem
transports the profile gap across those canonical `Fin` casts after the
actual lane networks have run. -/
theorem unequalSourceParityThresholdGap_exec_cast {m : Nat} {α : Type}
    [LinearOrder α] (A : Fin (2 * m) → α) (B : Fin (2 * m - 1) → α)
    (hA : Monotone A) (hB : Monotone B)
    (netE : ComparatorNetwork (m + m))
    (netO : ComparatorNetwork (m + (m - 1))) :
    ∀ t : α,
      unequalThresholdCount
        (fun i : Fin (2 * m) =>
          netE.exec (Fin.append (fun j : Fin m => A (unequalEvenIndex j))
            (fun j : Fin m => B (unequalEvenIndexOddLength j)))
            (Fin.cast (by omega : 2 * m = m + m) i)) t ≤
          unequalThresholdCount
            (fun i : Fin (2 * m - 1) =>
              netO.exec (Fin.append (fun j : Fin m => A (unequalOddIndex j))
                (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j)))
                (Fin.cast (by omega : 2 * m - 1 = m + (m - 1)) i)) t + 1 ∧
      unequalThresholdCount
        (fun i : Fin (2 * m - 1) =>
          netO.exec (Fin.append (fun j : Fin m => A (unequalOddIndex j))
            (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j)))
            (Fin.cast (by omega : 2 * m - 1 = m + (m - 1)) i)) t ≤
          unequalThresholdCount
            (fun i : Fin (2 * m) =>
              netE.exec (Fin.append (fun j : Fin m => A (unequalEvenIndex j))
                (fun j : Fin m => B (unequalEvenIndexOddLength j)))
                (Fin.cast (by omega : 2 * m = m + m) i)) t + 1 := by
  let e0 : Fin (m + m) → α := Fin.append
    (fun j : Fin m => A (unequalEvenIndex j))
    (fun j : Fin m => B (unequalEvenIndexOddLength j))
  let o0 : Fin (m + (m - 1)) → α := Fin.append
    (fun j : Fin m => A (unequalOddIndex j))
    (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j))
  let E : Fin (2 * m) → α := fun i =>
    netE.exec e0 (Fin.cast (by omega : 2 * m = m + m) i)
  let O : Fin (2 * m - 1) → α := fun i =>
    netO.exec o0 (Fin.cast (by omega : 2 * m - 1 = m + (m - 1)) i)
  intro t
  have hnative := unequalThresholdGap_exec netE netO _ _
    (unequalSourceParityThresholdGap A B hA hB) t
  have hE : unequalThresholdCount E t = unequalThresholdCount (netE.exec e0) t := by
    exact unequalThresholdCount_cast (by omega : 2 * m = m + m) (netE.exec e0) t
  have hO : unequalThresholdCount O t = unequalThresholdCount (netO.exec o0) t := by
    exact unequalThresholdCount_cast (by omega : 2 * m - 1 = m + (m - 1))
      (netO.exec o0) t
  rw [hE, hO]
  exact hnative

/-- Thus, for sorted source runs of lengths `2m` and `2m-1`, *any* recursive
comparator networks on their even and odd projections preserve the profile
gap needed by the final unequal correction layer. This isolates the invariant
induction step from the details of how each lane is sorted. -/
theorem unequalSourceParityThresholdGap_exec {m : Nat} {α : Type} [LinearOrder α]
    (A : Fin (2 * m) → α) (B : Fin (2 * m - 1) → α)
    (hA : Monotone A) (hB : Monotone B)
    (netE : ComparatorNetwork (m + m))
    (netO : ComparatorNetwork (m + (m - 1))) :
    ∀ t : α,
      unequalThresholdCount
        (netE.exec (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
          (fun i : Fin m => B (unequalEvenIndexOddLength i)))) t ≤
          unequalThresholdCount
            (netO.exec (Fin.append (fun i : Fin m => A (unequalOddIndex i))
              (fun i : Fin (m - 1) => B (unequalOddIndexOddLength i)))) t + 1 ∧
      unequalThresholdCount
        (netO.exec (Fin.append (fun i : Fin m => A (unequalOddIndex i))
          (fun i : Fin (m - 1) => B (unequalOddIndexOddLength i)))) t ≤
          unequalThresholdCount
            (netE.exec (Fin.append (fun i : Fin m => A (unequalEvenIndex i))
              (fun i : Fin m => B (unequalEvenIndexOddLength i)))) t + 1 := by
  exact unequalThresholdGap_exec netE netO _ _
    (unequalSourceParityThresholdGap A B hA hB)

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

/-- For equal-length sorted profiles, the asymmetric threshold-count bounds
`count(E) ≤ count(O) ≤ count(E)+2` imply exactly the cross-rank inequalities
needed by one odd-even correction layer. -/
theorem equal_cross_bounds_of_threshold_gap {L : Nat} {α : Type}
    [LinearOrder α] (E O : Fin L → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEcount : ∀ t, unequalThresholdCount E t ≤ unequalThresholdCount O t)
    (hOcount : ∀ t, unequalThresholdCount O t ≤ unequalThresholdCount E t + 2) :
    (∀ i : Fin L, E i ≤ O i) ∧
    (∀ i : Fin L, ∀ hi : i.val + 2 < L, O i ≤ E ⟨i.val + 2, hi⟩) := by
  constructor
  · intro i
    by_contra hnot
    have hlt : O i < E i := lt_of_not_ge hnot
    let t := E i
    have hElower := unequalThresholdCount_lower E hE i t (by simp [t])
    have hOupper := unequalThresholdCount_upper O hO i t (by simp [t, hlt])
    have hcnt := hEcount t
    omega
  · intro i hi
    by_contra hnot
    have hlt : E ⟨i.val + 2, hi⟩ < O i := lt_of_not_ge hnot
    let t := O i
    have hOlower := unequalThresholdCount_lower O hO i t (by simp [t])
    have hEupper := unequalThresholdCount_upper E hE ⟨i.val + 2, hi⟩ t
      (by simp [t, hlt])
    have hEupper' : unequalThresholdCount E t ≤ L - (i.val + 3) := by
      simpa using hEupper
    have hcnt := hOcount t
    omega

/-- Independent lane networks preserve the asymmetric `0/2` profile gap of
two even source runs. -/
private def evenEvenParityLane {m n : Nat} {α : Type}
    (A : Fin (2 * m) → α) (B : Fin (2 * n) → α) : Fin (m + n) → α :=
  Fin.append (fun i : Fin m => A (unequalEvenIndex i))
    (fun i : Fin n => B (unequalEvenIndex i))

private def oddEvenParityLane {m n : Nat} {α : Type}
    (A : Fin (2 * m) → α) (B : Fin (2 * n) → α) : Fin (m + n) → α :=
  Fin.append (fun i : Fin m => A (unequalOddIndex i))
    (fun i : Fin n => B (unequalOddIndex i))

theorem evenSourceParityThresholdGap_exec {m n : Nat} {α : Type}
    [LinearOrder α] (A : Fin (2 * m) → α) (B : Fin (2 * n) → α)
    (hA : Monotone A) (hB : Monotone B)
    (netE netO : ComparatorNetwork (m + n)) :
    ∀ t : α,
      unequalThresholdCount (netE.exec (evenEvenParityLane A B)) t ≤
        unequalThresholdCount (netO.exec (oddEvenParityLane A B)) t ∧
      unequalThresholdCount (netO.exec (oddEvenParityLane A B)) t ≤
        unequalThresholdCount (netE.exec (evenEvenParityLane A B)) t + 2 := by
  intro t
  rw [unequalThresholdCount_exec, unequalThresholdCount_exec]
  simpa [evenEvenParityLane, oddEvenParityLane] using
    (evenSourceParityThresholdGap A B hA hB t)

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

/-- Min/max interleave for two equal parity lanes after comparing every odd
wire with the following even wire. The final odd wire is left untouched. -/
def equalCorrectedInterleave {L : Nat} (hL : 2 ≤ L) {α : Type} [LinearOrder α]
    (E O : Fin L → α) (j : Fin (2 * L)) : α := by
  have hj := j.isLt
  by_cases hz : j.val = 0
  · exact E ⟨0, by omega⟩
  · by_cases hlast : j.val = 2 * L - 1
    · exact O ⟨L - 1, by omega⟩
    · by_cases heven : j.val % 2 = 0
      · exact max (O ⟨j.val / 2 - 1, by omega⟩) (E ⟨j.val / 2, by omega⟩)
      · exact min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩)

/-- A one-sided profile gap of zero/two yields the rank inequalities needed
to sort the equal-lane correction interleave. -/
theorem equalCorrectedInterleave_sorted {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E O : Fin L → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEO : ∀ i : Fin L, E i ≤ O i)
    (hshift : ∀ i : Fin L, ∀ hi : i.val + 2 < L,
      O i ≤ E ⟨i.val + 2, hi⟩) :
    Monotone (equalCorrectedInterleave hL E O) := by
  apply monotone_fin_of_adjacent_local _ (by have := Nat.two_pow_pos 1; omega)
  intro j
  have hj : j.val + 1 < 2 * L := by have := j.isLt; omega
  by_cases hz : j.val = 0
  · have hcur : equalCorrectedInterleave hL E O ⟨j.val, by omega⟩ = E ⟨0, by omega⟩ := by
      simp [equalCorrectedInterleave, hz]
    have hnext : equalCorrectedInterleave hL E O ⟨j.val + 1, hj⟩ =
        min (O ⟨0, by omega⟩) (E ⟨1, by omega⟩) := by
      have hnotlast : j.val + 1 ≠ 2 * L - 1 := by omega
      have hnz : j.val + 1 ≠ 0 := by omega
      have hnextOdd : (j.val + 1) % 2 ≠ 0 := by omega
      have hq : (j.val + 1) / 2 = 0 := by omega
      simp [equalCorrectedInterleave, hnotlast, hnz, hnextOdd, hq]
    rw [hcur, hnext]
    exact le_min (hEO ⟨0, by omega⟩) (hE (Fin.mk_le_mk.mpr (by omega)))
  · by_cases hlast : j.val + 1 = 2 * L - 1
    · have hcur : equalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
          max (O ⟨L - 2, by omega⟩) (E ⟨L - 1, by omega⟩) := by
        have heven : j.val % 2 = 0 := by omega
        have hnotlast : j.val ≠ 2 * L - 1 := by omega
        have hdiv : j.val / 2 = L - 1 := by omega
        simp [equalCorrectedInterleave, hz, hnotlast, heven, hdiv]
        have hidx : (⟨L - 1 - 1, by omega⟩ : Fin L) = ⟨L - 2, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hidx]
      have hnext : equalCorrectedInterleave hL E O ⟨j.val + 1, hj⟩ =
          O ⟨L - 1, by omega⟩ := by
        have hnz : j.val + 1 ≠ 0 := by omega
        have hLastNZ : 2 * L - 1 ≠ 0 := by omega
        simp [equalCorrectedInterleave, hlast, hLastNZ]
      rw [hcur, hnext]
      apply max_le
      · exact hO (Fin.mk_le_mk.mpr (by omega))
      · exact hEO ⟨L - 1, by omega⟩
    · by_cases heven : j.val % 2 = 0
      · have hnextOdd : (j.val + 1) % 2 ≠ 0 := by omega
        have hcur : equalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
            max (O ⟨j.val / 2 - 1, by omega⟩) (E ⟨j.val / 2, by omega⟩) := by
          have hnotlast : j.val ≠ 2 * L - 1 := by omega
          simp [equalCorrectedInterleave, hz, hnotlast, heven]
        have hnext : equalCorrectedInterleave hL E O ⟨j.val + 1, hj⟩ =
            min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
          have hq : (j.val + 1) / 2 = j.val / 2 := by omega
          have hnz : j.val + 1 ≠ 0 := by omega
          simp [equalCorrectedInterleave, hlast, hnz, hnextOdd, hq]
        rw [hcur, hnext]
        apply max_le
        · let k : Fin L := ⟨j.val / 2 - 1, by omega⟩
          have hqBound : j.val / 2 + 1 < L := by omega
          have hkBound : k.val + 2 < L := by
            dsimp [k]
            omega
          have hcross := hshift k hkBound
          have hidx : (⟨k.val + 2, by omega⟩ : Fin L) = ⟨j.val / 2 + 1, by omega⟩ := by
            apply Fin.ext
            simp [k]
            omega
          rw [hidx] at hcross
          exact le_min (hO (Fin.mk_le_mk.mpr (by omega))) hcross
        · exact le_min (hEO ⟨j.val / 2, by omega⟩) (hE (Fin.mk_le_mk.mpr (by omega)))
      · have hnextEven : (j.val + 1) % 2 = 0 := by omega
        have hcur : equalCorrectedInterleave hL E O ⟨j.val, by omega⟩ =
            min (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
          have hnotlast : j.val ≠ 2 * L - 1 := by omega
          simp [equalCorrectedInterleave, hz, hnotlast, heven]
        have hnext : equalCorrectedInterleave hL E O ⟨j.val + 1, hj⟩ =
            max (O ⟨j.val / 2, by omega⟩) (E ⟨j.val / 2 + 1, by omega⟩) := by
          have hq : (j.val + 1) / 2 = j.val / 2 + 1 := by omega
          have hnextNotLast : j.val + 1 ≠ 2 * L - 1 := by omega
          have hnz : j.val + 1 ≠ 0 := by omega
          simp [equalCorrectedInterleave, hnextNotLast, hnz, hnextEven, hq]
        rw [hcur, hnext]
        exact (min_le_left _ _).trans (le_max_left _ _)

/-- Threshold-count form of the equal-lane correction theorem. -/
theorem equalCorrectedInterleave_sorted_of_threshold_gap {L : Nat}
    (hL : 2 ≤ L) {α : Type} [LinearOrder α] (E O : Fin L → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEcount : ∀ t, unequalThresholdCount E t ≤ unequalThresholdCount O t)
    (hOcount : ∀ t, unequalThresholdCount O t ≤ unequalThresholdCount E t + 2) :
    Monotone (equalCorrectedInterleave hL E O) := by
  exact equalCorrectedInterleave_sorted hL E O hE hO
    (equal_cross_bounds_of_threshold_gap E O hE hO hEcount hOcount).1
    (equal_cross_bounds_of_threshold_gap E O hE hO hEcount hOcount).2

/-- Interleave two equal-length parity lanes on `2*L` wires. -/
def equalInterleave {L : Nat} {α : Type} [LinearOrder α]
    (E O : Fin L → α) (j : Fin (2 * L)) : α :=
  if j.val % 2 = 0 then E ⟨j.val / 2, by have hj := j.isLt; omega⟩
  else O ⟨j.val / 2, by have hj := j.isLt; omega⟩

private def equalCorrectionPrefixEmbed {L : Nat} (hL : 2 ≤ L) :
    Fin (2 * L - 1) ↪o Fin (2 * L) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨i.val, by have hi := i.isLt; omega⟩)
    (by intro i j hij; exact Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hij))

/-- Extend the unequal correction layer by one untouched final wire. -/
def equalCorrectionLayer {L : Nat} (hL : 2 ≤ L) : ComparatorNetwork (2 * L) :=
  (unequalCorrectionLayer hL).scatterEmbed (2 * L) (equalCorrectionPrefixEmbed hL)

private def equalEvenEmbed {L : Nat} : Fin L ↪o Fin (2 * L) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val, by have hi := i.isLt; omega⟩)
    (by intro i j hij; exact Fin.mk_lt_mk.mpr (by have h := Fin.mk_lt_mk.mp hij; omega))

private def equalOddEmbed {L : Nat} : Fin L ↪o Fin (2 * L) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
    (by intro i j hij; exact Fin.mk_lt_mk.mpr (by have h := Fin.mk_lt_mk.mp hij; omega))

private theorem equalEven_not_odd {L : Nat} (i : Fin L) :
    (equalEvenEmbed i : Fin (2 * L)) ∉ Set.range equalOddEmbed := by
  rintro ⟨j, h⟩
  have hv := congrArg Fin.val h
  simp [equalEvenEmbed, equalOddEmbed] at hv
  omega

private theorem equalOdd_not_even {L : Nat} (i : Fin L) :
    (equalOddEmbed i : Fin (2 * L)) ∉ Set.range equalEvenEmbed := by
  rintro ⟨j, h⟩
  have hv := congrArg Fin.val h
  simp [equalEvenEmbed, equalOddEmbed] at hv
  omega

/-- Parallel front stage that runs the two lane networks on even and odd
physical wires. -/
def equalParityFront {L : Nat} (netE netO : ComparatorNetwork L) :
    ComparatorNetwork (2 * L) :=
  let e := netE.scatterEmbed (2 * L) equalEvenEmbed
  let o := netO.scatterEmbed (2 * L) equalOddEmbed
  ⟨e.comparators ++ o.comparators⟩

/-- The two equal-size parity lanes run in parallel because their wire supports
are disjoint. -/
theorem equalParityFront_depth_le {L : Nat} (netE netO : ComparatorNetwork L) :
    (equalParityFront netE netO).depth ≤ max netE.depth netO.depth := by
  let e := netE.scatterEmbed (2 * L) equalEvenEmbed
  let o := netO.scatterEmbed (2 * L) equalOddEmbed
  have he : e.depth ≤ max netE.depth netO.depth :=
    (depth_scatterEmbed_le _ _ _).trans (le_max_left _ _)
  have ho : o.depth ≤ max netE.depth netO.depth :=
    (depth_scatterEmbed_le _ _ _).trans (le_max_right _ _)
  have hflat := depth_flatMap_disjoint [false, true]
    (fun b => if b then o.comparators else e.comparators) (max netE.depth netO.depth)
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
      have hci : equalEvenEmbed ce.i = c.i := congrArg Comparator.i hce
      have hcj : equalEvenEmbed ce.j = c.j := congrArg Comparator.j hce
      have hdi : equalOddEmbed cd.i = d.i := congrArg Comparator.i hcd
      have hdj : equalOddEmbed cd.j = d.j := congrArg Comparator.j hcd
      have h1 := equalEven_not_odd ce.i
      have h2 := equalEven_not_odd ce.i
      have h3 := equalEven_not_odd ce.j
      have h4 := equalEven_not_odd ce.j
      change (c.i ≠ d.i ∧ c.i ≠ d.j) ∧ (c.j ≠ d.i ∧ c.j ≠ d.j)
      exact ⟨⟨fun h => h1 ⟨cd.i, hdi.trans (h.symm.trans hci.symm)⟩,
        fun h => h2 ⟨cd.j, hdj.trans (h.symm.trans hci.symm)⟩⟩,
        ⟨fun h => h3 ⟨cd.i, hdi.trans (h.symm.trans hcj.symm)⟩,
         fun h => h4 ⟨cd.j, hdj.trans (h.symm.trans hcj.symm)⟩⟩⟩)
  simpa [equalParityFront, e, o] using hflat

theorem equalParityFront_exec_even {L : Nat} (netE netO : ComparatorNetwork L)
    {α : Type} [LinearOrder α] (v : Fin (2 * L) → α) (i : Fin L) :
    (equalParityFront netE netO).exec v (equalEvenEmbed i) =
      netE.exec (fun j => v (equalEvenEmbed j)) i := by
  let e := netE.scatterEmbed (2 * L) equalEvenEmbed
  let o := netO.scatterEmbed (2 * L) equalOddEmbed
  change (⟨e.comparators ++ o.comparators⟩ : ComparatorNetwork (2 * L)).exec
    v (equalEvenEmbed i) = _
  rw [ComparatorNetwork.exec_append]
  rw [ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ (equalEven_not_odd i)]
  exact ComparatorNetwork.scatterEmbed_exec_inside _ _ _ _ _

theorem equalParityFront_exec_odd {L : Nat} (netE netO : ComparatorNetwork L)
    {α : Type} [LinearOrder α] (v : Fin (2 * L) → α) (i : Fin L) :
    (equalParityFront netE netO).exec v (equalOddEmbed i) =
      netO.exec (fun j => v (equalOddEmbed j)) i := by
  let e := netE.scatterEmbed (2 * L) equalEvenEmbed
  let o := netO.scatterEmbed (2 * L) equalOddEmbed
  change (⟨e.comparators ++ o.comparators⟩ : ComparatorNetwork (2 * L)).exec
    v (equalOddEmbed i) = _
  rw [ComparatorNetwork.exec_append]
  rw [ComparatorNetwork.scatterEmbed_exec_inside]
  apply congrArg (fun w : Fin L → α => netO.exec w i)
  funext j
  exact ComparatorNetwork.scatterEmbed_exec_outside netE (2 * L) equalEvenEmbed
    v (equalOddEmbed j) (equalOdd_not_even j)

theorem equalParityFront_exec_eq_interleave {L : Nat} {α : Type} [LinearOrder α]
    (netE netO : ComparatorNetwork L) (v : Fin (2 * L) → α) :
    (equalParityFront netE netO).exec v =
      equalInterleave (netE.exec (fun i => v (equalEvenEmbed i)))
        (netO.exec (fun i => v (equalOddEmbed i))) := by
  funext j
  by_cases heven : j.val % 2 = 0
  · let i : Fin L := ⟨j.val / 2, by have hj := j.isLt; omega⟩
    have hidx : equalEvenEmbed i = j := by
      apply Fin.ext
      simp [equalEvenEmbed, i]
      omega
    rw [← hidx, equalParityFront_exec_even]
    simp [equalInterleave, equalEvenEmbed, i]
  · let i : Fin L := ⟨j.val / 2, by have hj := j.isLt; omega⟩
    have hidx : equalOddEmbed i = j := by
      apply Fin.ext
      simp [equalOddEmbed, i]
      omega
    rw [← hidx, equalParityFront_exec_odd]
    simp [equalInterleave, equalOddEmbed, i]
    congr 1
    apply Fin.ext
    have hq : (2 * (j.val / 2) + 1) / 2 = j.val / 2 := by omega
    simpa [hq]

/-- One recursive equal-size merge step: parity lane networks, followed by
the concrete equal-lane correction layer. -/
def equalParityMergeNet {L : Nat} (hL : 2 ≤ L)
    (netE netO : ComparatorNetwork L) : ComparatorNetwork (2 * L) :=
  ⟨(equalParityFront netE netO).comparators ++ (equalCorrectionLayer hL).comparators⟩

theorem equalParityMergeNet_exec_eq {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (netE netO : ComparatorNetwork L)
    (v : Fin (2 * L) → α) :
    (equalParityMergeNet hL netE netO).exec v =
      (equalCorrectionLayer hL).exec
        (equalInterleave (netE.exec (fun i => v (equalEvenEmbed i)))
          (netO.exec (fun i => v (equalOddEmbed i)))) := by
  have h := ComparatorNetwork.exec_append (equalParityFront netE netO)
    (equalCorrectionLayer hL) v
  simpa [equalParityMergeNet, equalParityFront_exec_eq_interleave] using h

private def equalOddPrefix {L : Nat} (hL : 2 ≤ L) {α : Type}
    (O : Fin L → α) : Fin (L - 1) → α :=
  fun j => O ⟨j.val, by have hj := j.isLt; omega⟩

theorem equalCorrectionLayer_depth_le {L : Nat} (hL : 2 ≤ L) :
    (equalCorrectionLayer hL).depth ≤ 1 := by
  exact (depth_scatterEmbed_le _ _ _).trans (unequalCorrectionLayer_depth_le hL)

theorem equalParityMergeNet_depth_le {L : Nat} (hL : 2 ≤ L)
    (netE netO : ComparatorNetwork L) :
    (equalParityMergeNet hL netE netO).depth ≤ max netE.depth netO.depth + 1 := by
  have happend := ComparatorNetwork.depth_append_le (equalParityFront netE netO)
    (equalCorrectionLayer hL)
  simpa [equalParityMergeNet] using happend.trans
    (add_le_add (equalParityFront_depth_le netE netO) (equalCorrectionLayer_depth_le hL))

private theorem equalInterleave_prefix {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E O : Fin L → α) :
    (fun j : Fin (2 * L - 1) =>
      equalInterleave E O (equalCorrectionPrefixEmbed hL j)) =
      unequalInterleave E (equalOddPrefix hL O) := by
  funext i
  by_cases heven : i.val % 2 = 0
  · simp [equalInterleave, unequalInterleave, equalCorrectionPrefixEmbed, heven]
  · simp [equalInterleave, unequalInterleave, equalCorrectionPrefixEmbed, equalOddPrefix, heven]

private theorem equalCorrectedInterleave_prefix {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E O : Fin L → α) (i : Fin (2 * L - 1)) :
    equalCorrectedInterleave hL E O (equalCorrectionPrefixEmbed hL i) =
      unequalCorrectedInterleave hL E (equalOddPrefix hL O) i := by
  by_cases hz : i.val = 0
  · simp [equalCorrectedInterleave, unequalCorrectedInterleave,
      equalCorrectionPrefixEmbed, hz]
  · by_cases heven : i.val % 2 = 0
    · have hnotlast : i.val ≠ 2 * L - 1 := by have hi := i.isLt; omega
      simp [equalCorrectedInterleave, unequalCorrectedInterleave,
        equalCorrectionPrefixEmbed, equalOddPrefix, hz, hnotlast, heven]
    · have hnotlast : i.val ≠ 2 * L - 1 := by have hi := i.isLt; omega
      simp [equalCorrectedInterleave, unequalCorrectedInterleave,
        equalCorrectionPrefixEmbed, equalOddPrefix, hz, hnotlast, heven]

/-- The concrete extended layer executes as the equal-lane min/max interleave. -/
theorem equalCorrectionLayer_exec_eq {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E O : Fin L → α) :
    (equalCorrectionLayer hL).exec (equalInterleave E O) =
      equalCorrectedInterleave hL E O := by
  funext j
  by_cases hlast : j.val = 2 * L - 1
  · have houtside : j ∉ Set.range (equalCorrectionPrefixEmbed hL) := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp [equalCorrectionPrefixEmbed] at hv
      omega
    dsimp [equalCorrectionLayer]
    rw [ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ houtside]
    have hmod : (2 * L - 1) % 2 ≠ 0 := by omega
    have hq : (2 * L - 1) / 2 = L - 1 := by omega
    have hzero : ¬ 2 * L - 1 = 0 := by omega
    simp [equalInterleave, equalCorrectedInterleave, hlast, hmod, hq, hzero]
  · let i : Fin (2 * L - 1) := ⟨j.val, by omega⟩
    have hi : equalCorrectionPrefixEmbed hL i = j := by
      apply Fin.ext
      rfl
    rw [← hi]
    dsimp [equalCorrectionLayer]
    rw [ComparatorNetwork.scatterEmbed_exec_inside]
    change (unequalCorrectionLayer hL).exec
      (fun k => equalInterleave E O (equalCorrectionPrefixEmbed hL k)) i = _
    rw [equalInterleave_prefix hL E O, unequalCorrectionLayer_exec_eq,
      equalCorrectedInterleave_prefix]

/-- The actual equal-length correction network sorts whenever its lane
profiles satisfy the asymmetric threshold-count gap `0/2`. -/
theorem equalCorrectionLayer_sorts_of_threshold_gap {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (E O : Fin L → α)
    (hE : Monotone E) (hO : Monotone O)
    (hEcount : ∀ t, unequalThresholdCount E t ≤ unequalThresholdCount O t)
    (hOcount : ∀ t, unequalThresholdCount O t ≤ unequalThresholdCount E t + 2) :
    Monotone ((equalCorrectionLayer hL).exec (equalInterleave E O)) := by
  rw [equalCorrectionLayer_exec_eq]
  exact equalCorrectedInterleave_sorted_of_threshold_gap hL E O hE hO hEcount hOcount

/-- The even/even analogue of the odd-size induction step. If independent
networks sort the even and odd projections of two even sorted source runs,
the equal-length correction layer sorts their parent. -/
theorem evenParityMerge_step_sorts {m n : Nat} {α : Type} [LinearOrder α]
    (hL : 2 ≤ m + n) (A : Fin (2 * m) → α) (B : Fin (2 * n) → α)
    (hA : Monotone A) (hB : Monotone B)
    (netE netO : ComparatorNetwork (m + n))
    (hE : Monotone (netE.exec (evenEvenParityLane A B)))
    (hO : Monotone (netO.exec (oddEvenParityLane A B))) :
    Monotone ((equalCorrectionLayer hL).exec
      (equalInterleave (netE.exec (evenEvenParityLane A B))
        (netO.exec (oddEvenParityLane A B)))) := by
  have hgap := evenSourceParityThresholdGap_exec A B hA hB netE netO
  exact equalCorrectionLayer_sorts_of_threshold_gap hL _ _ hE hO
    (fun t => (hgap t).1) (fun t => (hgap t).2)

/-- One full induction step for the odd-sized unequal merge: if networks
correctly sort the two parity-lane subproblems, then the transported source
profile gap makes the concrete final correction layer sort their parent. -/
theorem unequalParityMerge_step_sorts {m : Nat} {α : Type} [LinearOrder α]
    (hm : 1 ≤ m)
    (A : Fin (2 * m) → α) (B : Fin (2 * m - 1) → α)
    (hA : Monotone A) (hB : Monotone B)
    (netE : ComparatorNetwork (m + m))
    (netO : ComparatorNetwork (m + (m - 1)))
    (hE : Monotone (netE.exec (Fin.append
      (fun j : Fin m => A (unequalEvenIndex j))
      (fun j : Fin m => B (unequalEvenIndexOddLength j)))))
    (hO : Monotone (netO.exec (Fin.append
      (fun j : Fin m => A (unequalOddIndex j))
      (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j))))) :
    Monotone ((unequalCorrectionLayer (by omega : 2 ≤ 2 * m)).exec
      (unequalInterleave
        (fun i : Fin (2 * m) =>
          netE.exec (Fin.append (fun j : Fin m => A (unequalEvenIndex j))
            (fun j : Fin m => B (unequalEvenIndexOddLength j)))
            (Fin.cast (by omega : 2 * m = m + m) i))
        (fun i : Fin (2 * m - 1) =>
          netO.exec (Fin.append (fun j : Fin m => A (unequalOddIndex j))
            (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j)))
            (Fin.cast (by omega : 2 * m - 1 = m + (m - 1)) i)))) := by
  let E : Fin (2 * m) → α := fun i =>
    netE.exec (Fin.append (fun j : Fin m => A (unequalEvenIndex j))
      (fun j : Fin m => B (unequalEvenIndexOddLength j)))
      (Fin.cast (by omega : 2 * m = m + m) i)
  let O : Fin (2 * m - 1) → α := fun i =>
    netO.exec (Fin.append (fun j : Fin m => A (unequalOddIndex j))
      (fun j : Fin (m - 1) => B (unequalOddIndexOddLength j)))
      (Fin.cast (by omega : 2 * m - 1 = m + (m - 1)) i)
  have hEmono : Monotone E := unequalMonotone_cast (by omega) _ hE
  have hOmono : Monotone O := unequalMonotone_cast (by omega) _ hO
  have hgap := unequalSourceParityThresholdGap_exec_cast A B hA hB netE netO
  have hsorted := unequalCorrectionLayer_sorts_of_threshold_gap
    (by omega : 2 ≤ 2 * m) E O hEmono hOmono
    (fun t => (hgap t).1) (fun t => (hgap t).2)
  simpa [E, O] using hsorted

/-- The executable equal-size merge step sorts when the two lane outputs are
sorted and their threshold profiles satisfy the `0/2` gap. -/
theorem equalParityMergeNet_sorts {L : Nat} (hL : 2 ≤ L)
    {α : Type} [LinearOrder α] (netE netO : ComparatorNetwork L)
    (v : Fin (2 * L) → α)
    (hE : Monotone (netE.exec (fun i => v (equalEvenEmbed i))))
    (hO : Monotone (netO.exec (fun i => v (equalOddEmbed i))))
    (hEcount : ∀ t, unequalThresholdCount
      (netE.exec (fun i => v (equalEvenEmbed i))) t ≤
      unequalThresholdCount (netO.exec (fun i => v (equalOddEmbed i))) t)
    (hOcount : ∀ t, unequalThresholdCount
      (netO.exec (fun i => v (equalOddEmbed i))) t ≤
      unequalThresholdCount (netE.exec (fun i => v (equalEvenEmbed i))) t + 2) :
    Monotone ((equalParityMergeNet hL netE netO).exec v) := by
  rw [equalParityMergeNet_exec_eq]
  rw [equalCorrectionLayer_exec_eq]
  exact equalCorrectedInterleave_sorted_of_threshold_gap hL _ _ hE hO hEcount hOcount

private theorem evenLane32_eq {α : Type} [LinearOrder α]
    (A B : Fin 32 → α) :
    (fun i : Fin 32 => Fin.append (m := 32) (n := 32) A B (equalEvenEmbed i)) =
      evenEvenParityLane (m := 16) (n := 16) A B := by
  funext i
  by_cases hi : i.val < 16
  · let j : Fin 16 := ⟨i.val, hi⟩
    have hidx : i = Fin.castAdd 16 j := by apply Fin.ext; rfl
    rw [hidx]
    have hw : equalEvenEmbed (Fin.castAdd 16 j) = Fin.castAdd 32 (unequalEvenIndex j) := by
      apply Fin.ext
      simp [equalEvenEmbed, unequalEvenIndex]
    rw [hw, Fin.append_left]
    simp [evenEvenParityLane]
  · let j : Fin 16 := ⟨i.val - 16, by have := i.isLt; omega⟩
    have hidx : i = Fin.natAdd 16 j := by apply Fin.ext; simp [j]; omega
    rw [hidx]
    have hw : equalEvenEmbed (Fin.natAdd 16 j) = Fin.natAdd 32 (unequalEvenIndex j) := by
      apply Fin.ext
      simp [equalEvenEmbed, unequalEvenIndex, j]
      omega
    rw [hw, Fin.append_right]
    simp only [evenEvenParityLane]
    rw [Fin.append_right]

private theorem oddLane32_eq {α : Type} [LinearOrder α]
    (A B : Fin 32 → α) :
    (fun i : Fin 32 => Fin.append (m := 32) (n := 32) A B (equalOddEmbed i)) =
      oddEvenParityLane (m := 16) (n := 16) A B := by
  funext i
  by_cases hi : i.val < 16
  · let j : Fin 16 := ⟨i.val, hi⟩
    have hidx : i = Fin.castAdd 16 j := by apply Fin.ext; rfl
    rw [hidx]
    have hw : equalOddEmbed (Fin.castAdd 16 j) = Fin.castAdd 32 (unequalOddIndex j) := by
      apply Fin.ext
      simp [equalOddEmbed, unequalOddIndex]
    rw [hw, Fin.append_left]
    simp [oddEvenParityLane]
  · let j : Fin 16 := ⟨i.val - 16, by have := i.isLt; omega⟩
    have hidx : i = Fin.natAdd 16 j := by apply Fin.ext; simp [j]; omega
    rw [hidx]
    have hw : equalOddEmbed (Fin.natAdd 16 j) = Fin.natAdd 32 (unequalOddIndex j) := by
      apply Fin.ext
      simp [equalOddEmbed, unequalOddIndex, j]
      omega
    rw [hw, Fin.append_right]
    simp only [oddEvenParityLane]
    rw [Fin.append_right]

/-- A concrete 64-wire recursive merge step: once its two 32-wire parity
submerges sort the parity projections of two sorted 32-wire runs, the
composed network sorts all 64 wires. -/
theorem equalParityMerge64_sorts_two_runs {α : Type} [LinearOrder α]
    (netE netO : ComparatorNetwork 32) (A B : Fin 32 → α)
    (hA : Monotone A) (hB : Monotone B)
    (hE : Monotone (netE.exec (evenEvenParityLane (m := 16) (n := 16) A B)))
    (hO : Monotone (netO.exec (oddEvenParityLane (m := 16) (n := 16) A B))) :
    Monotone ((equalParityMergeNet (by omega : 2 ≤ 32) netE netO).exec
      (Fin.append (m := 32) (n := 32) A B)) := by
  have hgap := evenSourceParityThresholdGap_exec (m := 16) (n := 16) A B hA hB netE netO
  apply equalParityMergeNet_sorts (by omega) netE netO (Fin.append (m := 32) (n := 32) A B)
  · simpa [evenLane32_eq] using hE
  · simpa [oddLane32_eq] using hO
  · intro t
    simpa [evenLane32_eq, oddLane32_eq] using (hgap t).1
  · intro t
    simpa [evenLane32_eq, oddLane32_eq] using (hgap t).2

theorem equalParityMerge64_depth_le (netE netO : ComparatorNetwork 32)
    (hE : netE.depth ≤ 5) (hO : netO.depth ≤ 5) :
    (equalParityMergeNet (by omega : 2 ≤ 32) netE netO).depth ≤ 6 := by
  exact (equalParityMergeNet_depth_le (by omega) netE netO).trans (by omega)

private theorem evenIndex32_monotone : Monotone (unequalEvenIndex : Fin 16 → Fin 32) := by
  intro i j hij
  apply Fin.mk_le_mk.mpr
  have h : i.val ≤ j.val := Fin.mk_le_mk.mp hij
  change 2 * i.val ≤ 2 * j.val
  omega

private theorem oddIndex32_monotone : Monotone (unequalOddIndex : Fin 16 → Fin 32) := by
  intro i j hij
  apply Fin.mk_le_mk.mpr
  have h : i.val ≤ j.val := Fin.mk_le_mk.mp hij
  change 2 * i.val + 1 ≤ 2 * j.val + 1
  omega

/-- The usual 32-wire odd-even submerges instantiate the abstract hypotheses,
so this gives the standard, fully closed 64-wire merge proof at depth six. -/
theorem standard64Merge_sorts_two_runs {α : Type} [LinearOrder α]
    (A B : Fin 32 → α) (hA : Monotone A) (hB : Monotone B) :
    Monotone ((equalParityMergeNet (by omega : 2 ≤ 32)
      (oddEvenMergeNet 5) (oddEvenMergeNet 5)).exec (Fin.append (m := 32) (n := 32) A B)) := by
  have hEven : Monotone (unequalEvenIndex : Fin 16 → Fin 32) := evenIndex32_monotone
  have hOdd : Monotone (unequalOddIndex : Fin 16 → Fin 32) := oddIndex32_monotone
  have hLaneE : Monotone ((oddEvenMergeNet 5).exec
      (evenEvenParityLane (m := 16) (n := 16) A B)) := by
    apply oddEvenMergeNet_sorts_two_runs 4
    constructor
    · simpa [evenEvenParityLane, Fin.append_left] using hA.comp hEven
    · change Monotone (fun i : Fin 16 =>
        Fin.append (fun j : Fin 16 => A (unequalEvenIndex j))
          (fun j : Fin 16 => B (unequalEvenIndex j)) (Fin.natAdd 16 i))
      have heq : (fun i : Fin 16 =>
          Fin.append (fun j : Fin 16 => A (unequalEvenIndex j))
            (fun j : Fin 16 => B (unequalEvenIndex j)) (Fin.natAdd 16 i)) =
          fun i : Fin 16 => B (unequalEvenIndex i) := by
        funext i
        exact Fin.append_right _ _ i
      rw [heq]
      exact hB.comp hEven
  have hLaneO : Monotone ((oddEvenMergeNet 5).exec
      (oddEvenParityLane (m := 16) (n := 16) A B)) := by
    apply oddEvenMergeNet_sorts_two_runs 4
    constructor
    · simpa [oddEvenParityLane, Fin.append_left] using hA.comp hOdd
    · change Monotone (fun i : Fin 16 =>
        Fin.append (fun j : Fin 16 => A (unequalOddIndex j))
          (fun j : Fin 16 => B (unequalOddIndex j)) (Fin.natAdd 16 i))
      have heq : (fun i : Fin 16 =>
          Fin.append (fun j : Fin 16 => A (unequalOddIndex j))
            (fun j : Fin 16 => B (unequalOddIndex j)) (Fin.natAdd 16 i)) =
          fun i : Fin 16 => B (unequalOddIndex i) := by
        funext i
        exact Fin.append_right _ _ i
      rw [heq]
      exact hB.comp hOdd
  exact equalParityMerge64_sorts_two_runs (oddEvenMergeNet 5) (oddEvenMergeNet 5)
    A B hA hB hLaneE hLaneO

theorem standard64Merge_depth_le :
    (equalParityMergeNet (by omega : 2 ≤ 32)
      (oddEvenMergeNet 5) (oddEvenMergeNet 5)).depth ≤ 6 := by
  apply equalParityMerge64_depth_le
  · exact oddEvenMergeNet_depth_le 5
  · exact oddEvenMergeNet_depth_le 5

end Chvatal.PacketAlignment
