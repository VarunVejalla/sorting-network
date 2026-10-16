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

end Chvatal.PacketAlignment
