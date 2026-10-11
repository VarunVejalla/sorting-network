module
/-
  # Correctness of the bitonic sorter

  By the 0-1 principle it suffices to sort Boolean vectors. The half-cleaner (`layer 1`) splits a
  `Window` vector (true entries, or false entries, form an interval) into two `Window` halves
  with the lower half entirely below the upper one; the flip layer does the same to a vector whose
  two halves are sorted.
-/

public import AKS.Bitonic.Net
public import AKS.Sort.ZeroOne

@[expose] public section

open ComparatorNetwork

namespace Bitonic
variable {N n : ℕ}

/-- A Boolean vector whose true entries form a window, or whose false entries do. -/
def Window {m : ℕ} (f : Fin m → Bool) : Prop :=
  ∃ l h : ℕ, (∀ i : Fin m, f i = true ↔ (l ≤ i.val ∧ i.val < h)) ∨
    (∀ i : Fin m, f i = true ↔ ¬(l ≤ i.val ∧ i.val < h))

theorem min_eq_true (a b : Bool) : min a b = true ↔ a = true ∧ b = true := by
  revert a b; decide

theorem max_eq_true (a b : Bool) : max a b = true ↔ a = true ∨ b = true := by
  revert a b; decide

/-- The half-cleaner splits a bitonic vector into two bitonic halves, one entirely below the
other. -/
theorem halfClean (hn : N + N = n) (w : Fin n → Bool) (hw : Window w) :
    Window (fun i => min (lowH hn w i) (upH hn w i)) ∧
    Window (fun i => max (lowH hn w i) (upH hn w i)) ∧
    ((fun i => min (lowH hn w i) (upH hn w i)) = (fun _ => false) ∨
     (fun i => max (lowH hn w i) (upH hn w i)) = (fun _ => true)) := by
  obtain ⟨l, h, H | H⟩ := hw
  · have H1 : ∀ i : Fin N, lowH hn w i = true ↔ (l ≤ i.val ∧ i.val < h) :=
      fun i => H ⟨i, by have := i.2; omega⟩
    have H2 : ∀ i : Fin N, upH hn w i = true ↔ (l ≤ N + i.val ∧ N + i.val < h) :=
      fun i => H ⟨N + i, by have := i.2; omega⟩
    refine ⟨⟨l, h - N, Or.inl fun i => ?_⟩, ?_, ?_⟩
    · simp only [min_eq_true, H1 i, H2 i]; have := i.2; omega
    · by_cases c1 : h ≤ N
      · exact ⟨l, h, Or.inl fun i => by simp only [max_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      by_cases c2 : N ≤ l
      · exact ⟨l - N, h - N, Or.inl fun i => by
          simp only [max_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      by_cases c3 : l ≤ h - N
      · exact ⟨0, N, Or.inl fun i => by simp only [max_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      · exact ⟨h - N, l, Or.inr fun i => by
          simp only [max_eq_true, H1 i, H2 i]; have := i.2; omega⟩
    · by_contra hc
      push_neg at hc
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hc.1
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hc.2
      have hi' : min (lowH hn w i) (upH hn w i) = true := by simpa using hi
      have hj' : ¬ max (lowH hn w j) (upH hn w j) = true := by simpa using hj
      rw [min_eq_true, H1 i, H2 i] at hi'
      rw [max_eq_true, H1 j, H2 j] at hj'
      have := i.2; have := j.2
      omega
  · have H1 : ∀ i : Fin N, lowH hn w i = true ↔ ¬(l ≤ i.val ∧ i.val < h) :=
      fun i => H ⟨i, by have := i.2; omega⟩
    have H2 : ∀ i : Fin N, upH hn w i = true ↔ ¬(l ≤ N + i.val ∧ N + i.val < h) :=
      fun i => H ⟨N + i, by have := i.2; omega⟩
    refine ⟨?_, ⟨l, h - N, Or.inr fun i => ?_⟩, ?_⟩
    · by_cases c1 : h ≤ N
      · exact ⟨l, h, Or.inr fun i => by simp only [min_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      by_cases c2 : N ≤ l
      · exact ⟨l - N, h - N, Or.inr fun i => by
          simp only [min_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      by_cases c3 : l ≤ h - N
      · exact ⟨0, N, Or.inr fun i => by simp only [min_eq_true, H1 i, H2 i]; have := i.2; omega⟩
      · exact ⟨h - N, l, Or.inl fun i => by
          simp only [min_eq_true, H1 i, H2 i]; have := i.2; omega⟩
    · simp only [max_eq_true, H1 i, H2 i]; have := i.2; omega
    · by_contra hc
      push_neg at hc
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hc.1
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hc.2
      have hi' : min (lowH hn w i) (upH hn w i) = true := by simpa using hi
      have hj' : ¬ max (lowH hn w j) (upH hn w j) = true := by simpa using hj
      rw [min_eq_true, H1 i, H2 i] at hi'
      rw [max_eq_true, H1 j, H2 j] at hj'
      have := i.2; have := j.2
      omega

/-- A monotone Boolean vector is a threshold. -/
theorem mono_thr {m : ℕ} (f : Fin m → Bool) (hf : Monotone f) :
    ∃ a : ℕ, ∀ i : Fin m, f i = true ↔ a ≤ i.val := by
  classical
  by_cases h : ∃ a, ∃ ha : a < m, f ⟨a, ha⟩ = true
  · refine ⟨Nat.find h, fun i => ⟨fun hi => Nat.find_min' h ⟨i.2, hi⟩, fun hle => ?_⟩⟩
    obtain ⟨ha, hfa⟩ := Nat.find_spec h
    have := hf (show (⟨Nat.find h, ha⟩ : Fin m) ≤ i from hle)
    cases hfi : f i
    · rw [hfa, hfi] at this; exact absurd this (by decide)
    · rfl
  · exact ⟨m, fun i => ⟨fun hi => absurd ⟨i, i.2, hi⟩ h, fun hle => absurd i.2 (by omega)⟩⟩

/-- The flip layer turns two sorted halves into two bitonic halves, one below the other. -/
theorem cross_props (hn : N + N = n) (u : Fin n → Bool)
    (h0 : Monotone (lowH hn u)) (h1 : Monotone (upH hn u)) :
    Window (lowH hn ((layer hn Fin.revPerm).exec u)) ∧
    Window (upH hn ((layer hn Fin.revPerm).exec u)) ∧
    (lowH hn ((layer hn Fin.revPerm).exec u) = (fun _ => false) ∨
     upH hn ((layer hn Fin.revPerm).exec u) = (fun _ => true)) := by
  obtain ⟨a, ha⟩ := mono_thr _ h0
  obtain ⟨b, hb⟩ := mono_thr _ h1
  obtain ⟨e1, e2⟩ := layer_exec hn Fin.revPerm u
  have L : ∀ i : Fin N, lowH hn ((layer hn Fin.revPerm).exec u) i = true ↔
      (a ≤ i.val ∧ b ≤ N - (i.val + 1)) := fun i => by
    rw [e1, min_eq_true, ha i, hb (Fin.revPerm i)]; simp
  have R : ∀ j : Fin N, upH hn ((layer hn Fin.revPerm).exec u) j = true ↔
      (a ≤ N - (j.val + 1) ∨ b ≤ j.val) := fun j => by
    rw [e2, max_eq_true, ha _, hb j]; simp [Fin.revPerm]
  refine ⟨⟨a, N - b, Or.inl fun i => ?_⟩, ⟨N - a, b, Or.inr fun j => ?_⟩, ?_⟩
  · rw [L i]; have := i.2; omega
  · rw [R j]; have := j.2; omega
  · by_contra hc
    push_neg at hc
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc.1
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc.2
    have hi' : lowH hn ((layer hn Fin.revPerm).exec u) i = true := by simpa using hi
    have hj' : ¬ upH hn ((layer hn Fin.revPerm).exec u) j = true := by simpa using hj
    rw [L i] at hi'
    rw [R j] at hj'
    have := i.2; have := j.2
    omega

/-- Glue two sorted halves, the lower all `false` or the upper all `true`. -/
theorem glue (hn : N + N = n) (o : Fin n → Bool) (h0 : Monotone (lowH hn o))
    (h1 : Monotone (upH hn o))
    (h : lowH hn o = (fun _ => false) ∨ upH hn o = (fun _ => true)) : Monotone o := by
  have hub : ∀ x : Fin n, N ≤ x.val → o x = upH hn o ⟨x - N, by have := x.2; omega⟩ :=
    fun x hx => by unfold upH; congr 1; ext; simp; omega
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  by_cases ha : a.val < N
  · by_cases hb : b.val < N
    · exact h0 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab
    · rcases h with h | h
      · rw [show o a = false from congrFun h ⟨a, ha⟩]; exact Bool.false_le _
      · rw [hub b (by omega), congrFun h]; exact Bool.le_true _
  · rw [hub a (by omega), hub b (by omega)]
    exact h1 (show (⟨a - N, _⟩ : Fin N) ≤ ⟨b - N, _⟩ from Fin.mk_le_mk.2 (by omega))

theorem bitonicMerge_sorts : ∀ (k : ℕ) (v : Fin (2 ^ k) → Bool),
    Window v → Monotone ((bitonicMerge k).exec v)
  | 0, v, _ => fun a b _ => by
    have := a.2; have := b.2
    rw [show a = b from Fin.ext (by rw [Nat.pow_zero] at *; omega)]
  | k + 1, v, hv => by
    have hn := two_pow_succ' k
    obtain ⟨hl, hu, hord⟩ := halfClean hn v hv
    obtain ⟨e1, e2⟩ := layer_exec hn 1 v
    obtain ⟨p1, p2⟩ := par_exec hn (bitonicMerge k) (bitonicMerge k) ((layer hn 1).exec v)
    simp only [← Equiv.Perm.inv_def, inv_one, Equiv.Perm.coe_one, id_eq] at e1 e2
    rw [show (bitonicMerge (k + 1)).exec v = (par hn (bitonicMerge k) (bitonicMerge k)).exec ((layer hn 1).exec v) from exec_append _ _ v]
    refine glue hn _ (by rw [p1, e1]; exact bitonicMerge_sorts k _ hl)
      (by rw [p2, e2]; exact bitonicMerge_sorts k _ hu) ?_
    rcases hord with h | h
    · left; rw [p1, e1, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)
    · right; rw [p2, e2, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)

theorem bitonicSort_sorts_bool : ∀ (k : ℕ) (v : Fin (2 ^ k) → Bool),
    Monotone ((bitonicSort k).exec v)
  | 0, v => fun a b _ => by
    have := a.2; have := b.2
    rw [show a = b from Fin.ext (by rw [Nat.pow_zero] at *; omega)]
  | k + 1, v => by
    have hn := two_pow_succ' k
    obtain ⟨q1, q2⟩ := par_exec hn (bitonicSort k) (bitonicSort k) v
    obtain ⟨hl, hu, hord⟩ := cross_props hn _ (by rw [q1]; exact bitonicSort_sorts_bool k _)
      (by rw [q2]; exact bitonicSort_sorts_bool k _)
    obtain ⟨r1, r2⟩ := par_exec hn (bitonicMerge k) (bitonicMerge k)
      ((layer hn Fin.revPerm).exec ((par hn (bitonicSort k) (bitonicSort k)).exec v))
    rw [show (bitonicSort (k + 1)).exec v = (par hn (bitonicMerge k) (bitonicMerge k)).exec
      ((layer hn Fin.revPerm).exec ((par hn (bitonicSort k) (bitonicSort k)).exec v)) from
      (exec_append _ _ v).trans (exec_append _ _ _)]
    refine glue hn _ (by rw [r1]; exact bitonicMerge_sorts k _ hl)
      (by rw [r2]; exact bitonicMerge_sorts k _ hu) ?_
    rcases hord with h | h
    · left; rw [r1, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)
    · right; rw [r2, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)

theorem bitonicSort_sorts (k : ℕ) : (bitonicSort k).Sorts :=
  zero_one_principle _ (bitonicSort_sorts_bool k)

end Bitonic

end
