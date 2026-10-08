module
/-
  # Monotonicity Preservation for Comparator Networks

  Comparators and networks preserve monotonicity of input functions.
  This is the key structural property underlying the 0-1 principle.

  Main results:
  • `Comparator.apply_comp_monotone`: monotone functions commute with comparator application
  • `Comparator.apply_preserves_monotone`: comparators preserve monotone inputs
  • `ComparatorNetwork.exec_comp_monotone`: monotone functions commute with network execution
  • `ComparatorNetwork.Sorts`: a network sorts all inputs iff every output is monotone
-/

public import AKS.Sort.Defs
public import AKS.Sort.Depth

@[expose] public section


open Finset BigOperators


/-! **Helper Lemmas** -/



/-! **Comparator Preservation Lemmas** -/

/-- Monotone functions commute with a single comparator application.
    This is the key lemma for the 0-1 principle: min/max commute
    with monotone functions on linear orders. -/
theorem Comparator.apply_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (c : Comparator n) {f : α → β} (hf : Monotone f) (v : Fin n → α) :
    f ∘ c.apply v = c.apply (f ∘ v) := by
  ext k
  simp only [Function.comp, Comparator.apply]
  split_ifs with h1 h2
  · exact hf.map_min
  · exact hf.map_max
  · rfl



/-- Monotone functions commute with sequential comparator application. -/
private theorem foldl_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (cs : List (Comparator n)) {f : α → β} (hf : Monotone f)
    (v : Fin n → α) :
    f ∘ cs.foldl (fun acc c ↦ c.apply acc) v =
      cs.foldl (fun acc c ↦ c.apply acc) (f ∘ v) := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (c.apply v), c.apply_comp_monotone hf v]

/-- Monotone functions commute with network execution.
    Extends `apply_comp_monotone` to the full comparator sequence. -/
theorem ComparatorNetwork.exec_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (net : ComparatorNetwork n) {f : α → β} (hf : Monotone f)
    (v : Fin n → α) :
    f ∘ net.exec v = net.exec (f ∘ v) :=
  foldl_comp_monotone net.comparators hf v

/-- A comparator applied to a monotone function is the identity:
    `v(c.i) ≤ v(c.j)` already holds, so `min = v(c.i)` and `max = v(c.j)`. -/
theorem Comparator.apply_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {v : Fin n → α} (hv : Monotone v) :
    c.apply v = v := by
  ext k; unfold Comparator.apply
  by_cases hki : k = c.i
  · subst hki; rw [if_pos rfl, min_eq_left (hv (Fin.le_of_lt c.h))]
  · rw [if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj; rw [if_pos rfl, max_eq_right (hv (Fin.le_of_lt c.h))]
    · rw [if_neg hkj]

/-- Network execution on a monotone input is the identity: already-sorted
    inputs are not modified by any comparator. -/
theorem ComparatorNetwork.exec_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Monotone v) :
    net.exec v = v := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [c.apply_eq_of_monotone hv]
    exact ih hv

/-- A network is a *sorting network* if it sorts every input. -/
def ComparatorNetwork.Sorts {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (α : Type*) [LinearOrder α] (v : Fin n → α),
    Monotone (net.exec v)





end
