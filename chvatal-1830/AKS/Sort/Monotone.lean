module
/- Comparators and networks commute with monotone maps; the `Sorts` predicate. -/

public import AKS.Sort.Defs
public import AKS.Sort.Depth

@[expose] public section

open Finset BigOperators

/-- Monotone functions commute with network execution (min/max commute with monotone maps). -/
theorem ComparatorNetwork.exec_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (net : ComparatorNetwork n) {f : α → β} (hf : Monotone f)
    (v : Fin n → α) :
    f ∘ net.exec v = net.exec (f ∘ v) := by
  unfold exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    ext k
    simp only [Function.comp, Comparator.apply]
    split_ifs
    · exact hf.map_min
    · exact hf.map_max
    · rfl

/-- Network execution on a monotone input is the identity. -/
theorem ComparatorNetwork.exec_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Monotone v) :
    net.exec v = v := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [c.apply_eq_of_le v (hv c.h.le)]
    exact ih hv

/-- A network is a *sorting network* if it sorts every input. -/
def ComparatorNetwork.Sorts {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (α : Type*) [LinearOrder α] (v : Fin n → α),
    Monotone (net.exec v)

end
