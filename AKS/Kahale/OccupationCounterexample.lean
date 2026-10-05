module

public import AKS.Kahale.OccupationLayer
public import AKS.Sort.ZeroOne

/-! # Equal-height comparisons can finish sorting

A four-wire sorting network has equal scalar heights at every comparator.
This refutes a universally positive local height-loss charge, not an
asymptotic lower bound with scale-dependent or endpoint terms.
-/

@[expose] public section

namespace Kahale

def occupationFourSorter : ComparatorNetwork 4 :=
  ⟨[⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩,
    ⟨0, 2, by decide⟩, ⟨1, 3, by decide⟩, ⟨1, 2, by decide⟩]⟩

def scalarHeightStep {n : ℕ} (c : Comparator n) (h : Fin n → ℕ) : Fin n → ℕ :=
  fun k => if k = c.i then min (h c.i) (h c.j)
    else if k = c.j then max (h c.i) (h c.j) + 1 else h k

def scalarHeightEfficient {n : ℕ} (net : ComparatorNetwork n) : Bool :=
  (net.comparators.foldl (fun (state : (Fin n → ℕ) × Bool) c =>
    (scalarHeightStep c state.1, state.2 && decide (state.1 c.i = state.1 c.j)))
    ((fun _ => 0), true)).2

theorem occupationFourSorter_equal_heights :
    scalarHeightEfficient occupationFourSorter = true := by decide

theorem occupationFourSorter_bool :
    ∀ v : Fin 4 → Bool, Monotone (occupationFourSorter.exec v) := by decide

theorem occupationFourSorter_sorts : occupationFourSorter.Sorts :=
  zero_one_principle occupationFourSorter occupationFourSorter_bool

end Kahale
