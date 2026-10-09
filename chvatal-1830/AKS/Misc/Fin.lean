module
/- `Fin` counting, order and rank helpers. -/

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-- Count of `Fin n` elements with value ≥ thresh equals n - thresh. -/
lemma card_filter_val_ge (n thresh : ℕ) (h : thresh ≤ n) :
    (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)).card = n - thresh := by
  by_cases ht : thresh < n
  · have : (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)) = Finset.Ici ⟨thresh, ht⟩ := by
      ext i; simp [Fin.le_def]
    rw [this, Fin.card_Ici]
  · obtain rfl := le_antisymm h (not_lt.1 ht)
    simp

/-- Strict inequality from `≤` and `≠` for `Fin`. -/
lemma Fin.lt_of_le_of_ne {n : ℕ} {a b : Fin n} (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  _root_.lt_of_le_of_ne h1 h2

/-- The rank of an element: the number of strictly smaller elements. -/
def rank {α : Type*} [Fintype α] [LinearOrder α] (a : α) : ℕ :=
  (Finset.univ.filter (· < a)).card

end
