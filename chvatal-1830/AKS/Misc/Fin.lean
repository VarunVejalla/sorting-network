module
/-
  # Fin Arithmetic Helpers

  Reusable `Fin` encode/decode lemmas for product-type indexing.
  Used by graph constructions in `Graph/Regular.lean` and `ZigZag.lean` that represent
  `Fin n × Fin d` as `Fin (n * d)` via `j * d + i` encoding.
-/

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring

@[expose] public section







/-! **Counting** -/

/-- Count of `Fin n` elements with value < t equals t (when t ≤ n). -/
lemma card_filter_val_lt (n t : ℕ) (h : t ≤ n) :
    (Finset.univ.filter (fun i : Fin n ↦ i.val < t)).card = t := by
  by_cases ht : t < n
  · have : (Finset.univ.filter (fun i : Fin n ↦ i.val < t)) = Finset.Iio ⟨t, ht⟩ := by
      ext i; simp [Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · push_neg at ht; obtain rfl := le_antisymm h ht
    have : (Finset.univ.filter (fun i : Fin t ↦ i.val < t)) = Finset.univ := by ext i; simp
    rw [this, Finset.card_fin]

/-- Count of `Fin n` elements with value ≥ thresh equals n - thresh. -/
lemma card_filter_val_ge (n thresh : ℕ) (h : thresh ≤ n) :
    (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)).card = n - thresh := by
  have htotal : (Finset.univ.filter (fun i : Fin n ↦ i.val < thresh)).card +
      (Finset.univ.filter (fun i : Fin n ↦ ¬ i.val < thresh)).card = n := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _)]
    rw [Finset.filter_union_filter_not_eq]; exact Finset.card_fin n
  have hconv : (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)) =
      (Finset.univ.filter (fun i : Fin n ↦ ¬ i.val < thresh)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [← hconv, card_filter_val_lt n thresh h] at htotal; omega


/-! **Order** -/

/-- Strict inequality from `≤` and `≠` for `Fin`. -/
lemma Fin.lt_of_le_of_ne {n : ℕ} {a b : Fin n} (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  by_contra h
  push_neg at h
  exact h2 (Fin.le_antisymm h1 h)


/-! **Rank** -/

/-- The rank of an element: the number of strictly smaller elements.
    For `Fin n`, this equals the element's value. -/
def rank {α : Type*} [Fintype α] [LinearOrder α] (a : α) : ℕ :=
  (Finset.univ.filter (· < a)).card





/-! **Fin (2 * m) Partition Helpers** -/



end
