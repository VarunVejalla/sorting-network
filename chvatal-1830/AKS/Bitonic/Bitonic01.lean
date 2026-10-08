module
/-
  # Bitonic 0-1 Sequences

  `IsBitonic01` definition, basic facts, interval helpers for and/or of bitonic inputs.
-/

public import AKS.Bitonic.Defs

@[expose] public section

open Finset

/-! **Bitonic 0-1 Sequences** -/

/-- A 0-1 sequence is *bitonic* if some Bool value forms a contiguous interval `[lo, hi)`.
    Equivalently, the sequence has at most two "transitions" between false and true
    (a rotation of a monotone sequence). -/
def IsBitonic01 {n : Nat} (v : Fin n → Bool) : Prop :=
  ∃ (b : Bool) (lo hi : Nat), lo ≤ hi ∧ hi ≤ n ∧
    (∀ i : Fin n, v i = b ↔ lo ≤ i.val ∧ i.val < hi)




/-! **Interval Helpers for Compare Layer** -/

/-- Helper to get clean `Fin.val` characterization from the `IsBitonic01` hypothesis. -/
theorem isBitonic01_val_left {m : Nat} {v : Fin (2 * m) → Bool} {b : Bool} {lo hi : Nat}
    (hv : ∀ j : Fin (2 * m), v j = b ↔ lo ≤ j.val ∧ j.val < hi) (i : Fin m) :
    v ⟨i.val, by omega⟩ = b ↔ lo ≤ i.val ∧ i.val < hi := by
  have := hv ⟨i.val, by omega⟩; simpa using this

theorem isBitonic01_val_right {m : Nat} {v : Fin (2 * m) → Bool} {b : Bool} {lo hi : Nat}
    (hv : ∀ j : Fin (2 * m), v j = b ↔ lo ≤ j.val ∧ j.val < hi) (i : Fin m) :
    v ⟨i.val + m, by omega⟩ = b ↔ lo ≤ i.val + m ∧ i.val + m < hi := by
  have := hv ⟨i.val + m, by omega⟩; simpa using this

/-- AND of bitonic input (b=false case). -/
theorem and_bitonic_false {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = false ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨false, lo, hi, _hlo, h1, fun i ↦ ?_⟩
    rw [Bool.and_eq_false_iff]; constructor
    · intro h; rcases h with h | h
      · exact (hvi i).mp h
      · exact absurd ((hvim i).mp h) (by omega)
    · intro h; exact Or.inl ((hvi i).mpr h)
  · by_cases h2 : m ≤ lo
    · refine ⟨false, lo - m, hi - m, by omega, by omega, fun i ↦ ?_⟩
      rw [Bool.and_eq_false_iff]; constructor
      · intro h; rcases h with h | h
        · exact absurd ((hvi i).mp h) (by omega)
        · have := (hvim i).mp h; omega
      · intro h; exact Or.inr ((hvim i).mpr (by omega))
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨false, 0, m, Nat.zero_le _, Nat.le.refl, fun i ↦ ?_⟩
        rw [Bool.and_eq_false_iff]; constructor
        · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
        · intro _
          by_cases h : lo ≤ i.val
          · exact Or.inl ((hvi i).mpr ⟨h, by omega⟩)
          · exact Or.inr ((hvim i).mpr (by omega))
      · refine ⟨true, hi - m, lo, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩
          have hni : ¬(lo ≤ i.val ∧ i.val < hi) := fun hc ↦ by
            have := (hvi i).mpr hc; rw [h1] at this; exact Bool.noConfusion this
          have hnim : ¬(lo ≤ i.val + m ∧ i.val + m < hi) := fun hc ↦ by
            have := (hvim i).mpr hc; rw [h2] at this; exact Bool.noConfusion this
          omega
        · intro ⟨h1, h2⟩
          exact ⟨by cases hv' : v ⟨i.val, by omega⟩ with
                   | false => exact absurd ((hvi i).mp hv') (by omega)
                   | true => rfl,
                 by cases hv' : v ⟨i.val + m, by omega⟩ with
                   | false => exact absurd ((hvim i).mp hv') (by omega)
                   | true => rfl⟩

/-- AND of bitonic input (b=true case). -/
theorem and_bitonic_true {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = true ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
    rw [Bool.and_eq_true]; constructor
    · intro ⟨_, h2⟩; have := (hvim i).mp h2; omega
    · intro ⟨_, h⟩; omega
  · by_cases h2 : m ≤ lo
    · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
      rw [Bool.and_eq_true]; constructor
      · intro ⟨h1, _⟩; have := (hvi i).mp h1; omega
      · intro ⟨_, h⟩; omega
    · by_cases h3 : hi - m ≤ lo
      · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩; have := (hvi i).mp h1; have := (hvim i).mp h2; omega
        · intro ⟨_, h⟩; omega
      · refine ⟨true, lo, hi - m, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩; exact ⟨((hvi i).mp h1).1, by have := (hvim i).mp h2; omega⟩
        · intro ⟨h1, h2⟩; exact ⟨(hvi i).mpr ⟨h1, by omega⟩, (hvim i).mpr (by omega)⟩

/-- OR of bitonic input (b=false case). -/
theorem or_bitonic_false {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = false ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
    rw [Bool.or_eq_false_iff]; constructor
    · intro ⟨_, h2⟩; exact absurd ((hvim i).mp h2) (by omega)
    · intro ⟨_, h⟩; omega
  · by_cases h2 : m ≤ lo
    · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
      rw [Bool.or_eq_false_iff]; constructor
      · intro ⟨h1, _⟩; exact absurd ((hvi i).mp h1) (by omega)
      · intro ⟨_, h⟩; omega
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨false, lo, hi - m, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩; exact ⟨((hvi i).mp h1).1, by have := (hvim i).mp h2; omega⟩
        · intro ⟨h1, h2⟩; exact ⟨(hvi i).mpr ⟨h1, by omega⟩, (hvim i).mpr (by omega)⟩
      · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩; have := (hvi i).mp h1; have := (hvim i).mp h2; omega
        · intro ⟨_, h⟩; omega

/-- OR of bitonic input (b=true case). -/
theorem or_bitonic_true {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = true ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨true, lo, hi, _hlo, h1, fun i ↦ ?_⟩
    rw [Bool.or_eq_true]; constructor
    · intro h; rcases h with h | h
      · exact (hvi i).mp h
      · exact absurd ((hvim i).mp h) (by omega)
    · intro h; exact Or.inl ((hvi i).mpr h)
  · by_cases h2 : m ≤ lo
    · refine ⟨true, lo - m, hi - m, by omega, by omega, fun i ↦ ?_⟩
      rw [Bool.or_eq_true]; constructor
      · intro h; rcases h with h | h
        · exact absurd ((hvi i).mp h) (by omega)
        · have := (hvim i).mp h; omega
      · intro h; exact Or.inr ((hvim i).mpr (by omega))
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨true, 0, m, Nat.zero_le _, Nat.le.refl, fun i ↦ ?_⟩
        rw [Bool.or_eq_true]; constructor
        · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
        · intro _
          by_cases h : lo ≤ i.val
          · exact Or.inl ((hvi i).mpr ⟨h, by omega⟩)
          · exact Or.inr ((hvim i).mpr (by omega))
      · refine ⟨false, hi - m, lo, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩
          have hni : ¬(lo ≤ i.val ∧ i.val < hi) := fun hc ↦ by
            have := (hvi i).mpr hc; rw [h1] at this; exact Bool.noConfusion this
          have hnim : ¬(lo ≤ i.val + m ∧ i.val + m < hi) := fun hc ↦ by
            have := (hvim i).mpr hc; rw [h2] at this; exact Bool.noConfusion this
          omega
        · intro ⟨h1, h2⟩
          exact ⟨by cases hv' : v ⟨i.val, by omega⟩ with
                   | true => exact absurd ((hvi i).mp hv') (by omega)
                   | false => rfl,
                 by cases hv' : v ⟨i.val + m, by omega⟩ with
                   | true => exact absurd ((hvim i).mp hv') (by omega)
                   | false => rfl⟩

end
