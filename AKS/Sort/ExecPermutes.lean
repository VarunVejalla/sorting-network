module

public import AKS.Sort.Defs

/-! Comparator networks permute wire values (each output equals some input). -/

@[expose] public section

theorem Comparator.apply_exists_preimage {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (k : Fin n) :
    ∃ i : Fin n, c.apply v k = v i := by
  unfold Comparator.apply
  by_cases hki : k = c.i
  · subst hki
    rw [if_pos rfl]
    -- min of two inputs
    by_cases hle : v c.i ≤ v c.j
    · refine ⟨c.i, ?_⟩
      simp [min_eq_left hle]
    · refine ⟨c.j, ?_⟩
      simp [min_eq_right (le_of_not_ge hle)]
  · rw [if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj
      rw [if_pos rfl]
      by_cases hle : v c.i ≤ v c.j
      · refine ⟨c.j, ?_⟩
        simp [max_eq_right hle]
      · refine ⟨c.i, ?_⟩
        simp [max_eq_left (le_of_not_ge hle)]
    · rw [if_neg hkj]
      exact ⟨k, rfl⟩

theorem ComparatorNetwork.exec_exists_preimage {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) (k : Fin n) :
    ∃ i : Fin n, net.exec v k = v i := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact ⟨k, rfl⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    obtain ⟨j, hj⟩ := ih (c.apply v) k
    obtain ⟨i, hi⟩ := Comparator.apply_exists_preimage c v j
    refine ⟨i, ?_⟩
    rw [hj, hi]

end
