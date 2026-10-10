module
/- Permutation principle helper: any `v : Fin n → α` is monotone after a permutation. -/

public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-- For any `v : Fin n → α`, there is a permutation `σ` with `v ∘ σ.symm` monotone. -/
theorem exists_sorting_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (v : Fin n → α) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (v ∘ ⇑σ.symm) :=
  ⟨(Tuple.sort v).symm, by simpa using Tuple.monotone_sort v⟩

end
