module
/- The 0-1 principle: a network sorts all inputs iff it sorts all Boolean inputs. -/

public import AKS.Sort.Monotone

@[expose] public section

open Finset BigOperators

/-- The 0-1 Principle. -/
theorem zero_one_principle {n : ℕ} (net : ComparatorNetwork n) :
    (∀ (v : Fin n → Bool), Monotone (net.exec v)) →
    net.Sorts := by
  intro h_bool α _ v
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  -- threshold function: true iff strictly above `(net.exec v) j`
  have hf : Monotone fun x : α ↦ decide ((net.exec v) j < x) := fun a b hab ↦ by
    by_cases ha : (net.exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have h_sorted := h_bool ((fun x : α ↦ decide ((net.exec v) j < x)) ∘ v) hij
  have hcomm := congr_fun (net.exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

end
