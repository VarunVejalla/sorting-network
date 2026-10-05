module

public import AKS.Kahale.PermutationCompletion
public import AKS.Sort.Defs

/-! # Comparator boundary reconstruction

On rank permutations, the untouched ranks determine the whole comparator
output. This is the combinatorial foundation for the exact single-gate
information identity. The entropy identity is not formalized here.
-/

@[expose] public section

namespace Kahale

theorem comparator_apply_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    c.apply (fun i ↦ v (Equiv.swap c.i c.j i)) = c.apply v := by
  funext k
  by_cases hi : k = c.i
  · subst k
    simp [Comparator.apply, min_comm]
  · by_cases hj : k = c.j
    · subst k
      simp [Comparator.apply, ne_of_gt c.h, max_comm]
    · simp [Comparator.apply, hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem comparator_output_of_untouched_ranks {n : ℕ} (c : Comparator n)
    (v w : Fin n → Fin n) (hv : Function.Injective v) (hw : Function.Injective w)
    (agree : ∀ k, k ≠ c.i → k ≠ c.j → v k = w k) : c.apply v = c.apply w := by
  rcases permutation_eq_or_swap_of_agree_except_two v w hv hw c.i c.j agree with h | h
  · rw [h]
  · rw [h]
    exact comparator_apply_swap c w

theorem comparator_untouched_projection {n : ℕ} {ι α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (positions : ι → Fin n)
    (outside : ∀ t, positions t ≠ c.i ∧ positions t ≠ c.j) :
    c.apply v ∘ positions = v ∘ positions := by
  funext t
  simp [Comparator.apply, (outside t).1, (outside t).2]

end Kahale
