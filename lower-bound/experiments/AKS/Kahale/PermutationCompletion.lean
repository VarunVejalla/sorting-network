module

public import AKS.Kahale.RelativeOrderCode
public import Mathlib.Data.Fintype.Card

/-! # Completing a rank permutation from the untouched coordinates

The ranks off a compared pair determine its unordered pair of missing ranks.
This supports the conditional-information interpretation of a comparator.
-/

@[expose] public section

namespace Kahale

theorem permutation_eq_of_agree_except_one {n : ℕ} (v w : Fin n → Fin n)
    (hv : Function.Injective v) (hw : Function.Injective w) (missing : Fin n)
    (agree : ∀ i, i ≠ missing → v i = w i) : v = w := by
  funext i
  by_cases hi : i = missing
  · subst i
    by_contra h
    obtain ⟨j, hj⟩ := Finite.surjective_of_injective hw (v missing)
    have hne : j ≠ missing := by
      intro he
      subst j
      exact h hj.symm
    have he : v j = v missing := (agree j hne).trans hj
    exact hne (hv he)
  · exact agree i hi

theorem permutation_eq_or_swap_of_agree_except_two {n : ℕ}
    (v w : Fin n → Fin n) (hv : Function.Injective v) (hw : Function.Injective w)
    (i j : Fin n)
    (agree : ∀ k, k ≠ i → k ≠ j → v k = w k) :
    v = w ∨ v = fun k ↦ w (Equiv.swap i j k) := by
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hw (v i)
  by_cases hki : k = i
  · subst k
    left
    apply permutation_eq_of_agree_except_one v w hv hw j
    intro k hkj
    by_cases hki : k = i
    · subst k; exact hk.symm
    · exact agree k hki hkj
  · have hkj : k = j := by
      by_contra hkj
      have he : v k = v i := (agree k hki hkj).trans hk
      exact hki (hv he)
    subst k
    right
    apply permutation_eq_of_agree_except_one v
      (fun k ↦ w (Equiv.swap i j k)) hv (hw.comp (Equiv.swap i j).injective) j
    intro k hkj
    by_cases hki : k = i
    · subst k; simpa using hk.symm
    · simpa [Equiv.swap_apply_of_ne_of_ne hki hkj] using agree k hki hkj

end Kahale
