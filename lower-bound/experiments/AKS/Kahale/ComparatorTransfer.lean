module

public import AKS.Kahale.BoundaryTransfer
public import AKS.Kahale.ComparatorBoundary

/-! # The boundary identity for an actual comparator

The fixed positions omit both comparator endpoints. Distinctness follows
from the input permutation and injectivity preservation, not a new assumption
about a uniform rank image.
-/

@[expose] public section

namespace Kahale

theorem comparator_boundary_transfer {Ω ι : Type*} {n : ℕ} [Fintype ι]
    (source : Finset Ω) (f : Ω → Fin n → Fin n) (c : Comparator n)
    (positions : ι → Fin n)
    (outside : ∀ t, positions t ≠ c.i ∧ positions t ≠ c.j)
    (hinj : ∀ x ∈ source, Function.Injective (f x)) :
    let rest := fun x t ↦ f x (positions t)
    let before := fun x ↦ f x c.i
    let after := fun x ↦ c.apply (f x) c.i
    blockRelativeEntropy source rest after - blockRelativeEntropy source rest before =
      (insertionEntropy source rest after - insertionEntropy source rest before) -
      (boundaryCoupling source rest after - boundaryCoupling source rest before) := by
  classical
  apply boundary_transfer_identity
  · intro x hx hmem
    rcases Finset.mem_image.mp hmem with ⟨t, _, ht⟩
    exact (outside t).1 ((hinj x hx) ht)
  · intro x hx hmem
    rcases Finset.mem_image.mp hmem with ⟨t, _, ht⟩
    have he : c.apply (f x) (positions t) = c.apply (f x) c.i := by
      simpa [Comparator.apply, (outside t).1, (outside t).2] using ht
    exact (outside t).1 ((c.apply_injective (hinj x hx)) he)

end Kahale
