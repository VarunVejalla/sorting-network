module

public import AKS.Kahale.InsertionFibers
public import Mathlib.Tactic.Ring

/-! # Exact transfer of relative-order entropy across a boundary

The untouched vector is fixed while the boundary rank changes. This identity
does not bound how often the resulting information is created or destroyed.
-/

@[expose] public section

namespace Kahale

noncomputable def blockRelativeEntropy {Ω ι α : Type*} [Fintype ι] [LinearOrder α]
    (source : Finset Ω) (rest : Ω → ι → α) (rank : Ω → α) : ℝ :=
  finiteEntropy source (fun x ↦ (rest x, rank x)) -
    finiteEntropy source (fun x ↦ insert (rank x) (coordinateRankSet (rest x)))

noncomputable def insertionEntropy {Ω ι α : Type*} [Fintype ι] [LinearOrder α]
    (source : Finset Ω) (rest : Ω → ι → α) (rank : Ω → α) : ℝ :=
  finiteEntropy source (fun x ↦ (insert (rank x) (coordinateRankSet (rest x)),
    insertionOrdinal (coordinateRankSet (rest x)) (rank x))) -
    finiteEntropy source (fun x ↦ insert (rank x) (coordinateRankSet (rest x)))

noncomputable def boundaryCoupling {Ω ι α : Type*} [Fintype ι] [LinearOrder α]
    (source : Finset Ω) (rest : Ω → ι → α) (rank : Ω → α) : ℝ :=
  finiteEntropy source rest +
    finiteEntropy source (fun x ↦ (coordinateRankSet (rest x), rank x)) -
    finiteEntropy source (fun x ↦ coordinateRankSet (rest x)) -
    finiteEntropy source (fun x ↦ (rest x, rank x))

theorem relative_entropy_insertion_coupling {Ω ι α : Type*} [Fintype ι] [LinearOrder α]
    (source : Finset Ω) (rest : Ω → ι → α) (rank : Ω → α)
    (outside : ∀ x ∈ source, rank x ∉ coordinateRankSet (rest x)) :
    blockRelativeEntropy source rest rank = insertionEntropy source rest rank +
      (finiteEntropy source rest - finiteEntropy source (fun x ↦ coordinateRankSet (rest x))) -
      boundaryCoupling source rest rank := by
  unfold blockRelativeEntropy insertionEntropy boundaryCoupling
  rw [entropy_insertion_eq_rankSet_rank source (fun x ↦ coordinateRankSet (rest x)) rank outside]
  ring

theorem boundary_transfer_identity {Ω ι α : Type*} [Fintype ι] [LinearOrder α]
    (source : Finset Ω) (rest : Ω → ι → α) (before after : Ω → α)
    (beforeOutside : ∀ x ∈ source, before x ∉ coordinateRankSet (rest x))
    (afterOutside : ∀ x ∈ source, after x ∉ coordinateRankSet (rest x)) :
    blockRelativeEntropy source rest after - blockRelativeEntropy source rest before =
      (insertionEntropy source rest after - insertionEntropy source rest before) -
      (boundaryCoupling source rest after - boundaryCoupling source rest before) := by
  rw [relative_entropy_insertion_coupling source rest after afterOutside,
    relative_entropy_insertion_coupling source rest before beforeOutside]
  ring

end Kahale
