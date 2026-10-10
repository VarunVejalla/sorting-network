module

public import AKS.Kahale.FiniteFibers
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Entropy from uniform-source fiber multiplicities

The target distribution need not be uniform. This input-average expression
is Shannon entropy in bits when the finite source is nonempty. Empty sources
use Lean's total logarithm/division conventions. No entropy inequality is
proved by this module.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

noncomputable def finiteEntropy {α β : Type*} [DecidableEq β]
    (source : Finset α) (f : α → β) : ℝ :=
  Real.log (source.card : ℝ) / Real.log 2 -
    (∑ x ∈ source, Real.log (fiberCount source f (f x) : ℝ)) /
      ((source.card : ℝ) * Real.log 2)

theorem finiteEntropy_eq_of_sameFibers {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (source : Finset α) (f : α → β) (g : α → γ)
    (same : ∀ x ∈ source, ∀ y ∈ source, f y = f x ↔ g y = g x) :
    finiteEntropy source f = finiteEntropy source g := by
  classical
  have hs : (∑ x ∈ source, Real.log (fiberCount source f (f x) : ℝ)) =
      ∑ x ∈ source, Real.log (fiberCount source g (g x) : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hfilter : source.filter (fun y ↦ f y = f x) =
        source.filter (fun y ↦ g y = g x) := by
      ext y
      simp only [Finset.mem_filter]
      exact and_congr_right (fun hy ↦ same x hx y hy)
    have hc : fiberCount source f (f x) = fiberCount source g (g x) :=
      congrArg Finset.card hfilter
    rw [hc]
  unfold finiteEntropy
  rw [hs]

end Kahale
