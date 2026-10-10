module

public import AKS.Kahale.LayerBank
public import Mathlib.Tactic.FieldSimp

/-! # Centered relative-order progress

This module proves the algebraic endpoint cancellation. The interpretation
of completion as conditional relative-order entropy and the structural local
budget are separate obligations, not assumptions hidden in this definition.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

noncomputable def centeredProgress (terminal initialEntropy completion information : ℝ) : ℝ :=
  completion - terminal / initialEntropy * information

theorem centeredProgress_initial (terminal initialEntropy : ℝ) :
    centeredProgress terminal initialEntropy 0 0 = 0 := by
  simp [centeredProgress]

theorem centeredProgress_terminal (terminal initialEntropy : ℝ)
    (h : initialEntropy ≠ 0) :
    centeredProgress terminal initialEntropy terminal initialEntropy = 0 := by
  unfold centeredProgress
  field_simp
  ring

/-- Fixed scale weights preserve the cancellation of every component. -/
theorem weighted_centered_endpoint {ι : Type*} (scales : Finset ι)
    (weight terminal : ι → ℝ) (initialEntropy : ℝ) (h : initialEntropy ≠ 0) :
    (∑ k ∈ scales, weight k * centeredProgress (terminal k) initialEntropy 0 0) -
      (∑ k ∈ scales, weight k *
        centeredProgress (terminal k) initialEntropy (terminal k) initialEntropy) = 0 := by
  simp [centeredProgress_initial, centeredProgress_terminal _ _ h]

end Kahale
