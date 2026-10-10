module

public import AKS.Kahale.FiniteEntropy
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Entropy decreases under deterministic coarsening

This also proves nonnegativity of conditional entropy. It does not prove
conditional mutual-information nonnegativity, which needs a stronger argument.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

theorem fiberCount_pos_of_mem {α β : Type*} [DecidableEq β]
    (source : Finset α) (f : α → β) (x : α) (hx : x ∈ source) :
    0 < fiberCount source f (f x) := by
  apply Finset.card_pos.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

theorem fiberCount_le_comp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (source : Finset α) (f : α → β) (g : β → γ) (x : α) :
    fiberCount source f (f x) ≤ fiberCount source (g ∘ f) (g (f x)) := by
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_filter.mp hy with ⟨hy, he⟩
  exact Finset.mem_filter.mpr ⟨hy, congrArg g he⟩

theorem finiteEntropy_comp_le {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (source : Finset α) (f : α → β) (g : β → γ) :
    finiteEntropy source (g ∘ f) ≤ finiteEntropy source f := by
  classical
  have hs : (∑ x ∈ source, Real.log (fiberCount source f (f x) : ℝ)) ≤
      ∑ x ∈ source, Real.log (fiberCount source (g ∘ f) (g (f x)) : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Real.log_le_log
    · exact_mod_cast fiberCount_pos_of_mem source f x hx
    · exact_mod_cast fiberCount_le_comp source f g x
  have hden : 0 ≤ (source.card : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.log_pos (by norm_num)))
  have hd := div_le_div_of_nonneg_right hs hden
  unfold finiteEntropy
  simpa only [Function.comp_apply] using sub_le_sub_left hd
    (Real.log (source.card : ℝ) / Real.log 2)

theorem finiteConditionalEntropy_nonneg {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (source : Finset α) (f : α → β) (g : α → γ) :
    0 ≤ finiteEntropy source (fun x ↦ (f x, g x)) - finiteEntropy source g := by
  have h := finiteEntropy_comp_le source (fun x ↦ (f x, g x)) Prod.snd
  change finiteEntropy source g ≤ finiteEntropy source (fun x ↦ (f x, g x)) at h
  exact sub_nonneg.mpr h

end Kahale
