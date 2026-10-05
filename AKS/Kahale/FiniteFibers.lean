module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite fiber accounting

Independent of comparators and entropy. Intermediate states carry their
actual fiber multiplicities; no uniform-image assumption is made.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

def fiberCount {α β : Type*} [DecidableEq β] (source : Finset α)
    (f : α → β) (y : β) : ℕ :=
  (source.filter (fun x ↦ f x = y)).card

theorem fiberCount_comp {α β γ : Type*} [Fintype β] [DecidableEq β]
    [DecidableEq γ] (source : Finset α) (f : α → β) (g : β → γ) (z : γ) :
    fiberCount source (g ∘ f) z =
      ∑ y ∈ Finset.univ.filter (fun y ↦ g y = z), fiberCount source f y := by
  classical
  unfold fiberCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext x
  simp

theorem fiberCount_total {α β : Type*} [Fintype β] [DecidableEq β]
    (source : Finset α) (f : α → β) :
    ∑ y : β, fiberCount source f y = source.card := by
  classical
  unfold fiberCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

end Kahale
