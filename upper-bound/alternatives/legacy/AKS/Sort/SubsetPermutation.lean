module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Card

/-! A fixed permutation can match two equally sized subsets. -/

@[expose] public section

open Finset

theorem exists_perm_subset_transport {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) (h : s.card = t.card) :
    ∃ g : Equiv.Perm α, ∀ a, a ∈ s ↔ g a ∈ t := by
  classical
  let e := Finset.equivOfCardEq h
  have hc : sᶜ.card = tᶜ.card := by simp [card_compl, h]
  let ec := Finset.equivOfCardEq hc
  let f : α → α := fun a ↦ if ha : a ∈ s then (e ⟨a, ha⟩).val
    else (ec ⟨a, mem_compl.mpr ha⟩).val
  have hf (a : α) : a ∈ s ↔ f a ∈ t := by
    by_cases ha : a ∈ s
    · simp only [f, dif_pos ha]
      exact iff_of_true ha (e ⟨a, ha⟩).property
    · simp only [f, dif_neg ha]
      exact iff_of_false ha (mem_compl.mp (ec ⟨a, mem_compl.mpr ha⟩).property)
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : a ∈ s ↔ b ∈ s := (hf a).trans (hab ▸ (hf b).symm)
    by_cases ha : a ∈ s
    · have hb := heq.mp ha
      simp only [f, dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (e.injective (Subtype.ext hab))
    · have hb : b ∉ s := fun hb ↦ ha (heq.mpr hb)
      simp only [f, dif_neg ha, dif_neg hb] at hab
      exact congrArg Subtype.val (ec.injective (Subtype.ext hab))
  have hsurj : Function.Surjective f := by
    intro b
    by_cases hb : b ∈ t
    · let a := e.symm ⟨b, hb⟩
      refine ⟨a.val, ?_⟩
      simp only [f, dif_pos a.property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    · let a := ec.symm ⟨b, mem_compl.mpr hb⟩
      refine ⟨a.val, ?_⟩
      simp only [f, dif_neg (mem_compl.mp a.property)]
      exact congrArg Subtype.val (ec.apply_symm_apply ⟨b, mem_compl.mpr hb⟩)
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩
