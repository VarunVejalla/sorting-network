module

public import AKS.Sort.Perm
public import AKS.Sort.ZeroOne

/-! # Coalescing every two-bit face suffices for sorting

The Johnson graph on subsets of fixed cardinality is connected: exchanging
one element at a time connects any two vertices. This retains exact input
identities and does not provide a quantitative depth lower bound.
-/

@[expose] public section

namespace Kahale

open Finset

theorem exchange_constant_of_equal_card {α β : Type*} [DecidableEq α]
    (f : Finset α → β)
    (exchange : ∀ (s : Finset α) (p q : α), p ∉ s → q ∉ s →
      f (insert p s) = f (insert q s))
    (a b : Finset α) (cardEq : a.card = b.card) : f a = f b := by
  classical
  suffices h : ∀ m (a : Finset α), (a \ b).card = m → a.card = b.card → f a = f b by
    exact h _ a rfl cardEq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a hm hc
    by_cases hab : a = b
    · exact congrArg f hab
    have hsub : ¬ a ⊆ b := by
      intro hs
      exact hab (eq_of_subset_of_card_le hs hc.symm.le)
    have hsub' : ¬ b ⊆ a := by
      intro hs
      exact hab (eq_of_subset_of_card_le hs hc.le).symm
    obtain ⟨p, hp, hpb⟩ := not_subset.mp hsub
    obtain ⟨q, hq, hqa⟩ := not_subset.mp hsub'
    let next := insert q (a.erase p)
    have hqe : q ∉ a.erase p := fun he ↦ hqa (mem_of_mem_erase he)
    have hnext : next.card = b.card := by
      simp only [next, card_insert_of_notMem hqe, card_erase_of_mem hp]
      have ha : 0 < a.card := card_pos.mpr ⟨p, hp⟩
      omega
    have hdiff : next \ b = (a \ b).erase p := by
      ext x
      simp only [next, mem_sdiff, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hxp, hxa⟩, hxb⟩
        · exact False.elim (hxb hq)
        · exact ⟨hxp, hxa, hxb⟩
      · rintro ⟨hxp, hxa, hxb⟩
        exact ⟨Or.inr ⟨hxp, hxa⟩, hxb⟩
    have hlt : (next \ b).card < m := by
      rw [hdiff, ← hm]
      exact card_erase_lt_of_mem (mem_sdiff.mpr ⟨hp, hpb⟩)
    have he := exchange (a.erase p) p q (notMem_erase p a) hqe
    rw [insert_erase hp] at he
    exact he.trans (ih _ hlt next rfl hnext)

def faceSetInput {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i ↦ decide (i ∈ s)

def CoalescesAllFaces {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (s : Finset (Fin n)) (p q : Fin n), p ∉ s → q ∉ s →
    net.exec (faceSetInput (insert p s)) = net.exec (faceSetInput (insert q s))

theorem coalescence_equal_weight {n : ℕ} (net : ComparatorNetwork n)
    (h : CoalescesAllFaces net) (a b : Finset (Fin n)) (hc : a.card = b.card) :
    net.exec (faceSetInput a) = net.exec (faceSetInput b) :=
  exchange_constant_of_equal_card (fun s ↦ net.exec (faceSetInput s)) h a b hc

/-- The exact coupled-input requirement suffices for full sorting by the
0–1 principle. No relaxation to independent routing paths is made. -/
theorem sorts_of_coalesces_all_faces {n : ℕ} (net : ComparatorNetwork n)
    (h : CoalescesAllFaces net) : net.Sorts := by
  classical
  apply zero_one_principle
  intro v
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g := v ∘ σ.symm
  let a := univ.filter (fun i ↦ v i = true)
  let b := univ.filter (fun i ↦ g i = true)
  have ha : faceSetInput a = v := by
    funext i
    cases he : v i <;> simp [faceSetInput, a, he]
  have hb : faceSetInput b = g := by
    funext i
    cases he : g i <;> simp [faceSetInput, b, he]
  have hc : a.card = b.card := by
    apply card_nbij' σ σ.symm
    · intro i hi
      simpa [a, b, g, Function.comp_apply] using hi
    · intro i hi
      simpa [a, b, g, Function.comp_apply] using hi
    · intro i _
      exact σ.symm_apply_apply i
    · intro i _
      exact σ.apply_symm_apply i
  have he := coalescence_equal_weight net h a b hc
  rw [ha, hb, net.exec_eq_of_monotone hg] at he
  rw [he]
  exact hg

end Kahale
