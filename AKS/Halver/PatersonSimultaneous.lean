module

public import AKS.Halver.PatersonTail

/-! # Two restricted-halver contracts on one matching sequence -/

@[expose] public section

open Finset

namespace Paterson

theorem trap_union_weight_le_sum {m c : ℕ}
    (pairs₀ pairs₁ : Finset (Finset (Fin m) × Finset (Fin m))) :
    (∑ p ∈ pairs₀ ∪ pairs₁,
      ((p.2.card : ℚ) / m) ^ (p.1.card * c)) ≤
      (∑ p ∈ pairs₀,
        ((p.2.card : ℚ) / m) ^ (p.1.card * c)) +
      (∑ p ∈ pairs₁,
        ((p.2.card : ℚ) / m) ^ (p.1.card * c)) := by
  let w : Finset (Fin m) × Finset (Fin m) → ℚ := fun p =>
    ((p.2.card : ℚ) / m) ^ (p.1.card * c)
  have hdisj : Disjoint (pairs₀ \ pairs₁) pairs₁ := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 hq
  have hunion : (pairs₀ \ pairs₁) ∪ pairs₁ = pairs₀ ∪ pairs₁ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hsub : pairs₀ \ pairs₁ ⊆ pairs₀ := Finset.sdiff_subset
  have hle : (∑ p ∈ pairs₀ \ pairs₁, w p) ≤ ∑ p ∈ pairs₀, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  change (∑ p ∈ pairs₀ ∪ pairs₁, w p) ≤
    (∑ p ∈ pairs₀, w p) + ∑ p ∈ pairs₁, w p
  rw [← hunion, Finset.sum_union hdisj]
  exact add_le_add hle le_rfl

/-- A single matching sequence can satisfy two restricted-halver contracts
whenever the union of their trap families has total density below one. This
is the exact interface needed for the first level of Paterson's separator. -/
theorem exists_simultaneous_halver_of_trap_covers
    {m c : ℕ} {e₀ a₀ e₁ a₁ : ℚ} (hm : 0 < m) (hcpos : 0 < c)
    (ha₀ : a₀ ≤ 1) (ha₁ : a₁ ≤ 1)
    (pairs₀ pairs₁ : Finset (Finset (Fin m) × Finset (Fin m)))
    (hcover₀ : ∀ k : ℕ, (k : ℝ) ≤ (a₀ : ℝ) * m →
      ∀ X Y : Finset (Fin m), (e₀ : ℝ) * k < X.card →
        X.card + Y.card ≤ k → X.card ≤ Y.card →
        ∃ X' Y', (X', Y') ∈ pairs₀ ∧ X' ⊆ X ∧ Y ⊆ Y')
    (hcover₁ : ∀ k : ℕ, (k : ℝ) ≤ (a₁ : ℝ) * m →
      ∀ X Y : Finset (Fin m), (e₁ : ℝ) * k < X.card →
        X.card + Y.card ≤ k → X.card ≤ Y.card →
        ∃ X' Y', (X', Y') ∈ pairs₁ ∧ X' ⊆ X ∧ Y ⊆ Y')
    (hsmall : 2 * (∑ p ∈ pairs₀ ∪ pairs₁,
      ((p.2.card : ℚ) / m) ^ (p.1.card * c)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e₀ a₀ ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e₁ a₁ ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  obtain ⟨gs, hgs⟩ := exists_matchings_escaping_pairs (pairs₀ ∪ pairs₁) c
    (by simpa using hm) (by simpa using hsmall)
  let gList := List.ofFn gs
  have makeHalver : ∀ (e a : ℚ)
      (pairs : Finset (Finset (Fin m) × Finset (Fin m))),
      a ≤ 1 → pairs ⊆ pairs₀ ∪ pairs₁ →
      (∀ k : ℕ, (k : ℝ) ≤ (a : ℝ) * m →
        ∀ X Y : Finset (Fin m), (e : ℝ) * k < X.card →
          X.card + Y.card ≤ k → X.card ≤ Y.card →
          ∃ X' Y', (X', Y') ∈ pairs ∧ X' ⊆ X ∧ Y ⊆ Y') →
      IsEpsilonAlphaHalver (patersonMatchingNetwork gList) e a := by
    intro e a pairs ha hsubset hcover
    apply isHalver_of_noSmallTraps _ ha
    intro k hk X Y hx hxy
    by_cases hXY : X.card ≤ Y.card
    · obtain ⟨X', Y', hp, hX, hY⟩ := hcover k hk X Y hx hxy hXY
      obtain ⟨hf, hb⟩ := hgs (X', Y') (hsubset hp)
      constructor
      · obtain ⟨i, x, hx, hnot⟩ := hf
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x,
          hX hx, fun hy => hnot (hY hy)⟩
      · obtain ⟨i, x, hx, hnot⟩ := hb
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x,
          hX hx, fun hy => hnot (hY hy)⟩
    · have hgt : Y.card < X.card := by omega
      let i : Fin c := ⟨0, hcpos⟩
      constructor
      · obtain ⟨x, hx, hnot⟩ := exists_escape_of_card_gt (gs i) X Y hgt
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hx, hnot⟩
      · obtain ⟨x, hx, hnot⟩ := exists_escape_of_card_gt (gs i).symm X Y hgt
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hx, hnot⟩
  refine ⟨gList, List.length_ofFn, ?_, ?_, ?_⟩
  · exact makeHalver e₀ a₀ pairs₀ ha₀ Finset.subset_union_left hcover₀
  · exact makeHalver e₁ a₁ pairs₁ ha₁ Finset.subset_union_right hcover₁
  · simpa [gList] using patersonMatchingNetwork_depth_le (List.ofFn gs)

end Paterson
