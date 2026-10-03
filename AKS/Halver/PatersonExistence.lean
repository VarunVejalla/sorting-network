module

public import AKS.Halver.MatchingCount
public import AKS.Halver.PatersonCorrectness

/-! # Finite probabilistic criterion for Paterson halvers

This file combines the exact matching counts, the two-sided union bound, and
the deterministic correctness proof. Its numerical hypothesis is explicit;
the uniform entropy estimate needed for Paterson's published depth is a
separate obligation.
-/

@[expose] public section

open Finset BigOperators
open scoped Classical

namespace Paterson

/-- A bijection cannot map a larger set entirely into a smaller one. This
discharges trap sizes outside the range of the sharp entropy estimate. -/
theorem exists_escape_of_card_gt {A : Type*} [Fintype A]
    (g : Equiv.Perm A) (X Y : Finset A) (h : Y.card < X.card) :
    ∃ x ∈ X, g x ∉ Y := by
  classical
  by_contra hn
  push_neg at hn
  have hsubset : X.image g ⊆ Y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hn x hx
  have hcard := Finset.card_image_of_injective X g.injective
  have hle := Finset.card_le_card hsubset
  omega

/-- A union bound over specified trap pairs yields matchings that escape
every pair in both orientations. -/
theorem exists_matchings_escaping_pairs {A : Type*} [Fintype A]
    (pairs : Finset (Finset A × Finset A)) (c : ℕ) (hm : 0 < Fintype.card A)
    (hsmall : 2 * (∑ p ∈ pairs,
      ((p.2.card : ℚ) / Fintype.card A) ^ (p.1.card * c)) < 1) :
    ∃ gs : Fin c → Equiv.Perm A, ∀ p ∈ pairs,
      (∃ i, ∃ x ∈ p.1, gs i x ∉ p.2) ∧
      (∃ i, ∃ x ∈ p.1, (gs i).symm x ∉ p.2) := by
  classical
  let samples : Finset (Fin c → Equiv.Perm A) := univ
  let forward := fun p : Finset A × Finset A =>
    samples.filter (fun gs => ∀ i, ∀ x ∈ p.1, gs i x ∈ p.2)
  let backward := fun p : Finset A × Finset A =>
    samples.filter (fun gs => ∀ i, ∀ x ∈ p.1, (gs i).symm x ∈ p.2)
  let bad := fun p => forward p ∪ backward p
  let weight := fun p : Finset A × Finset A =>
    ((p.2.card : ℚ) / Fintype.card A) ^ (p.1.card * c)
  have hs : 0 < samples.card := by
    simp only [samples, card_univ, card_matching_sequences]
    exact pow_pos (Nat.factorial_pos _) c
  have hsQ : (0 : ℚ) < Fintype.card (Fin c → Equiv.Perm A) := by
    exact_mod_cast hs
  have hevent : ∀ p ∈ pairs, ((bad p).card : ℚ) ≤ (2 * weight p) * samples.card := by
    intro p _
    have hf := (div_le_iff₀ hsQ).mp (restricted_matching_sequence_density_le p.1 p.2 c hm)
    have hb := (div_le_iff₀ hsQ).mp (inverse_matching_sequence_density_le p.1 p.2 c hm)
    rw [Fintype.card_subtype] at hf hb
    have hu : ((bad p).card : ℚ) ≤ (forward p).card + (backward p).card := by
      exact_mod_cast card_union_le (forward p) (backward p)
    change ((forward p).card : ℚ) ≤ weight p * samples.card at hf
    change ((backward p).card : ℚ) ≤ weight p * samples.card at hb
    linarith
  have hweight : (∑ p ∈ pairs, 2 * weight p) < 1 := by
    rw [← mul_sum]
    exact hsmall
  obtain ⟨gs, _, hgs⟩ := exists_outside_finset_events_of_density samples pairs bad
    (fun p => 2 * weight p) hs hevent hweight
  refine ⟨gs, ?_⟩
  intro p hp
  have havoid := hgs p hp
  simp only [bad, mem_union, forward, backward, samples, mem_filter, mem_univ,
    true_and, not_or] at havoid
  constructor
  · by_contra hn
    push_neg at hn
    exact havoid.1 hn
  · by_contra hn
    push_neg at hn
    exact havoid.2 hn

/-- If the specified trap pairs cover every potential halver violation and
their explicit probability sum is below one, a depth-`c` restricted halver
exists. No probabilistic or combinatorial premise other than that displayed
finite sum is hidden in this theorem. -/
theorem exists_halver_of_trap_cover {m c : ℕ} {ε α : ℚ} (hm : 0 < m)
    (hcpos : 0 < c)
    (hα : α ≤ 1) (pairs : Finset (Finset (Fin m) × Finset (Fin m)))
    (hcover : ∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m →
      ∀ X Y : Finset (Fin m), (ε : ℝ) * k < X.card → X.card + Y.card ≤ k →
        X.card ≤ Y.card →
        ∃ X' Y', (X', Y') ∈ pairs ∧ X' ⊆ X ∧ Y ⊆ Y')
    (hsmall : 2 * (∑ p ∈ pairs, ((p.2.card : ℚ) / m) ^ (p.1.card * c)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) ε α ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  obtain ⟨gs, hgs⟩ := exists_matchings_escaping_pairs pairs c (by simpa using hm)
    (by simpa using hsmall)
  refine ⟨List.ofFn gs, List.length_ofFn, ?_, ?_⟩
  · apply isHalver_of_noSmallTraps _ hα
    intro k hk X Y hx hxy
    by_cases hXY : X.card ≤ Y.card
    · obtain ⟨X', Y', hp, hX, hY⟩ := hcover k hk X Y hx hxy hXY
      obtain ⟨hf, hb⟩ := hgs (X', Y') hp
      constructor
      · obtain ⟨i, x, hx, hnot⟩ := hf
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hX hx, fun hy => hnot (hY hy)⟩
      · obtain ⟨i, x, hx, hnot⟩ := hb
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hX hx, fun hy => hnot (hY hy)⟩
    · have hgt : Y.card < X.card := by omega
      let i : Fin c := ⟨0, hcpos⟩
      constructor
      · obtain ⟨x, hx, hnot⟩ := exists_escape_of_card_gt (gs i) X Y hgt
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hx, hnot⟩
      · obtain ⟨x, hx, hnot⟩ := exists_escape_of_card_gt (gs i).symm X Y hgt
        exact ⟨gs i, List.mem_ofFn.mpr ⟨i, rfl⟩, x, hx, hnot⟩
  · simpa using patersonMatchingNetwork_depth_le (List.ofFn gs)

/-- Trap pairs with specified cardinalities. -/
def pairsOfSizes (m : ℕ) (rs : ℕ × ℕ) : Finset (Finset (Fin m) × Finset (Fin m)) :=
  (univ.powersetCard rs.1) ×ˢ (univ.powersetCard rs.2)

/-- Distinct cardinality pairs describe disjoint collections of traps. -/
theorem pairsOfSizes_disjoint (m : ℕ) {rs uv : ℕ × ℕ} (hne : rs ≠ uv) :
    Disjoint (pairsOfSizes m rs) (pairsOfSizes m uv) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  simp only [pairsOfSizes, mem_product, mem_powersetCard] at hp hq
  apply hne
  exact Prod.ext (hp.1.2.symm.trans hq.1.2) (hp.2.2.symm.trans hq.2.2)

/-- Counting choices for the two vertex sets gives the two binomial factors
in Paterson's failure-probability bound. -/
theorem sum_trap_weights (m c : ℕ) (sizes : Finset (ℕ × ℕ)) :
    (∑ p ∈ sizes.biUnion (pairsOfSizes m),
      ((p.2.card : ℚ) / m) ^ (p.1.card * c)) =
    ∑ rs ∈ sizes, (m.choose rs.1 : ℚ) * m.choose rs.2 *
      ((rs.2 : ℚ) / m) ^ (rs.1 * c) := by
  rw [Finset.sum_biUnion (fun rs _ uv _ hne => pairsOfSizes_disjoint m hne)]
  apply sum_congr rfl
  intro rs _
  calc
    _ = ∑ _p ∈ pairsOfSizes m rs, ((rs.2 : ℚ) / m) ^ (rs.1 * c) := by
      apply sum_congr rfl
      intro p hp
      simp only [pairsOfSizes, mem_product, mem_powersetCard] at hp
      rw [hp.1.2, hp.2.2]
    _ = _ := by
      simp [pairsOfSizes, card_product, card_powersetCard, mul_assoc]

/-- Explicit finite-size version of the probabilistic halver theorem. The
only estimate still required is the displayed scalar sum over size pairs.
The covering condition permits reducing all failures to Paterson's smaller
list of witnesses before applying that estimate. -/
theorem exists_halver_of_size_bound {m c : ℕ} {ε α : ℚ} (hm : 0 < m)
    (hcpos : 0 < c)
    (hα : α ≤ 1) (sizes : Finset (ℕ × ℕ))
    (hcover : ∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m →
      ∀ t : ℕ, (ε : ℝ) * k < t → 2 * t ≤ k →
        ∃ rs ∈ sizes, rs.1 ≤ t ∧ k - t ≤ rs.2 ∧ rs.2 ≤ m)
    (hsmall : 2 * (∑ rs ∈ sizes, (m.choose rs.1 : ℚ) * m.choose rs.2 *
      ((rs.2 : ℚ) / m) ^ (rs.1 * c)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) ε α ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  apply exists_halver_of_trap_cover hm hcpos hα (sizes.biUnion (pairsOfSizes m))
  · intro k hk X Y hx hxy hXY
    obtain ⟨rs, hrs, hr, hs, hsm⟩ := hcover k hk X.card hx (by omega)
    obtain ⟨X', hX', hcX'⟩ := exists_subset_card_eq hr
    obtain ⟨Y', hY', _, hcY'⟩ := exists_subsuperset_card_eq
      (subset_univ Y) (show Y.card ≤ rs.2 from by omega)
      (show rs.2 ≤ (univ : Finset (Fin m)).card from by simpa using hsm)
    refine ⟨X', Y', mem_biUnion.mpr ⟨rs, hrs, ?_⟩, hX', hY'⟩
    simp [pairsOfSizes, hcX', hcY']
  · rw [sum_trap_weights]
    exact hsmall

end Paterson
