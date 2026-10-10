module

public import AKS.Separator.PatersonCertificate
public import AKS.Sort.Displaced

/-! # The first-level good-value contract survives the separator

Paterson (1990), Section 8, needs the first-level large-cohort guarantee in
addition to the small-cohort fringe guarantee. Appending any comparator
network can only reduce displaced extreme values, so subsequent refinement
levels preserve that guarantee.
-/

@[expose] public section

namespace Paterson

theorem IsEpsilonAlphaHalver.append {m : ℕ} {ε α : ℚ}
    {first : ComparatorNetwork (2 * m)}
    (hfirst : IsEpsilonAlphaHalver first ε α)
    (rest : ComparatorNetwork (2 * m)) :
    IsEpsilonAlphaHalver ⟨first.comparators ++ rest.comparators⟩ ε α := by
  intro v
  constructor
  · intro k hk
    rw [ComparatorNetwork.exec_append]
    have hle := exec_displaced_le rest (first.exec v) m k
    have hleR :
        ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
          m ≤ pos.val ∧ (rest.exec (first.exec v) pos).val < k)).card : ℝ) ≤
        ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
          m ≤ pos.val ∧ (first.exec v pos).val < k)).card : ℝ) := by
      exact_mod_cast hle
    exact hleR.trans ((hfirst v).1 k hk)
  · intro k hk
    rw [ComparatorNetwork.exec_append]
    have hle := exec_displaced_final_le rest (first.exec v) m (2 * m - k)
    have hleR :
        ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
          pos.val < m ∧ 2 * m - k ≤ (rest.exec (first.exec v) pos).val)).card : ℝ) ≤
        ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
          pos.val < m ∧ 2 * m - k ≤ (first.exec v pos).val)).card : ℝ) := by
      exact_mod_cast hle
    exact hleR.trans ((hfirst v).2 k hk)

theorem shiftEmbed_zero_self {n : ℕ} (net : ComparatorNetwork n)
    (h : 0 + n ≤ n) : net.shiftEmbed n 0 h = net := by
  apply ComparatorNetwork.ext
  simp only [ComparatorNetwork.shiftEmbed]
  conv_rhs => rw [← List.map_id net.comparators]
  apply List.map_congr_left
  intro c _
  cases c
  congr 1 <;> apply Fin.ext <;> simp

theorem halverAtLevel_even_zero (m : ℕ)
    (halvers : (s : ℕ) → ComparatorNetwork (2 * s)) :
    halverAtLevel (2 * m) halvers 0 = halvers m := by
  unfold halverAtLevel
  dsimp only
  have hh : 2 * m / 2 ^ 0 / 2 = m := by omega
  simp only [hh]
  simp only [applyHalverToSubinterval, pow_zero, List.range_one,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.zero_mul,
    Nat.zero_add, dif_pos (show 2 * m ≤ 2 * m by omega), shiftEmbed_zero_self]

/-- The five-level network retains the jointly selected first-level contract
at every even arity, including zero. No divisibility-by-32 hypothesis is needed
for this half-split property. -/
theorem separatorNetwork_good (m : ℕ) :
    IsEpsilonAlphaHalver (separatorNetwork (2 * m))
      patersonDelta0 patersonAlpha0 := by
  let rest : ComparatorNetwork (2 * m) :=
    ⟨([1, 2, 3, 4] : List ℕ).flatMap fun level ↦
      (halverAtLevel (2 * m) (stageNetwork level) level).comparators⟩
  have hsplit : separatorNetwork (2 * m) =
      ⟨(firstLevelNetwork m).comparators ++ rest.comparators⟩ := by
    unfold separatorNetwork
    change (⟨(halverAtLevel (2 * m) (stageNetwork 0) 0).comparators ++
      rest.comparators⟩ : ComparatorNetwork (2 * m)) = _
    rw [halverAtLevel_even_zero]
    rfl
  rw [hsplit]
  exact IsEpsilonAlphaHalver.append (firstLevelNetwork_good m) rest

/-- Enlarging the protected fringe only improves the supported-cohort
guarantee, as required by the integer fringe recipe in Section 7. -/
theorem supported_separator_mono_fringe {n f₁ f₂ : ℕ}
    {net : ComparatorNetwork n} {support err : ℝ}
    (h : IsSupportedSeparator net f₁ support err) (hf : f₁ ≤ f₂) :
    IsSupportedSeparator net f₂ support err := by
  intro v
  obtain ⟨hl, hr⟩ := h v
  constructor
  · intro k hk
    apply le_trans _ (hl k hk)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro pos hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    exact ⟨hf.trans hpos.1, hpos.2⟩
  · intro k hk
    apply le_trans _ (hr k hk)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro pos hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    exact ⟨by omega, hpos.2⟩

end Paterson
