module

public import AKS.Separator.PatersonInjective

/-! # Paterson's supported-range separator interface -/

@[expose] public section

open Finset

namespace Paterson

/-- A two-sided separator whose extreme-value guarantee is required only up
to `support * n`. The output fringe size is an integer so the statement also
applies at rounded local sizes. This is deliberately weaker than the existing
`IsSeparator` when the supported cohort is smaller than the fringe. -/
def IsSupportedSeparator {n : ℕ} (net : ComparatorNetwork n)
    (fringe : ℕ) (support err : ℝ) : Prop :=
  ∀ v : Equiv.Perm (Fin n),
    (∀ k : ℕ, (k : ℝ) ≤ support * n →
      ((Finset.univ.filter (fun pos : Fin n =>
        fringe ≤ pos.val ∧ (net.exec v pos).val < k)).card : ℝ) ≤ err * k) ∧
    (∀ k : ℕ, (k : ℝ) ≤ support * n →
      ((Finset.univ.filter (fun pos : Fin n =>
        pos.val < n - fringe ∧ n - k ≤ (net.exec v pos).val)).card : ℝ) ≤ err * k)

theorem restricted_halver_is_supported_separator {m : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α) :
    IsSupportedSeparator net m ((α : ℝ) / 2) ε := by
  intro v
  obtain ⟨hleft, hright⟩ := hnet v
  have hfactor : ((α : ℝ) / 2) * ((2 * m : ℕ) : ℝ) = (α : ℝ) * m := by
    push_cast
    ring
  constructor
  · intro k hk
    have hk' : (k : ℝ) ≤ (α : ℝ) * m := hk.trans_eq hfactor
    exact hleft k hk'
  · intro k hk
    have hk' : (k : ℝ) ≤ (α : ℝ) * m := hk.trans_eq hfactor
    have hh := hright k hk'
    have hnm : 2 * m - m = m := by omega
    simpa [hnm] using hh

theorem supported_separator_mono_support {n fringe : ℕ}
    {net : ComparatorNetwork n} {support₁ support₂ err : ℝ}
    (h : IsSupportedSeparator net fringe support₂ err)
    (hle : support₁ ≤ support₂) :
    IsSupportedSeparator net fringe support₁ err := by
  intro v
  obtain ⟨hl, hr⟩ := h v
  constructor
  · intro k hk
    exact hl k (hk.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))
  · intro k hk
    exact hr k (hk.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))

theorem supported_separator_mono_error {n fringe : ℕ}
    {net : ComparatorNetwork n} {support err₁ err₂ : ℝ}
    (h : IsSupportedSeparator net fringe support err₁)
    (hle : err₁ ≤ err₂) :
    IsSupportedSeparator net fringe support err₂ := by
  intro v
  obtain ⟨hl, hr⟩ := h v
  constructor
  · intro k hk
    exact (hl k hk).trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))
  · intro k hk
    exact (hr k hk).trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))

/-- The shared first-level matching network provides Paterson's restricted
cohort guarantee and the stronger half-split guarantee needed for good values. -/
theorem exists_paterson_first_level_supported (m : ℕ) :
    ∃ net : ComparatorNetwork (2 * m),
      IsSupportedSeparator net m (patersonMu : ℝ) patersonDelta1 ∧
      IsEpsilonAlphaHalver net patersonDelta0 patersonAlpha0 ∧
      net.depth ≤ 263 := by
  obtain ⟨net, hsmall, hlarge, hdepth⟩ :=
    exists_paterson_first_level_all_arities m
  refine ⟨net, ?_, hlarge, hdepth⟩
  simpa using restricted_halver_is_supported_separator hsmall

end Paterson
