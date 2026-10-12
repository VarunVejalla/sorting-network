import AKS.Bounds.Minimum
import AKS.Sort.Depth
import AKS.Sort.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup

/-! # Trusted specification of an upper-bound contribution

This file is part of the trusted base (see `upper-bound/TRUSTED.md`); it is fingerprinted by CI.

`BoundSpec C` says: for every `ε > 0`, eventually `D(n) ≤ (C + ε) · log₂ n`, where `D(n)` is the
canonical `SortingDepth.minimum`. This *eventual pointwise* form is used instead of
`Filter.limsup … ≤ C` because in `ℝ` the limsup of a sequence that is not bounded above is the
junk value `0` (`sInf ∅ = 0`), so `limsup ≤ C` alone does not certify a bound. `BoundSpec.limsup_le`
recovers the limsup statement. -/

namespace UpperBoundContrib

open Filter

/-- Trusted statement of an upper bound on `limsup D(n)/log₂ n` by `C`, in eventual pointwise form. -/
def BoundSpec (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (SortingDepth.minimum n : ℝ) ≤ (C + ε) * Real.logb 2 (n : ℝ)

/-- The eventual pointwise bound implies the limsup bound. -/
theorem BoundSpec.limsup_le {C : ℝ} (h : BoundSpec C) :
    limsup (fun n : ℕ => (SortingDepth.minimum n : ℝ) / Real.logb 2 n) atTop ≤ C := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (SortingDepth.minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hle : ∀ᶠ n : ℕ in atTop,
      (SortingDepth.minimum n : ℝ) / Real.logb 2 n ≤ C + ε := by
    filter_upwards [h ε hε, eventually_ge_atTop 2] with n hn h2
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
    exact (div_le_iff₀ hlog).2 hn
  exact (limsup_le_limsup hle
    (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
    isBoundedUnder_const).trans (le_of_eq (limsup_const (C + ε)))

/-- Network form of the same claim, mentioning only comparator networks (no `minimum`): for every
`ε > 0`, for all large `n` there is a sorting network on `n` wires of depth `≤ (C + ε) · log₂ n`.
This is the form used by the comparator `Challenge` (it needs only the definitions of `Comparator`,
`ComparatorNetwork`, `depth` and `Sorts`). -/
def NetSpec (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧
      (net.depth : ℝ) ≤ (C + ε) * Real.logb 2 (n : ℝ)

theorem NetSpec.boundSpec {C : ℝ} (h : NetSpec C) : BoundSpec C := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨net, hsort, hdepth⟩ := hN n hn
  exact le_trans (Nat.cast_le.2 (SortingDepth.minimum_le net hsort)) hdepth

theorem BoundSpec.netSpec {C : ℝ} (h : BoundSpec C) : NetSpec C := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε hε)
  refine ⟨N, fun n hn => ?_⟩
  classical
  have hex := SortingDepth.exists_sorting_depth n
  obtain ⟨net, hsort, hdepth⟩ := Nat.find_spec hex
  refine ⟨net, hsort, ?_⟩
  have hmin : SortingDepth.minimum n = Nat.find hex := rfl
  have := hN n hn
  rw [hmin] at this
  rw [hdepth]
  exact this

end UpperBoundContrib
