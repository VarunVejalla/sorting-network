module
public import AKS.Bounds.Minimum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Order.LiminfLimsup

/-! A construction-independent certificate API for upper bounds on sorting-network depth.

Candidate constructions may use any proof strategy, but they must produce networks in the canonical
`ComparatorNetwork` model and meet this interface. This module then converts the network family to a
bound on `SortingDepth.minimum` and its limsup. -/

@[expose] public section

namespace SortingDepth

open Filter

/-- A global upper-bound certificate: for every sufficiently large input size, provide a sorting
network in the canonical comparator model with depth at most `C * log₂ n + K`. The additive constant
does not affect the limsup coefficient. -/
structure UpperBoundCertificate (C K : ℝ) where
  threshold : ℕ
  network : ∀ n : ℕ, threshold ≤ n →
    ∃ net : ComparatorNetwork n,
      ComparatorNetwork.Sorts.{0} net ∧ (net.depth : ℝ) ≤ C * Real.logb 2 (n : ℝ) + K

/-- A sorting-network certificate bounds the canonical minimum depth pointwise. -/
theorem UpperBoundCertificate.minimum_bound {C K : ℝ} (cert : UpperBoundCertificate C K)
    {n : ℕ} (hn : cert.threshold ≤ n) :
    (minimum n : ℝ) ≤ C * Real.logb 2 (n : ℝ) + K := by
  obtain ⟨net, hsort, hdepth⟩ := cert.network n hn
  have hmin : minimum n ≤ net.depth := minimum_le net hsort
  exact (Nat.cast_le.2 hmin).trans hdepth

/-- Any global network certificate gives the matching limsup bound for the canonical `D(n)`. -/
theorem UpperBoundCertificate.limsup_bound {C K : ℝ} (cert : UpperBoundCertificate C K) :
    limsup (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop ≤ C := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  have hlog_atTop : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hnear (ε : ℝ) (hε : 0 < ε) :
      limsup (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop ≤ C + ε := by
    have hK : ∀ᶠ n : ℕ in atTop, K / ε < Real.logb 2 (n : ℝ) :=
      hlog_atTop.eventually (eventually_gt_atTop (K / ε))
    have hle : ∀ᶠ n : ℕ in atTop,
        (minimum n : ℝ) / Real.logb 2 n ≤ C + ε := by
      filter_upwards [eventually_ge_atTop (max cert.threshold 2), hK] with n hn hk
      have hN : cert.threshold ≤ n := le_trans (Nat.le_max_left _ _) hn
      have h2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
      have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hlog : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
      have hb := cert.minimum_bound hN
      apply (div_le_iff₀ hlog).2
      have hK' : K < ε * Real.logb 2 (n : ℝ) := by
        have h' := (div_lt_iff₀ hε).1 hk
        nlinarith [h']
      nlinarith
    exact (limsup_le_limsup hle
      (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
      isBoundedUnder_const).trans (le_of_eq (limsup_const (C + ε)))
  by_contra hnot
  have hlt : C < limsup (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop := lt_of_not_ge hnot
  let ε := (limsup (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop - C) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h := hnear ε hε
  dsimp [ε] at h
  linarith

end SortingDepth
