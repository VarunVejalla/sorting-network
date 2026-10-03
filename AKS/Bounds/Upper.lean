import AKS.Seiferas

/-! # A complete improved upper bound and the minimum depth

This is a conservative parameter improvement of the existing Seiferas/MGG
construction. It is independent of the unfinished rounded Paterson bag proof.
All logarithms in the finite bound are base two.
-/

namespace SortingDepth

/-- Rational parameters satisfying the already proved global bag invariant.
The larger separator error reduces its depth sufficiently to offset the
increased number of stages. -/
def tunedParams : Params where
  γ := 1 / 64
  ε := 1 / 57
  ν := 41 / 50
  A := 8
  hγ_pos := by norm_num
  hγ_half := by norm_num
  hε_pos := by norm_num
  hε_lt := by norm_num
  hA := by norm_num
  hν_pos := by norm_num
  hν_lt := by norm_num
  h2εA := by norm_num
  hC3 := by norm_num
  hC4_gt1 := by norm_num
  hC4_eq1 := by norm_num
  hC_bound := by norm_num
  hA2_le := by norm_num

/-- Numerical certificate for the full global depth coefficient, rather than
only a local halver or ideal shrink coefficient. -/
theorem tunedParams_depth_le : tunedParams.depth ≤ 102 * 10 ^ 62 := by
  decide +kernel

/-- The full construction with tuned parameters, restricted from the next
power of two. The small finite cases use the existing bitonic network. -/
def upperNetwork (n : ℕ) : ComparatorNetwork n :=
  if h : 1024 ≤ n then
    (seiferasNetwork tunedParams (Nat.clog 2 n)).restrictWires n
      (Nat.le_pow_clog (by omega) n)
  else bitonicNetwork n

theorem upperNetwork_sorts (n : ℕ) : (upperNetwork n).Sorts := by
  unfold upperNetwork
  split
  · rename_i h
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact restrictWires_sorts _ _ _ (fun v ↦ (seiferasNetwork_sorts _ _ hk) _ v)
  · exact bitonicNetwork_sorts n

theorem upperNetwork_depth_le (n : ℕ) :
    (upperNetwork n).depth ≤ 102 * 10 ^ 62 * Nat.clog 2 n := by
  unfold upperNetwork
  split
  · rename_i h
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact (restrictWires_depth_le _ _ _).trans
      ((seiferasNetwork_depth_le _ _ hk).trans
        (Nat.mul_le_mul_right _ tunedParams_depth_le))
  · rename_i h
    set k := Nat.clog 2 n
    calc (bitonicNetwork n).depth
        ≤ k ^ 2 := bitonicNetwork_depth_le n
      _ = k * k := by ring
      _ ≤ (102 * 10 ^ 62) * k := by
        apply Nat.mul_le_mul_right
        calc k ≤ Nat.clog 2 1023 := Nat.clog_mono_right 2 (by omega)
          _ ≤ 102 * 10 ^ 62 := by decide +kernel

theorem exists_sorting_depth (n : ℕ) :
    ∃ d : ℕ, ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧ net.depth = d :=
  ⟨(bitonicNetwork n).depth, bitonicNetwork n, bitonicNetwork_sorts n, rfl⟩

/-- `D(n)`: the minimum depth among all sorting networks on `n` wires. -/
noncomputable def minimum (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_sorting_depth n)

theorem minimum_le {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) :
    minimum n ≤ net.depth := by
  classical
  exact Nat.find_min' _ ⟨net, hs, rfl⟩

theorem minimum_attained (n : ℕ) :
    ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧ net.depth = minimum n := by
  classical
  exact Nat.find_spec (exists_sorting_depth n)

/-- Improved all-arity bound on the actual minimum sorting-network depth.
Since `clog 2 n = log₂ n + O(1)`, this also improves the corresponding
mathematical limsup upper bound. The analytic limsup corollary is separate. -/
theorem minimum_depth_le (n : ℕ) :
    minimum n ≤ 102 * 10 ^ 62 * Nat.clog 2 n :=
  (minimum_le (upperNetwork n) (upperNetwork_sorts n)).trans (upperNetwork_depth_le n)

end SortingDepth
