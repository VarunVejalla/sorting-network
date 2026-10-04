module

public import AKS.Separator.PatersonForest

/-! # Depth of the actual finite recursive forest -/

@[expose] public section

namespace Paterson.Bags

theorem forestNetwork_depth_le (k fuel : ℕ) (root : ℚ) (t : ℕ) (hr : 0 ≤ root)
    (phase : PhaseWindow root t) (pl : StoredPlacement k)
    (ha : AllocationInvariant root t pl) (hf : FuelCertificate root t k fuel) :
    (forestNetwork k fuel root t hr phase pl ha hf).depth ≤ 989 * fuel + 561 * k + 561 := by
  rw [forestNetwork]
  split_ifs with hk hs
  · exact (bitonicNetwork_depth_le_561 (Nat.pow_le_pow_right (by omega) hk)).trans (by omega)
  · dsimp only
    apply (depth_append _ _).trans
    have hfirst := root_sort_depth_le (upperRegisters pl (by omega))
      (allocated_upper_region_budget hr (by omega) (phase.min hr) hs.2 pl ha hs.1).le
    have hchild (s : Fin 2) := forestNetwork_depth_le (k - 1) fuel (childRoot root) (t + 1)
      (childRoot_nonneg hr) (phase.child hr hs.1) (scheduledChild hr (by omega) (phase.min hr) pl ha hs.1 s)
      (scheduledChild_allocation hr (by omega) (phase.min hr) pl ha hs.1 s) (hf.child (by omega))
    have hrest := parallelOnSets_depth_le (childRegisters pl (by omega))
      (childRegisters_card_allocation hr (by omega) (phase.min hr) pl ha hs.1) _
      (childRegisters_disjoint (by omega) pl ha hs.1) hchild
    have hsum := add_le_add hfirst hrest
    apply hsum.trans
    omega
  · dsimp only
    apply (depth_append _ _).trans
    have hpos : 1 ≤ fuel := hf.positive hr phase
    have hfnext : FuelCertificate root (t + 1) k (fuel - 1) :=
      FuelCertificate.compare (by simpa only [Nat.sub_add_cancel hpos] using hf)
    have hrest := forestNetwork_depth_le k (fuel - 1) root (t + 1) hr (phase.compare hr hs)
      (allocationStep root t pl) (allocationStep_preserves hr (by omega) (phase.min hr) pl ha) hfnext
    have hsum := add_le_add (scheduledCompare_depth_le hr pl ha) hrest
    apply hsum.trans
    omega
termination_by k + fuel
decreasing_by all_goals omega

theorem initial_phase_window {k : ℕ} (hk : 33 < k) : PhaseWindow (initialCapacity k) 0 := by
  have hpow : (2 : ℚ) ^ 34 ≤ (2 : ℚ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  norm_num [PhaseWindow, capacity, initialCapacity, fastParams] at hpow ⊢
  linarith

noncomputable def preliminaryNetwork (k : ℕ) : ComparatorNetwork (2 ^ k) :=
  if hk : k ≤ 33 then bitonicNetwork (2 ^ k)
  else forestNetwork k (idealStageCount k) (initialCapacity k) 0 (initialCapacity_nonneg k)
    (initial_phase_window (by omega)) (scheduledInitial k) (scheduledInitial_allocation k (by omega))
    (initial_fuel_certificate k)

theorem preliminaryNetwork_depth_le (k : ℕ) :
    (preliminaryNetwork k).depth ≤ 989 * idealStageCount k + 561 * k + 561 := by
  unfold preliminaryNetwork
  split_ifs with hk
  · exact (bitonicNetwork_depth_le_561 (Nat.pow_le_pow_right (by omega) hk)).trans (by omega)
  · exact forestNetwork_depth_le _ _ _ _ _ _ _ _ _

end Paterson.Bags
