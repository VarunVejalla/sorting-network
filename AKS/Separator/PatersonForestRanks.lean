module

public import AKS.Separator.PatersonForestDepth
public import AKS.Paterson.TerminalRanks

/-! # The finite forest has one fixed output rank arrangement -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem forestNetwork_independent (k fuel : ℕ) (root : ℚ) (t : ℕ) (hr : 0 ≤ root)
    (phase : PhaseWindow root t) (pl : StoredPlacement k)
    (ha : AllocationInvariant root t pl) (hf : FuelCertificate root t k fuel)
    (w v : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) (hv : Function.Injective v)
    (hiw : Invariant fastParams (fun b ↦ capacity fastParams root t b.l) pl.regs w)
    (hiv : Invariant fastParams (fun b ↦ capacity fastParams root t b.l) pl.regs v) :
    (forestNetwork k fuel root t hr phase pl ha hf).exec w =
      (forestNetwork k fuel root t hr phase pl ha hf).exec v := by
  conv_lhs => rw [forestNetwork]
  conv_rhs => rw [forestNetwork]
  split_ifs with hk hs
  · rw [sorted_network_rank_identity _ (bitonicNetwork_sorts _) w hw,
      sorted_network_rank_identity _ (bitonicNetwork_sorts _) v hv]
  · dsimp only
    rw [ComparatorNetwork.exec_append, ComparatorNetwork.exec_append]
    let hk6 : 6 ≤ k := by omega
    let hc := phase.min hr
    let U := upperRegisters pl (by omega)
    let first := (bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)
    let S := childRegisters pl hk6
    let sz := childRegisters_card_allocation hr hk6 hc pl ha hs.1
    let children := fun s : Fin 2 ↦ forestNetwork (k - 1) fuel (childRoot root) (t + 1)
      (childRoot_nonneg hr) (phase.child hr hs.1) (scheduledChild hr hk6 hc pl ha hs.1 s)
      (scheduledChild_allocation hr hk6 hc pl ha hs.1 s) (hf.child (by omega))
    change (parallelOnSets S sz children).exec (first.exec w) =
      (parallelOnSets S sz children).exec (first.exec v)
    funext i
    have hcover : ∃ s : Fin 2, i ∈ S s := by
      have hi : i ∈ childRegisters pl hk6 0 ∪ childRegisters pl hk6 1 := by
        rw [childRegisters_cover hr hk6 hc pl ha hs.1]; exact mem_univ _
      rcases mem_union.mp hi with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    obtain ⟨s, hiS⟩ := hcover
    have hir : i ∈ Set.range ((S s).orderEmbOfFin (sz s)) := by rw [range_orderEmbOfFin]; exact hiS
    obtain ⟨j, rfl⟩ := hir
    have hpw := childRegisters_pure hr hk6 hc hs.2 pl ha hs.1 w hw hiw s
    have hpv := childRegisters_pure hr hk6 hc hs.2 pl ha hs.1 v hv hiv s
    let cw := childRankView (S s) (sz s) (first.exec w)
    let cv := childRankView (S s) (sz s) (first.exec v)
    have hchild := forestNetwork_independent (k - 1) fuel (childRoot root) (t + 1)
      (childRoot_nonneg hr) (phase.child hr hs.1) (scheduledChild hr hk6 hc pl ha hs.1 s)
      (scheduledChild_allocation hr hk6 hc pl ha hs.1 s) (hf.child (by omega)) cw cv
      (childRankView_injective (by omega) _ _ s _ (ComparatorNetwork.exec_injective first hw) hpw)
      (childRankView_injective (by omega) _ _ s _ (ComparatorNetwork.exec_injective first hv) hpv)
      (scheduledChild_invariant hr hk6 hc hs.2 pl ha hs.1 w hw hiw s)
      (scheduledChild_invariant hr hk6 hc hs.2 pl ha hs.1 v hv hiv s)
    have hvieww : first.exec w ∘ (S s).orderEmbOfFin (sz s) = liftChildRank (by omega) s ∘ cw := by
      funext a
      exact (lift_dropChildRank (by omega) s _ (hpw _ (orderEmbOfFin_mem _ _ a))).symm
    have hviewv : first.exec v ∘ (S s).orderEmbOfFin (sz s) = liftChildRank (by omega) s ∘ cv := by
      funext a
      exact (lift_dropChildRank (by omega) s _ (hpv _ (orderEmbOfFin_mem _ _ a))).symm
    rw [parallelOnSets_exec_inside S sz children (childRegisters_disjoint hk6 pl ha hs.1),
      parallelOnSets_exec_inside S sz children (childRegisters_disjoint hk6 pl ha hs.1),
      hvieww, hviewv, ComparatorNetwork.exec_comp_mono _ (liftChildRank (by omega) s).monotone,
      ComparatorNetwork.exec_comp_mono _ (liftChildRank (by omega) s).monotone]
    exact congrFun (congrArg (fun f ↦ liftChildRank (by omega) s ∘ f) hchild) j
  · dsimp only
    rw [ComparatorNetwork.exec_append, ComparatorNetwork.exec_append]
    have hpos : 1 ≤ fuel := hf.positive hr phase
    have hfnext : FuelCertificate root (t + 1) k (fuel - 1) :=
      FuelCertificate.compare (by simpa only [Nat.sub_add_cancel hpos] using hf)
    exact forestNetwork_independent k (fuel - 1) root (t + 1) hr (phase.compare hr hs)
      (allocationStep root t pl) (allocationStep_preserves hr (by omega) (phase.min hr) pl ha) hfnext
      ((scheduledCompare hr pl ha).exec w) ((scheduledCompare hr pl ha).exec v)
      (ComparatorNetwork.exec_injective _ hw) (ComparatorNetwork.exec_injective _ hv)
      (scheduledCompare_preserves hr (by omega) (phase.min hr) pl ha w hw hiw)
      (scheduledCompare_preserves hr (by omega) (phase.min hr) pl ha v hv hiv)
termination_by k + fuel
decreasing_by all_goals omega

theorem preliminaryNetwork_independent (k : ℕ) (w v : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w) (hv : Function.Injective v) :
    (preliminaryNetwork k).exec w = (preliminaryNetwork k).exec v := by
  unfold preliminaryNetwork
  split_ifs with hk
  · rw [sorted_network_rank_identity _ (bitonicNetwork_sorts _) w hw,
      sorted_network_rank_identity _ (bitonicNetwork_sorts _) v hv]
  · exact forestNetwork_independent _ _ _ _ _ _ _ _ _ w v hw hv
      (scheduledInitial_strangerInvariant k w) (scheduledInitial_strangerInvariant k v)

end Paterson.Bags
