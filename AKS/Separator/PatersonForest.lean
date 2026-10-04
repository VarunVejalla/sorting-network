module

public import AKS.Paterson.ForestPhase
public import AKS.Paterson.ParallelSets

/-! # Finite recursive Paterson forest network

The network chooses operations from the size, allocation, and rational clock.
Comparison fuel and the number of root levels give a decreasing measure.
-/

@[expose] public section

namespace Paterson.Bags

noncomputable def forestNetwork (k fuel : ℕ) (root : ℚ) (t : ℕ) (hr : 0 ≤ root)
    (phase : PhaseWindow root t) (pl : StoredPlacement k)
    (ha : AllocationInvariant root t pl) (hf : FuelCertificate root t k fuel) :
    ComparatorNetwork (2 ^ k) :=
  if hk : k ≤ 33 then bitonicNetwork (2 ^ k)
  else if hs : t % 2 = 0 ∧ capacity fastParams root t 0 ≤ rootCeiling then
    let hk6 : 6 ≤ k := by omega
    let hc := phase.min hr
    let U := upperRegisters pl (by omega)
    let first := (bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)
    let children := fun s : Fin 2 ↦ forestNetwork (k - 1) fuel (childRoot root) (t + 1)
      (childRoot_nonneg hr) (phase.child hr hs.1) (scheduledChild hr hk6 hc pl ha hs.1 s)
      (scheduledChild_allocation hr hk6 hc pl ha hs.1 s) (hf.child (by omega))
    let rest := parallelOnSets (childRegisters pl hk6)
      (childRegisters_card_allocation hr hk6 hc pl ha hs.1) children
    ⟨first.comparators ++ rest.comparators⟩
  else
    let hpos : 1 ≤ fuel := hf.positive hr phase
    let hc := phase.min hr
    let first := scheduledCompare hr pl ha
    let next := allocationStep root t pl
    let hfnext : FuelCertificate root (t + 1) k (fuel - 1) :=
      FuelCertificate.compare (by simpa only [Nat.sub_add_cancel hpos] using hf)
    let rest := forestNetwork k (fuel - 1) root (t + 1) hr (phase.compare hr hs) next
      (allocationStep_preserves hr (by omega) hc pl ha) hfnext
    ⟨first.comparators ++ rest.comparators⟩
termination_by k + fuel
decreasing_by all_goals omega

end Paterson.Bags
