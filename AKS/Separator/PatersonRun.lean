module

public import AKS.Paterson.ScheduledInvariant

/-! # Actual repeated mixed stages before a root split

The stage-count argument here counts comparisons in a concrete network.
Forest splitting and final sortedness remain separate obligations.
-/

@[expose] public section

namespace Paterson.Bags

def RootWindow (k t : ℕ) : Prop :=
  ∀ s, s < t → fastParams.minCapacity ≤ capacity fastParams (initialCapacity k) s 0

theorem RootWindow.prefix {k t : ℕ} (hc : RootWindow k (t + 1)) : RootWindow k t :=
  fun s hs ↦ hc s (by omega)

noncomputable def comparisonRun (k : ℕ) (hk : 5 ≤ k) :
    (t : ℕ) → RootWindow k t → ComparatorNetwork (2 ^ k)
  | 0, _ => ⟨[]⟩
  | t + 1, hc =>
      let old := comparisonRun k hk t hc.prefix
      let step := scheduledCompare (initialCapacity_nonneg k) (allocationRun k t)
        (allocationRun_invariant k t hk hc.prefix)
      ⟨old.comparators ++ step.comparators⟩

theorem comparisonRun_depth_le (k : ℕ) (hk : 5 ≤ k) (t : ℕ) (hc : RootWindow k t) :
    (comparisonRun k hk t hc).depth ≤ 989 * t := by
  induction t with
  | zero => simp [comparisonRun, ComparatorNetwork.depth]
  | succ t ih =>
    change (⟨(comparisonRun k hk t hc.prefix).comparators ++
      (scheduledCompare (initialCapacity_nonneg k) (allocationRun k t)
        (allocationRun_invariant k t hk hc.prefix)).comparators⟩ : ComparatorNetwork (2 ^ k)).depth ≤ _
    apply (depth_append _ _).trans
    have h := add_le_add (ih hc.prefix)
      (scheduledCompare_depth_le (initialCapacity_nonneg k) (allocationRun k t)
        (allocationRun_invariant k t hk hc.prefix))
    convert h using 1 <;> omega

theorem comparisonRun_invariant (k : ℕ) (hk : 5 ≤ k) (t : ℕ) (hc : RootWindow k t)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) :
    Invariant fastParams (fun b ↦ capacity fastParams (initialCapacity k) t b.l)
      (allocationRun k t).regs ((comparisonRun k hk t hc).exec w) := by
  induction t with
  | zero => simpa [comparisonRun, allocationRun, ComparatorNetwork.exec] using
      scheduledInitial_strangerInvariant k w
  | succ t ih =>
    change Invariant fastParams _ (allocationStep (initialCapacity k) t (allocationRun k t)).regs
      ((⟨(comparisonRun k hk t hc.prefix).comparators ++
        (scheduledCompare (initialCapacity_nonneg k) (allocationRun k t)
          (allocationRun_invariant k t hk hc.prefix)).comparators⟩ : ComparatorNetwork (2 ^ k)).exec w)
    rw [ComparatorNetwork.exec_append]
    exact scheduledCompare_preserves (initialCapacity_nonneg k) hk (hc t (by omega))
      (allocationRun k t) (allocationRun_invariant k t hk hc.prefix)
      ((comparisonRun k hk t hc.prefix).exec w)
      (ComparatorNetwork.exec_injective _ hw) (ih hc.prefix)

end Paterson.Bags
