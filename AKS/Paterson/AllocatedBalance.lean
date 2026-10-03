module

public import AKS.Paterson.RankCohorts
public import AKS.Paterson.AllocationBounds

/-! # Rank balance for actual full parent bags -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem allocated_full_cohort_balance {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.parent.l) % 2 = 0)
    (hf : 0 ≤ nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l)) :
    goodCohort ((pl.regs b.parent).card / 2) ≤
      ((pl.regs b.parent).filter (fun i ↦ ¬ WrongSide b w i)).card := by
  have hcap := hc.trans (root_capacity_le_level hr t b.parent.l)
  have hS : pl.regs b.parent ⊆ pl.collapse.regs b.parent := by
    change pl.regs b.parent ⊆
      if b.parent = Bag.root k then pl.regs b.parent ∪ pl.cold else pl.regs b.parent
    split_ifs
    · exact subset_union_left
    · exact Subset.rfl
  have hdis : Disjoint (pl.regs b.parent) (subregs pl.collapse (b.sibling hb)) := by
    apply Disjoint.mono_left hS
    apply regs_disjoint_subregs'
    rw [Bag.sibling_level_eq]
    change b.l - 1 < b.l
    omega
  have heven : 2 ∣ (pl.regs b.parent).card := by
    rw [ha.1 b.parent]
    exact dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)
  have hhalf := (allocated_full_half_bounds pl ha b.parent hp hcap hf).1.le
  have hcoherent : ((pl.regs b.parent).card : ℚ) +
      2 * (subregs pl.collapse (b.sibling hb)).card =
      scheduledSubtree fastParams (nativeWidth k b.parent.l)
        (capacity fastParams root t b.parent.l) := by
    exact_mod_cast allocated_parent_coherence hr hc pl ha b hb hp
  have hn : (((univ.filter (fun i ↦ (b.sibling hb).Native i w)).card) : ℚ) =
      nativeWidth k b.parent.l / 2 := by
    rw [native_cohort_card _ w hw, size_eq_nativeWidth, Bag.sibling_level_eq]
    have hl : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
    rw [hl, nativeWidth_succ]
  have hpar : (t + b.l) % 2 ≠ 0 := by
    change (t + (b.l - 1)) % 2 = 0 at hp
    omega
  have hintr := pl.subtree_intrusion_stored root hr t w
    (fun c _ hc ↦ allocated_inactive_empty pl ha c hc) hi (b.sibling hb)
    (by rw [Bag.sibling_level_eq]; exact hb)
    (by rw [Bag.sibling_level_eq]; exact hpar)
  have hlevel : (b.sibling hb).l = b.parent.l + 1 := by
    rw [Bag.sibling_level_eq]
    change b.l = b.l - 1 + 1
    omega
  rw [hlevel, capacity_level_succ] at hintr
  have hintr' : (((subregs pl.collapse (b.sibling hb)).filter
      (fun i ↦ ¬ (b.sibling hb).Native i w)).card : ℚ) ≤
      2 * fastParams.mu * fastParams.delta * fastParams.A ^ 2 /
        (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) *
          capacity fastParams root t b.parent.l := by
    convert hintr using 1 <;> ring
  have hold : (((pl.regs b.parent).filter (fun i ↦ b.parent.Strange 1 i w)).card : ℚ) ≤
      fastParams.mu * capacity fastParams root t b.parent.l := by
    simpa only [Bag.strangers, Nat.sub_self, pow_zero, mul_one] using hi b.parent 1 (by omega)
  exact coherent_cohort_balance _ _ hdis
    (fun i ↦ (b.sibling hb).Native i w) (WrongSide b w)
    (fun i ↦ b.parent.Strange 1 i w)
    (fun i _ h ↦ wrongSide_cover b hb w i h)
    hcap heven hhalf hcoherent hn hintr' hold

end Paterson.Bags
