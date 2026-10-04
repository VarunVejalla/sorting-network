module

public import AKS.Paterson.ChildRanks
public import AKS.Paterson.AllocationFromCards

/-! # Allocation and rank invariants for the smaller child trees -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem scheduledChild_allocation {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) : AllocationInvariant (childRoot root) (t + 1) (scheduledChild hr hk hc pl ha hp s) := by
  apply allocationInvariant_of_bag_cards (childRoot_nonneg hr) (by omega)
  · rw [child_capacity]
    exact hc.trans (root_capacity_le_level hr t 1)
  · exact scheduledChild_bag_cards hr hk hc pl ha hp s

def childRankView {k : ℕ} (S : Finset (Fin (2 ^ k))) (hS : S.card = 2 ^ (k - 1))
    (w : Fin (2 ^ k) → Fin (2 ^ k)) : Fin (2 ^ (k - 1)) → Fin (2 ^ (k - 1)) :=
  dropChildRank ∘ w ∘ S.orderEmbOfFin hS

theorem childRankView_injective {k : ℕ} (hk : 1 ≤ k)
    (S : Finset (Fin (2 ^ k))) (hS : S.card = 2 ^ (k - 1)) (s : Fin 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hs : ∀ i ∈ S, nativeBagIdx k 1 (w i).val = s.val) :
    Function.Injective (childRankView S hS w) := by
  intro a b hab
  have he := congrArg (liftChildRank hk s) hab
  dsimp only [childRankView, Function.comp_apply] at he
  rw [lift_dropChildRank hk s _ (hs _ (orderEmbOfFin_mem S hS a)),
    lift_dropChildRank hk s _ (hs _ (orderEmbOfFin_mem S hS b))] at he
  exact (S.orderEmbOfFin hS).injective (hw he)

theorem restrictChild_strangers {k : ℕ} (hk : 1 ≤ k) (pl : StoredPlacement k)
    (S : Finset (Fin (2 ^ k))) (hS : S.card = 2 ^ (k - 1)) (s : Fin 2)
    (hs : RespectsHalf pl S s) (b : Bag (k - 1))
    (hsub : pl.regs (liftChildBag hk s b) ⊆ S)
    (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : ∀ i ∈ S, nativeBagIdx k 1 (w i).val = s.val)
    {j : ℕ} (hj : 1 ≤ j) (hjb : j ≤ b.l + 1) :
    b.strangers j (childRankView S hS w) ((restrictChild pl S hS).regs b) =
      (liftChildBag hk s b).strangers j w (pl.regs (liftChildBag hk s b)) := by
  have hstr (a : Fin (2 ^ (k - 1))) :
      b.Strange j a (childRankView S hS w) ↔
        (liftChildBag hk s b).Strange j (S.orderEmbOfFin hS a) w := by
    have he := lift_dropChildRank hk s (w (S.orderEmbOfFin hS a))
      (hw _ (orderEmbOfFin_mem S hS a))
    have h := (child_strange_iff hk s b hj hjb (dropChildRank (w (S.orderEmbOfFin hS a)))).symm
    simpa only [Bag.Strange, Bag.Native, childRankView, Function.comp_apply, he] using h
  unfold Bag.strangers
  apply card_bij (fun a _ ↦ S.orderEmbOfFin hS a)
  · intro a ha
    obtain ⟨haB, haJ⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨(restrictChild_mem_regs hk pl S hS s hs b a).mp haB,
      (hstr a).mp haJ⟩
  · intro a _ d _ had
    exact (S.orderEmbOfFin hS).injective had
  · intro i hi
    obtain ⟨hiB, hiJ⟩ := mem_filter.mp hi
    have hir : i ∈ Set.range (S.orderEmbOfFin hS) := by rw [range_orderEmbOfFin]; exact hsub hiB
    obtain ⟨a, rfl⟩ := hir
    exact ⟨a, mem_filter.mpr ⟨(restrictChild_mem_regs hk pl S hS s hs b a).mpr hiB,
      (hstr a).mpr hiJ⟩, rfl⟩

theorem scheduledChild_invariant {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w) (s : Fin 2) :
    let U := upperRegisters pl (by omega)
    let v := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    Invariant fastParams (fun b ↦ capacity fastParams (childRoot root) (t + 1) b.l)
      (scheduledChild hr hk hc pl ha hp s).regs
      (childRankView (childRegisters pl hk s) (childRegisters_card_allocation hr hk hc pl ha hp s) v) := by
  dsimp only
  intro b j hj
  by_cases hjb : b.l < j
  · rw [strangers_above_root_zero b hjb, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams (childRoot_nonneg hr) _ _)
  · unfold scheduledChild
    rw [restrictChild_strangers (by omega) _ _ _ s
      (fun i hi b hb ↦ rebuilt_child_owner_half hr hk hc pl ha hp s hi b hb) b
      (rebuilt_regs_subset_child hr hk hc pl ha hp (liftChildBag (by omega) s b)
        (by change 1 ≤ b.l + 1; omega) s (liftChildBag_half (by omega) s b)) _
      (childRegisters_pure hr hk hc hceil pl ha hp w hw hi s) hj (by omega)]
    dsimp only
    rw [child_capacity]
    exact allocatedRebuild_preserves hr hk hc pl ha hp w hw hi
      (liftChildBag (by omega) s b) j hj

end Paterson.Bags
