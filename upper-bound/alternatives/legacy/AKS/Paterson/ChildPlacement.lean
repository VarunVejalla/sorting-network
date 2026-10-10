module

public import AKS.Paterson.RootChildOwnership

/-! # Positional restriction to one smaller bag tree -/

@[expose] public section

namespace Paterson.Bags

open Finset

def restrictChild {k : ℕ} (pl : StoredPlacement k) (S : Finset (Fin (2 ^ k)))
    (hS : S.card = 2 ^ (k - 1)) : StoredPlacement (k - 1) where
  owner j := match pl.owner (S.orderEmbOfFin hS j) with
    | none => none
    | some b => if hb : 1 ≤ b.l then some (dropChildBag b hb) else none

def RespectsHalf {k : ℕ} (pl : StoredPlacement k) (S : Finset (Fin (2 ^ k))) (s : Fin 2) : Prop :=
  ∀ i ∈ S, ∀ b, i ∈ pl.regs b → 1 ≤ b.l ∧ b.x / 2 ^ (b.l - 1) = s.val

theorem restrictChild_mem_regs {k : ℕ} (hk : 1 ≤ k) (pl : StoredPlacement k)
    (S : Finset (Fin (2 ^ k))) (hS : S.card = 2 ^ (k - 1)) (s : Fin 2)
    (hs : RespectsHalf pl S s) (b : Bag (k - 1)) (j : Fin (2 ^ (k - 1))) :
    j ∈ (restrictChild pl S hS).regs b ↔ S.orderEmbOfFin hS j ∈ pl.regs (liftChildBag hk s b) := by
  simp only [StoredPlacement.mem_regs, restrictChild]
  cases ho : pl.owner (S.orderEmbOfFin hS j) with
  | none => simp
  | some c =>
    have hc := hs _ (orderEmbOfFin_mem S hS j) c ((pl.mem_regs c _).mpr ho)
    dsimp only
    rw [dif_pos hc.1]
    simp only [Option.some.injEq]
    constructor
    · intro he
      have hl := congrArg (liftChildBag hk s) he
      rw [lift_dropChildBag hk s c hc.1 hc.2] at hl
      exact hl
    · intro he
      subst c
      exact drop_liftChildBag hk s b

theorem restrictChild_regs_card {k : ℕ} (hk : 1 ≤ k) (pl : StoredPlacement k)
    (S : Finset (Fin (2 ^ k))) (hS : S.card = 2 ^ (k - 1)) (s : Fin 2)
    (hs : RespectsHalf pl S s) (b : Bag (k - 1))
    (hsub : pl.regs (liftChildBag hk s b) ⊆ S) :
    ((restrictChild pl S hS).regs b).card = (pl.regs (liftChildBag hk s b)).card := by
  apply card_bij (fun j _ ↦ S.orderEmbOfFin hS j)
  · intro j hj
    exact (restrictChild_mem_regs hk pl S hS s hs b j).mp hj
  · intro j _ l _ hjl
    exact (S.orderEmbOfFin hS).injective hjl
  · intro i hi
    have hir : i ∈ Set.range (S.orderEmbOfFin hS) := by rw [range_orderEmbOfFin]; exact hsub hi
    obtain ⟨j, rfl⟩ := hir
    exact ⟨j, (restrictChild_mem_regs hk pl S hS s hs b j).mpr hi, rfl⟩

def scheduledChild {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) : StoredPlacement (k - 1) :=
  restrictChild (allocatedRebuild root t pl (by omega)) (childRegisters pl hk s)
    (childRegisters_card_allocation hr hk hc pl ha hp s)

theorem allocatedRebuild_nonroot_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (b : Bag k) (hb : 1 ≤ b.l) :
    ((allocatedRebuild root t pl (by omega)).regs b).card = bagTarget root k t b.l := by
  by_cases hb6 : 6 ≤ b.l
  · rw [allocatedRebuild, rebuildUpper_deep_regs hk pl ha hp _ _ b hb6, ha.1 b]
  · rw [allocatedRebuild_low_cards hr hk hc pl ha hp b (by omega)]
    split_ifs with h
    · rfl
    · have hinactive : (t + b.l) % 2 ≠ 0 := by omega
      simp only [bagTarget, if_neg hinactive]

theorem scheduledChild_bag_cards {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) (b : Bag (k - 1)) :
    ((scheduledChild hr hk hc pl ha hp s).regs b).card =
      bagTarget (childRoot root) (k - 1) (t + 1) b.l := by
  unfold scheduledChild
  rw [restrictChild_regs_card (by omega) _ _ _ s
    (fun i hi b hb ↦ rebuilt_child_owner_half hr hk hc pl ha hp s hi b hb)
    b (rebuilt_regs_subset_child hr hk hc pl ha hp (liftChildBag (by omega) s b)
      (by change 1 ≤ b.l + 1; omega) s (liftChildBag_half (by omega) s b)),
    allocatedRebuild_nonroot_card hr hk hc pl ha hp (liftChildBag (by omega) s b)
      (by change 1 ≤ b.l + 1; omega), child_bagTarget root (by omega)]
  rfl

end Paterson.Bags
