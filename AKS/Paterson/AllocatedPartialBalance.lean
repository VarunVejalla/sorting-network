module

public import AKS.Paterson.AllocatedBalance
public import AKS.Paterson.PartialBoundary

/-! # Available rank cohorts at the clipped bottom boundary -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem allocated_partial_size {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hf : nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) ≤ 0) :
    (pl.regs b).card = subtreeTotal root k t b.l := by
  rw [ha.1 b, bagTarget_eq_scheduledBag root k t b.l hp, scheduledBag]
  have hz : scheduledSubtree fastParams (nativeWidth k b.l / 4)
      (fastParams.A ^ 2 * capacity fastParams root t b.l) = 0 := by
    unfold scheduledSubtree idealSubtree
    rw [max_eq_left hf]
    exact ceil32_of_nonpos (by rfl)
  rw [hz, Nat.mul_zero, Nat.sub_zero]
  rfl

theorem allocated_partial_half_upper {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hf : nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) ≤ 0) :
    (((pl.regs b).card / 2 : ℕ) : ℚ) ≤ capacity fastParams root t b.l / 2 + 16 := by
  have hcap := capacity_nonneg fastParams hr t b.l
  have hid := full_subtree_identity fastParams (nativeWidth k b.l)
    (capacity fastParams root t b.l)
  have hidle : idealSubtree fastParams (nativeWidth k b.l)
      (capacity fastParams root t b.l) ≤ capacity fastParams root t b.l := by
    apply max_le hcap
    linarith
  have hround := ceil32_mono hidle
  have htop := ceil32_lt_add hcap
  have heven : 2 ∣ (pl.regs b).card := by
    rw [ha.1 b]
    exact dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)
  have hhalf : (2 : ℚ) * ((pl.regs b).card / 2 : ℕ) = (pl.regs b).card := by
    exact_mod_cast Nat.mul_div_cancel' heven
  have hsame := allocated_partial_size pl ha b hp hf
  rw [hsame] at hhalf ⊢
  have hrQ : (subtreeTotal root k t b.l : ℚ) ≤
      ceil32 (capacity fastParams root t b.l) := by exact_mod_cast hround
  linarith

theorem allocated_partial_available {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.parent.l) % 2 = 0)
    (hf : nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l) ≤ 0) :
    (((pl.regs b.parent).card / 2 : ℕ) : ℚ) -
        ancestorReserve fastParams (capacity fastParams root t b.parent.l) / 2 -
        b.parent.strangers 1 w (pl.regs b.parent) ≤
      (((pl.regs b.parent).filter (fun i ↦ ¬ WrongSide b w i)).card : ℚ) := by
  have heven : 2 ∣ (pl.regs b.parent).card := by
    rw [ha.1 b.parent]
    exact dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)
  have hsize : ((pl.regs b.parent).card : ℚ) =
      2 * ((pl.regs b.parent).card / 2 : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' heven).symm
  have hcoherent : 2 * (((pl.regs b.parent).card / 2 : ℕ) : ℚ) + 2 * (0 : ℚ) =
      scheduledSubtree fastParams (nativeWidth k b.parent.l)
        (capacity fastParams root t b.parent.l) := by
    rw [← hsize, mul_zero, add_zero, allocated_partial_size pl ha b.parent hp hf]
    rfl
  have hn : (((univ.filter (fun i ↦ (b.sibling hb).Native i w)).card) : ℚ) =
      nativeWidth k b.parent.l / 2 := by
    rw [native_cohort_card _ w hw, size_eq_nativeWidth, Bag.sibling_level_eq]
    have hl : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
    rw [hl, nativeWidth_succ]
  have hdef := coherent_deficit hcoherent
  have hd : (((univ.filter (fun i ↦ (b.sibling hb).Native i w)).card) : ℚ) -
      (∅ : Finset (Fin (2 ^ k))).card ≤
      (((pl.regs b.parent).card / 2 : ℕ) : ℚ) +
        ancestorReserve fastParams (capacity fastParams root t b.parent.l) / 2 := by
    simpa only [hn, card_empty, Nat.cast_zero, sub_zero] using hdef
  have h := cohort_balance (pl.regs b.parent) ∅ (disjoint_empty_right _)
    (fun i ↦ (b.sibling hb).Native i w) (WrongSide b w)
    (fun i ↦ b.parent.Strange 1 i w)
    (fun i _ h ↦ wrongSide_cover b hb w i h) hsize hd
    (show (((∅ : Finset (Fin (2 ^ k))).filter
      (fun i ↦ ¬ (b.sibling hb).Native i w)).card : ℚ) ≤ 0 by simp)
    (show (((pl.regs b.parent).filter (fun i ↦ b.parent.Strange 1 i w)).card : ℚ) ≤
      b.parent.strangers 1 w (pl.regs b.parent) by rfl)
  simpa only [sub_zero] using h

theorem allocated_partial_fresh_budget {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.parent.l) % 2 = 0)
    (hf : nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l) ≤ 0) :
    let half := (pl.regs b.parent).card / 2
    let available := ((pl.regs b.parent).filter (fun i ↦ ¬ WrongSide b w i)).card
    (patersonDelta0 + refinementTailError) * b.parent.strangers 1 w (pl.regs b.parent) +
      ((half : ℚ) - availableCohort half available +
        patersonDelta0 * availableCohort half available) ≤
      fastParams.mu * capacity fastParams root (t + 1) b.l := by
  dsimp only
  have hcap := hc.trans (root_capacity_le_level hr t b.parent.l)
  have hhalf := allocated_partial_half_upper hr pl ha b.parent hp hf
  have hold : (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) ≤
      fastParams.mu * capacity fastParams root t b.parent.l := by
    simpa only [Nat.sub_self, pow_zero, mul_one] using hi b.parent 1 (by omega)
  have h := fast_partial_fresh hcap hhalf
    (show ancestorReserve fastParams (capacity fastParams root t b.parent.l) / 2 ≤
      ancestorReserve fastParams (capacity fastParams root t b.parent.l) / 2 + 32 by linarith)
    hold (allocated_partial_available pl ha w hw b hb hp hf)
  have hl : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
  rw [capacity_stage_succ, hl, capacity_level_succ]
  exact h

theorem allocated_partial_support {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t b.l)
    (hf : nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) ≤ 0)
    (hm : 0 < splitChildCard (pl.regs b).card (fringeTarget root k t b.l)) :
    fastParams.mu * capacity fastParams root t b.l ≤
        patersonAlpha0 * ((pl.regs b).card / 2 : ℕ) ∧
      fastParams.mu * capacity fastParams root t b.l ≤
        2 * patersonMu * ceil32 (capacity fastParams root t b.l / 2) := by
  have hroute := (target_source_cards (k := k) hc hp).1
  rw [ha.1 b] at hm
  rw [hroute] at hm
  have hnext : 0 < subtreeTotal root k (t + 1) (b.l + 1) := by omega
  have hcap : capacity fastParams root (t + 1) (b.l + 1) =
      fastParams.nu * fastParams.A * capacity fastParams root t b.l := by
    rw [capacity_stage_succ, capacity_level_succ]
    ring
  have hnextpos : 0 < nativeWidth k b.l / 2 -
      ancestorReserve fastParams (fastParams.nu * fastParams.A * capacity fastParams root t b.l) := by
    by_contra hn
    have hz : subtreeTotal root k (t + 1) (b.l + 1) = 0 := by
      unfold subtreeTotal scheduledSubtree idealSubtree
      rw [nativeWidth_succ, hcap, max_eq_left (by linarith)]
      exact ceil32_of_nonpos (by rfl)
    omega
  have heven : 2 ∣ (pl.regs b).card := by
    rw [ha.1 b]
    exact dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)
  have hhalf : (2 : ℚ) * ((pl.regs b).card / 2 : ℕ) = (pl.regs b).card := by
    exact_mod_cast Nat.mul_div_cancel' heven
  have hround := le_ceil32 (idealSubtree fastParams (nativeWidth k b.l)
    (capacity fastParams root t b.l))
  have ha' := le_max_right (0 : ℚ) (nativeWidth k b.l -
    ancestorReserve fastParams (capacity fastParams root t b.l))
  have hfringe := full_fringe_identity fastParams (nativeWidth k b.l)
    (capacity fastParams root t b.l)
  have hsize := allocated_partial_size pl ha b hp hf
  have hround' : nativeWidth k b.l - ancestorReserve fastParams (capacity fastParams root t b.l) ≤
      (pl.regs b).card := by
    rw [hsize]
    exact ha'.trans hround
  apply fast_partial_support hc
  · linarith
  · exact le_ceil32 _

end Paterson.Bags
