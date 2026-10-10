module

public import AKS.Paterson.Rounding
public import AKS.Bags.Filter

/-! # Single-stage preservation of Paterson's interior stranger invariant

This theorem concerns a real register flow on the existing binary bag tree.
Its hypotheses separate the tasks that must be supplied by the separator and
the scheduler: bag-local comparison, subset routing, filtering of the old
stranger cohort, and the first-stranger input-balance estimate. It does not
assume the invariant at the destination bag.

Source: Paterson (1990), Section 4, inequalities (4) and (5).
-/

@[expose] public section

namespace Paterson.Bags

open Finset

def Invariant {k : ℕ} (p : Params) (cap : Bag k → ℚ)
    (regs : Bag k → Finset (Fin (2 ^ k))) (w : Fin (2 ^ k) → Fin (2 ^ k)) : Prop :=
  ∀ b j, 1 ≤ j → (b.strangers j w (regs b) : ℚ) ≤
    p.mu * p.delta ^ (j - 1) * cap b

/-- A comparison stage local to each bag preserves every old stranger count
inside that bag, even though it can change which registers hold strangers. -/
theorem local_strangers_preserved {k : ℕ}
    (regs : Bag k → Finset (Fin (2 ^ k))) (net : ComparatorNetwork (2 ^ k))
    (hlocal : ∀ b c, c ∈ net.comparators →
      (c.i ∈ regs b ∧ c.j ∈ regs b) ∨ (c.i ∉ regs b ∧ c.j ∉ regs b))
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (b : Bag k) (j : ℕ) :
    b.strangers j (net.exec w) (regs b) = b.strangers j w (regs b) := by
  have h := network_card_filter net w (regs b)
    (fun v ↦ j = 0 ∨ nativeBagIdx k (b.ancestor (j - 1)).l v.val ≠
      (b.ancestor (j - 1)).x) (hlocal b)
  exact h

theorem tail_arithmetic (p : Params) {cap : ℚ} (hc : 0 ≤ cap)
    {j : ℕ} (hj : 2 ≤ j) :
    2 * p.mu * p.delta ^ j * (p.A * cap) +
      p.tailError * (p.mu * p.delta ^ (j - 2) * (cap / p.A)) ≤
    p.mu * p.delta ^ (j - 1) * (p.nu * cap) := by
  have hA : 0 < p.A := by linarith [p.A_gt_one]
  have hd : 0 < p.delta := p.delta_pos
  have hpow₁ : p.delta ^ j = p.delta ^ (j - 2) * p.delta ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpow₂ : p.delta ^ (j - 1) = p.delta ^ (j - 2) * p.delta := by
    rw [← pow_succ]
    congr 1
    omega
  have hbase : 2 * p.A * p.delta ^ 2 + p.tailError / p.A ≤ p.nu * p.delta := by
    have h := p.tail.le
    convert (div_le_div_of_nonneg_right h hA.le) using 1 <;> field_simp
  have hw : 0 ≤ p.mu * p.delta ^ (j - 2) * cap :=
    mul_nonneg (mul_nonneg p.mu_pos.le (pow_nonneg hd.le _)) hc
  have h := mul_le_mul_of_nonneg_left hbase hw
  rw [hpow₁, hpow₂]
  convert h using 1 <;> ring

theorem first_arithmetic (p : Params) {cap : ℚ} (hc : p.minCapacity ≤ cap) :
    2 * p.mu * p.delta * (p.A * cap) + p.freshCost * cap +
      p.roundingAllowance ≤ p.mu * (p.nu * cap) := by
  have hcap : 0 < cap := p.minCapacity_pos.trans_le hc
  have hallow : p.roundingAllowance ≤
      (p.roundingAllowance / p.minCapacity) * cap := by
    have hmul := mul_le_mul_of_nonneg_left hc
      (div_nonneg p.roundingAllowance_nonneg p.minCapacity_pos.le)
    rw [div_mul_cancel₀ _ (ne_of_gt p.minCapacity_pos)] at hmul
    exact hmul
  have h := mul_le_mul_of_nonneg_right p.firstRounded hcap.le
  nlinarith

/-- One interior destination bag receives only the two child fringes and a
filtered middle part from its parent. The old invariant and the local source
bounds imply the full invariant at that destination for every `j ≥ 1`.

`hfirst` is the first-stranger bridge to be proved from rank balance and the
large-cohort halver, not an assumption about the new whole bag. Root and
partial-level transitions are separate obligations. -/
theorem interior_step {k : ℕ} (p : Params)
    (cap : Bag k → ℚ) (regs : Bag k → Finset (Fin (2 ^ k)))
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (net : ComparatorNetwork (2 ^ k))
    (b : Bag k) (hl : 1 ≤ b.l) (hk : b.l < k)
    (fromLeft fromRight fromParent : Finset (Fin (2 ^ k)))
    (hleft : fromLeft ⊆ regs (b.left hk))
    (hright : fromRight ⊆ regs (b.right hk))
    (hlocal : ∀ c d, d ∈ net.comparators →
      (d.i ∈ regs c ∧ d.j ∈ regs c) ∨ (d.i ∉ regs c ∧ d.j ∉ regs c))
    (hinv : Invariant p cap regs w)
    (hcap : p.minCapacity ≤ cap b)
    (hcapLeft : cap (b.left hk) = p.A * cap b)
    (hcapRight : cap (b.right hk) = p.A * cap b)
    (hcapParent : cap b.parent = cap b / p.A)
    (hfilter : ∀ j, 1 ≤ j →
      (b.parent.strangers j (net.exec w) fromParent : ℚ) ≤
        p.tailError * b.parent.strangers j (net.exec w) (regs b.parent))
    (hfirst : (b.strangers 1 (net.exec w) fromParent : ℚ) ≤
      p.freshCost * cap b + p.roundingAllowance) :
    ∀ j, 1 ≤ j →
      (b.strangers j (net.exec w) (fromLeft ∪ fromRight ∪ fromParent) : ℚ) ≤
        p.mu * p.delta ^ (j - 1) * (p.nu * cap b) := by
  intro j hj
  have hchildren :
      (b.strangers j (net.exec w) (fromLeft ∪ fromRight) : ℚ) ≤
        2 * p.mu * p.delta ^ j * (p.A * cap b) := by
    have hL : (b.strangers j (net.exec w) fromLeft : ℚ) ≤
        p.mu * p.delta ^ j * (p.A * cap b) := by
      conv_lhs => rw [← Bag.left_parent_eq b hk,
        Bag.strangers_parent_eq (b.left hk) j hj (by show 1 ≤ b.l + 1; omega)]
      calc
        _ ≤ ((b.left hk).strangers (j + 1) (net.exec w)
            (regs (b.left hk)) : ℚ) := by
          exact_mod_cast Bag.strangers_mono (b.left hk) (j + 1) (net.exec w) hleft
        _ = ((b.left hk).strangers (j + 1) w (regs (b.left hk)) : ℚ) := by
          rw [local_strangers_preserved regs net hlocal]
        _ ≤ p.mu * p.delta ^ j * (p.A * cap b) := by
          simpa only [Nat.add_sub_cancel, hcapLeft] using hinv (b.left hk) (j + 1) (by omega)
    have hR : (b.strangers j (net.exec w) fromRight : ℚ) ≤
        p.mu * p.delta ^ j * (p.A * cap b) := by
      conv_lhs => rw [← Bag.right_parent_eq b hk,
        Bag.strangers_parent_eq (b.right hk) j hj (by show 1 ≤ b.l + 1; omega)]
      calc
        _ ≤ ((b.right hk).strangers (j + 1) (net.exec w)
            (regs (b.right hk)) : ℚ) := by
          exact_mod_cast Bag.strangers_mono (b.right hk) (j + 1) (net.exec w) hright
        _ = ((b.right hk).strangers (j + 1) w (regs (b.right hk)) : ℚ) := by
          rw [local_strangers_preserved regs net hlocal]
        _ ≤ p.mu * p.delta ^ j * (p.A * cap b) := by
          simpa only [Nat.add_sub_cancel, hcapRight] using hinv (b.right hk) (j + 1) (by omega)
    have hu : (b.strangers j (net.exec w) (fromLeft ∪ fromRight) : ℚ) ≤
        (b.strangers j (net.exec w) fromLeft : ℚ) +
        (b.strangers j (net.exec w) fromRight : ℚ) := by
      exact_mod_cast Bag.strangers_union_le b j (net.exec w) fromLeft fromRight
    linarith
  have hunion :
      (b.strangers j (net.exec w) (fromLeft ∪ fromRight ∪ fromParent) : ℚ) ≤
      (b.strangers j (net.exec w) (fromLeft ∪ fromRight) : ℚ) +
      (b.strangers j (net.exec w) fromParent : ℚ) := by
    exact_mod_cast Bag.strangers_union_le b j (net.exec w) (fromLeft ∪ fromRight) fromParent
  by_cases hj2 : 2 ≤ j
  · have hparent : (b.strangers j (net.exec w) fromParent : ℚ) ≤
        p.tailError * (p.mu * p.delta ^ (j - 2) * (cap b / p.A)) := by
      have hshift := Bag.strangers_parent_eq b (j - 1) (by omega) hl (net.exec w) fromParent
      rw [show j - 1 + 1 = j from by omega] at hshift
      rw [← hshift]
      have h := hfilter (j - 1) (by omega)
      rw [local_strangers_preserved regs net hlocal] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ p.tailError_nonneg
      simpa only [hcapParent, show j - 1 - 1 = j - 2 from by omega] using
        hinv b.parent (j - 1) (by omega)
    exact (hunion.trans (add_le_add hchildren hparent)).trans
      (tail_arithmetic p (p.minCapacity_pos.le.trans hcap) hj2)
  · have hj1 : j = 1 := by omega
    subst j
    simp only [Nat.sub_self, pow_zero, mul_one, pow_one] at hchildren ⊢
    exact (hunion.trans (add_le_add hchildren hfirst)).trans
      (by simpa only [add_assoc] using first_arithmetic p hcap)

end Paterson.Bags
