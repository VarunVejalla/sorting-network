module

public import AKS.Separator.PatersonScheduled

/-! # Supported contracts for scheduled partial bags -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem supported_cast {n m f : ℕ} (h : n = m) (net : ComparatorNetwork n)
    {support err : ℝ} (hc : IsSupportedSeparator net f support err) :
    IsSupportedSeparator (h ▸ net) f support err := by cases h; exact hc

theorem allocated_nonempty_next_positive {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t b.l)
    (hm : 0 < splitChildCard (pl.regs b).card (fringeTarget root k t b.l)) :
    0 < nativeWidth k b.l / 2 -
      ancestorReserve fastParams (fastParams.nu * fastParams.A * capacity fastParams root t b.l) := by
  have hroute := (target_source_cards (k := k) hc hp).1
  rw [ha.1 b, hroute] at hm
  have hn : 0 < subtreeTotal root k (t + 1) (b.l + 1) := by omega
  have hcap : capacity fastParams root (t + 1) (b.l + 1) =
      fastParams.nu * fastParams.A * capacity fastParams root t b.l := by
    rw [capacity_stage_succ, capacity_level_succ]
    ring
  by_contra hneg
  have hz : subtreeTotal root k (t + 1) (b.l + 1) = 0 := by
    unfold subtreeTotal scheduledSubtree idealSubtree
    rw [nativeWidth_succ, hcap, max_eq_left (by linarith)]
    exact ceil32_of_nonpos (by rfl)
  omega

def partialSupport {root : ℚ} {k t : ℕ} (pl : StoredPlacement k) (b : Bag k) : ℚ :=
  fastParams.mu * capacity fastParams root t b.l / (pl.regs b).card

theorem partialSupport_mul {root : ℚ} {k t : ℕ} (pl : StoredPlacement k) (b : Bag k)
    (hn : 0 < (pl.regs b).card) :
    (partialSupport (root := root) (t := t) pl b : ℝ) * (pl.regs b).card =
      (fastParams.mu : ℝ) * (capacity fastParams root t b.l : ℝ) := by
  unfold partialSupport
  push_cast
  field_simp [show ((pl.regs b).card : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]

theorem scheduled_partial_supported {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k)
    (hp : (t + b.l) % 2 = 0)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t b.l)
    (hf : nativeWidth k b.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l) < 0)
    (hm : 0 < splitChildCard (pl.regs b).card (fringeTarget root k t b.l)) :
    IsSupportedSeparator (scheduledLocalNetwork hr pl ha b) (fringeTarget root k t b.l)
      (partialSupport (root := root) (t := t) pl b) (patersonDelta0 + refinementTailError) := by
  have hn : 0 < (pl.regs b).card := by unfold splitChildCard at hm; omega
  have he := Nat.mul_div_cancel' (allocated_even pl ha b)
  have hsup := allocated_partial_support pl ha b hp hc hf.le hm
  have hfirst : (partialSupport (root := root) (t := t) pl b : ℝ) *
      (2 * ((pl.regs b).card / 2) : ℕ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs b).card / 2 : ℕ) := by
    rw [he, partialSupport_mul pl b hn]
    exact_mod_cast hsup.1
  have hvirtual : (partialSupport (root := root) (t := t) pl b : ℝ) *
      (2 * ((pl.regs b).card / 2) : ℕ) ≤
      (2 * patersonMu : ℝ) * ceil32 (capacity fastParams root t b.l / 2) := by
    rw [he, partialSupport_mul pl b hn]
    exact_mod_cast hsup.2
  have h16 : 16 ∣ ceil32 (capacity fastParams root t b.l / 2) :=
    dvd_trans (by norm_num) (ceil32_dvd _)
  have hfit := allocated_partial_fits hr pl ha b hf.le
  have hsmall := partialNetwork_supported hfit h16 _ hfirst hvirtual
  have hfr := fast_virtual_fringe_coverage hc
    (allocated_nonempty_next_positive pl ha b hp hc hm).le
  rw [← fringeTarget_eq_scheduledFringe root k t b.l hp] at hfr
  unfold scheduledLocalNetwork
  rw [dif_neg (not_le.mpr hf)]
  apply supported_separator_mono_fringe _ hfr
  exact supported_cast he _ hsmall

end Paterson.Bags
