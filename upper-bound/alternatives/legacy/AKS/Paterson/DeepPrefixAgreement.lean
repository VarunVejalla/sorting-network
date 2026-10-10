module

public import AKS.Paterson.DeepPrefix

/-! # Actual and assigned deep prefixes agree outside the coarse error set -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem deep_prefix_agreement {root : ℚ} {k t L : ℕ} (hk : 6 ≤ k)
    (hL : L ≤ 6) (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k)) (q : ℕ)
    {i : Fin (2 ^ k)} (hi : i ∈ deepRegisters pl hk)
    (he : i ∉ deepErrors pl w L) :
    nativeBagIdx k L (w i).val < q ↔ assignedPrefix pl L q i := by
  obtain ⟨x, _, hx⟩ := mem_biUnion.mp hi
  obtain ⟨b, hb, _, hmem⟩ := mem_subregs_exists_bag' pl.collapse
    (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k) hx
  have hbl : 6 ≤ b.l := hb
  rw [pl.collapse_regs_of_pos b (by omega)] at hmem
  have heq : nativeBagIdx k L (w i).val = (b.ancestor (b.l - L)).x := by
    by_contra hwrong
    exact he (deepErrors_contains hL pl ha hp w b hbl hmem hwrong)
  simp only [assignedPrefix, (pl.mem_regs b i).mp hmem, heq]

theorem allocated_remaining_prefix_discrepancy {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (q : ℕ) (hq : q ≤ 2 ^ L) (R : ℕ)
    (hglobal : (univ.filter (fun i ↦ nativeBagIdx k L (w i).val < q)).card = R)
    (hC : (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 ≤ R) :
    (((upperRegisters pl (by omega)).filter
      (fun i ↦ nativeBagIdx k L (w i).val < q)).card : ℚ) -
        (R - (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 : ℕ) ≤
          (deepErrors pl w L).card ∧
    ((R - (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 : ℕ) : ℚ) -
      ((upperRegisters pl (by omega)).filter
        (fun i ↦ nativeBagIdx k L (w i).val < q)).card ≤
          (deepErrors pl w L).card := by
  apply remaining_prefix_discrepancy
    (upperRegisters pl (by omega)) (deepRegisters pl hk) (deepErrors pl w L)
    (deepRegisters_disjoint_upper hk pl ha hp).symm
    (upper_deep_complete hk pl ha hp)
    (fun i ↦ nativeBagIdx k L (w i).val < q) (assignedPrefix pl L q)
    (fun _ hi he ↦ deep_prefix_agreement hk hL pl ha hp w q hi he)
    hglobal (assigned_deep_prefix_card hr hk hc pl ha hp hL q hq) hC

end Paterson.Bags
