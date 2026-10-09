module
-- Chvátal §4 children-send helpers (Lemmas 4.3-4.4 children terms)

public import AKS.Chvatal.StageKernel
public import AKS.Chvatal.Scheduler
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

open Finset

/-- Stranger count on a `biUnion` is at most the sum of the counts. -/
theorem strangers_biUnion_le (p : ScheduleParams) (d : Nat) (b : KBag p.br d) (j : Nat)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) (f : Fin p.br → Finset (Fin (p.br ^ d))) :
    (b.strangers j perm ((univ : Finset (Fin p.br)).biUnion f) (br_ge_one p) : Nat) ≤
      ∑ i : Fin p.br, b.strangers j perm (f i) (br_ge_one p) := by
  classical
  simp only [KBag.strangers, filter_biUnion]
  exact card_biUnion_le

/-- On any set, order-`j` outsiders at a parent equal order-`(j+1)` at a child. -/
theorem strangers_child_eq (p : ScheduleParams) (d : Nat) (b : KBag p.br d) (hbd : b.l < d)
    (j : Nat) (hj : 1 ≤ j) (childIdx : Fin p.br) (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (S : Finset (Fin (p.br ^ d))) (hbr : 1 ≤ p.br := br_ge_one p) :
    b.strangers j perm S hbr =
      (b.child childIdx.val childIdx.isLt hbd).strangers (j + 1) perm S hbr := by
  have h := KBag.strangers_parent_eq (b.child childIdx.val childIdx.isLt hbd) j hj
    (show 1 ≤ b.l + 1 by omega) perm S hbr
  rwa [KBag.child_parent b childIdx.val childIdx.isLt hbd hbr] at h

/-- Scale `k · μ · δ^{r+1} · A² · c` into the `StageKernel` children-send form. -/
theorem childrenR_scale (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (r : Nat) (hr1 : 1 ≤ r) :
    (p.br : Rat) * (ip.mu * ip.delta ^ (r + 1) * (p.A * (p.A * c))) =
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)) := by
  have hnu : p.nu ≠ 0 := ne_of_gt p.hnu_pos
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp [hnu]
  ring

end Chvatal
