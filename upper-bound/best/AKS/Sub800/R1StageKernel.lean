import AKS.Sub800.R1FringeSend
import AKS.Sub800.R1Lemma41

/-! # The real stage kernel at `k = 16` (W1, step 10)

Children part of Lemma 4.3′ (`hFromChildren0_of_subset`, `hFromChildrenR_of_subset`) and the
assembly `realStageKernel`: for a flow table `F`, node networks `nets`, input `v` and stage `t`, the
order-0 and fringe send bounds (`hBad`, `hFringe`) and `P` at stage `t` give a `StageKernel`. -/

namespace R1T

variable {sc : R1Scal}

open Finset
open Chvatal (KBag Placement)

theorem strangers_biUnion_le (d : ℕ) (b : KBag 16 d) (j : ℕ)
    (perm : Fin (16 ^ d) → Fin (16 ^ d)) (f : Fin 16 → Finset (Fin (16 ^ d))) :
    (b.strangers j perm ((univ : Finset (Fin 16)).biUnion f) : ℕ) ≤
      ∑ i : Fin 16, b.strangers j perm (f i) := by
  classical
  simp only [KBag.strangers, filter_biUnion]
  exact card_biUnion_le

theorem strangers_child_eq (d : ℕ) (b : KBag 16 d) (hbd : b.l < d)
    (j : ℕ) (hj : 1 ≤ j) (childIdx : Fin 16) (perm : Fin (16 ^ d) → Fin (16 ^ d))
    (S : Finset (Fin (16 ^ d))) :
    b.strangers j perm S = (b.child childIdx.val childIdx.isLt hbd).strangers (j + 1) perm S := by
  have h := KBag.strangers_parent_eq (b.child childIdx.val childIdx.isLt hbd) j hj
    (show 1 ≤ b.l + 1 by omega) perm S (by norm_num)
  rwa [KBag.child_parent b childIdx.val childIdx.isLt hbd (by norm_num)] at h

theorem cap_two_levels (d t : ℕ) (b : KBag 16 d) (hb : 1 ≤ b.l) :
    cap d (b.l + 1) t = 32 * (32 * cap d (b.l - 1) t) := by
  rw [cap_succ_level, show b.l = (b.l - 1) + 1 by omega, cap_succ_level]
  simp

section Children

variable (d t : ℕ) (pl : Placement 16 d) (hP : OutsiderBoundLe sc d t pl id) (b : KBag 16 d)

include hP

theorem strangers_children_le (hbd : b.l < d) (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (S : Finset (Fin (16 ^ d)))
    (hS : S ⊆ Finset.univ.biUnion (fun i : Fin 16 => pl.regs (b.child i.val i.isLt hbd))) :
    (b.strangers j id S : ℚ) ≤ 16 * (sc.mu * sc.delta ^ j * cap d (b.l + 1) t) := by
  calc (b.strangers j id S : ℚ)
      ≤ ∑ i : Fin 16, (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) : ℚ) := by
        exact_mod_cast (b.strangers_mono j id hS).trans
          (strangers_biUnion_le d b j id fun i => pl.regs (b.child i.val i.isLt hbd))
    _ ≤ ∑ _i : Fin 16, sc.mu * sc.delta ^ j * cap d (b.l + 1) t :=
        sum_le_sum fun i _ => by
          rw [strangers_child_eq d b hbd j hj1 i id _]
          exact hP (b.child i.val i.isLt hbd) j hjd
    _ = _ := by simp [sum_const]

theorem hFromChildren0_of_subset (hb : 1 ≤ b.l) (S : Finset (Fin (16 ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin 16 => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅) :
    (b.strangers 1 id S : ℚ) ≤ sc.mu * sc.delta * 16 * 32 ^ 2 * cap d (b.l - 1) t := by
  by_cases hbd : b.l < d
  · refine (strangers_children_le d t pl hP b hbd 1 le_rfl (by omega) S (hS hbd)).trans
      (le_of_eq ?_)
    rw [cap_two_levels d t b hb]; ring
  · rw [hleaf (Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)), KBag.strangers_empty, Nat.cast_zero]
    have := (cap_pos d (b.l - 1) t).le
    have := sc.mu_pos.le; have := sc.delta_pos.le
    positivity

theorem hFromChildrenR_of_subset (hb : 1 ≤ b.l) (S : Finset (Fin (16 ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin 16 => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    (b.strangers (r + 1) id S : ℚ) ≤
      sc.delta ^ 2 * 32 * 16 / (1 / 8) * (sc.mu * sc.delta ^ (r - 1) * (4 * cap d (b.l - 1) t)) := by
  have hnn : (0 : ℚ) ≤ sc.delta ^ 2 * 32 * 16 / (1 / 8) *
      (sc.mu * sc.delta ^ (r - 1) * (4 * cap d (b.l - 1) t)) := by
    have := (cap_pos d (b.l - 1) t).le
    have := sc.mu_pos.le; have := sc.delta_pos.le
    positivity
  by_cases hbd : b.l < d
  · by_cases hrd' : r + 1 ≤ d
    · refine (strangers_children_le d t pl hP b hbd (r + 1) (by omega) hrd' S (hS hbd)).trans
        (le_of_eq ?_)
      rw [cap_two_levels d t b hb]
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
    · rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) id S (by norm_num) (by omega) (by omega),
        Nat.cast_zero]
      exact hnn
  · rw [hleaf (Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)), KBag.strangers_empty, Nat.cast_zero]
    exact hnn

end Children

variable {d tf : ℕ}

/-- The real placement step. -/
noncomputable def realPlacementStep (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf) :
    PlacementStep d (execPlacement F nets v t (by omega)) (execPlacement F nets v (t + 1) ht) where
  fromParent b _ := fromParentK F nets v t b
  fromChildren b _ := fromChildrenK F nets v t b
  hregs b hb := by rw [execPlacement_succ_regs F nets v t ht b hb]

/-- **The real stage kernel.** -/
noncomputable def realStageKernel (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf)
    (hP : OutsiderBoundLe sc d t (execPlacement F nets v t (by omega)) id)
    (hBad : ∀ (b : KBag 16 d) (hb : 1 ≤ b.l),
      ((b.strangers 1 id (fromParentK F nets v t b) : ℕ) : ℚ) ≤
        ((b.parent).strangers 1 id ((execPlacement F nets v t (by omega)).regs b.parent) : ℚ) +
          sc.B0 * cap d (b.l - 1) t)
    (hFringe : ∀ (b : KBag 16 d) (r : ℕ) (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
      ((b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) : ℚ) ≤
        sc.epsF * ((b.parent).strangers r id ((execPlacement F nets v t (by omega)).regs b.parent) : ℚ)) :
    StageKernel sc d t (execPlacement F nets v t (by omega)) id
      (execPlacement F nets v (t + 1) ht) id where
  step := realPlacementStep F nets v t ht
  hBadSend0 b hb := hBad b hb
  hFringeSend b r hr1 hrd hb := hFringe b r hr1 hrd hb
  hFromChildren0 b hb :=
    hFromChildren0_of_subset d t _ hP b hb (fromChildrenK F nets v t b)
      (fun hbd => fromChildrenK_subset F nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt F nets v t b (by omega))
  hFromChildrenR b r hr1 hrd hb :=
    hFromChildrenR_of_subset d t _ hP b hb (fromChildrenK F nets v t b)
      (fun hbd => fromChildrenK_subset F nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt F nets v t b (by omega)) r hr1 hrd
  level0 b r hb0 hr := by
    have h0 : (b.strangers (r + 1) id ((execPlacement F nets v (t + 1) ht).regs b) : ℕ) = 0 :=
      KBag.strangers_eq_zero_of_lt_order b (r + 1) id _ (by norm_num) (by omega) (by omega)
    rw [h0]
    have := cap_pos d 0 (t + 1)
    have hm := sc.mu_pos
    have hdl := sc.delta_pos
    push_cast
    positivity

end R1T
