import R1Exec
import AKS.Chvatal.NodeKeys

/-! # Node contract with bounds at every cut (W1, step 4)

`NodeSpecAll a π net EB Jmax εF`: the misplaced keys across **every** cut position `p ≤ a` number at
most `EB` (both directions), and the fringe clauses of Theorem 5.1. The padded separator
(`paddedPack2Net_all_cut_bounds`) gives cut bounds at every position, and an exact sorter gives `0`.
With per-child blocks of arbitrary sizes, the intruders into any cell window `[s, e)` are then at
most `2·EB` (`intruder_keys`). -/

namespace R1T

open Chvatal (rk keySet rankPerm exec_rankPerm exec_keySet_injective)

/-- Two-sided position form of the separator guarantee, at every cut. -/
structure NodeSpecAll (a π : ℕ) (net : ComparatorNetwork a) (EB : ℝ) (Jmax : ℕ) (εF : ℝ) :
    Prop where
  bHigh : ∀ (x : Equiv.Perm (Fin a)), ∀ p, p ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        a - p ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - p).card : ℝ) ≤ EB
  bLow : ∀ (x : Equiv.Perm (Fin a)), ∀ p, p ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < p ∧ p ≤ c.val).card : ℝ) ≤ EB
  fHigh : ∀ (x : Equiv.Perm (Fin a)) (j : ℕ), 0 < j → j ≤ Jmax → j ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        a - j ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - π / 2).card : ℝ) < εF * j
  fLow : ∀ (x : Equiv.Perm (Fin a)) (j : ℕ), 0 < j → j ≤ Jmax → j ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < j ∧ π / 2 ≤ c.val).card : ℝ) < εF * j

section Keys

variable {a M : ℕ} {π : ℕ} {net : ComparatorNetwork a} {EB : ℝ} {Jmax : ℕ} {εF : ℝ}

theorem NodeSpecAll.fHigh_keys (h : NodeSpecAll a π net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (j : ℕ) (hj : 0 < j) (hjm : j ≤ Jmax) (hja : j ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        a - j ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < a - π / 2).card : ℝ) < εF * j := by
  have := h.fHigh (rankPerm hxr) j hj hjm hja
  simpa only [exec_rankPerm hxr net] using this

theorem NodeSpecAll.fLow_keys (h : NodeSpecAll a π net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (j : ℕ) (hj : 0 < j) (hjm : j ≤ Jmax) (hja : j ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        rk (keySet xr) (net.exec xr c) < j ∧ π / 2 ≤ c.val).card : ℝ) < εF * j := by
  have := h.fLow (rankPerm hxr) j hj hjm hja
  simpa only [exec_rankPerm hxr net] using this

/-- **Intruders into a window.** The keys in the cell window `[s, e)` whose rank (among the node's
keys) lies outside `[s, e)` number at most `2·EB`. -/
theorem NodeSpecAll.intruder_keys (h : NodeSpecAll a π net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (s e : ℕ) (hse : s ≤ e) (hea : e ≤ a) :
    (((((Finset.univ.filter fun c : Fin a => s ≤ c.val ∧ c.val < e)).image (net.exec xr)).filter
        fun κ => ¬ (s ≤ rk (keySet xr) κ ∧ rk (keySet xr) κ < e)).card : ℝ) ≤ 2 * EB := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (exec_keySet_injective hxr net),
    Finset.filter_filter]
  simp only [Function.comp, ← exec_rankPerm hxr net]
  have h1 := h.bLow (rankPerm hxr) s (by omega)
  have h2 := h.bHigh (rankPerm hxr) (a - e) (by omega)
  rw [show a - (a - e) = e by omega] at h2
  have hsub : (Finset.univ.filter fun c : Fin a =>
      (s ≤ c.val ∧ c.val < e) ∧
        ¬ (s ≤ (net.exec (rankPerm hxr : Fin a → Fin a) c).val ∧
           (net.exec (rankPerm hxr : Fin a → Fin a) c).val < e)) ⊆
      (Finset.univ.filter fun c : Fin a =>
        (net.exec (rankPerm hxr : Fin a → Fin a) c).val < s ∧ s ≤ c.val) ∪
      (Finset.univ.filter fun c : Fin a =>
        e ≤ (net.exec (rankPerm hxr : Fin a → Fin a) c).val ∧ c.val < e) := by
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have h3 := Nat.cast_le (α := ℝ) |>.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  push_cast at h3
  linarith

end Keys

end R1T
