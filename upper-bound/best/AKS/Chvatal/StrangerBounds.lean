module

public import AKS.Chvatal.StageKernel
public import AKS.Chvatal.WireFlow

@[expose] public section

/-! Stranger-count bounds for instantiating `StageKernel`. (A) Children part (Chvátal Lemmas
4.3-4.4): an outsider of order `r+1` that arrived from a child was an outsider of order `r+2`
there, so it is counted by the invariant `P` at the children. (B) Fringe part: a finite-set lemma
bounding the keys sent down outside the fringes that fall outside the address interval. -/

namespace Chvatal

open Finset

section Children

theorem capacity_two_levels (d t : Nat) (b : KBag 64 d) (hb : 1 ≤ b.l) :
    capacity d (b.l + 1) t = (4096 : Rat) * ((4096 : Rat) * capacity d (b.l - 1) t) := by
  rw [capacity_succ_level, show b.l = (b.l - 1) + 1 by omega, capacity_succ_level]
  simp

variable (d t : Nat)
  (pl : Placement 64 d) (hP : OutsiderBoundLe d t pl id) (b : KBag 64 d)

include hP

/-- Common core: order-`j` strangers of a set of child registers. -/
theorem strangers_children_le (hbd : b.l < d) (j : Nat) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (S : Finset (Fin (64 ^ d)))
    (hS : S ⊆ Finset.univ.biUnion (fun i : Fin 64 => pl.regs (b.child i.val i.isLt hbd))) :
    (b.strangers j id S : Rat) ≤
      (64 : Rat) * (invMu * invDelta ^ j * capacity d (b.l + 1) t) := by
  calc (b.strangers j id S : Rat)
      ≤ ∑ i : Fin 64, (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) : Rat) := by
        exact_mod_cast (b.strangers_mono j id hS).trans
          (strangers_biUnion_le d b j id fun i => pl.regs (b.child i.val i.isLt hbd))
    _ ≤ ∑ _i : Fin 64, invMu * invDelta ^ j * capacity d (b.l + 1) t :=
        sum_le_sum fun i _ => by
          rw [strangers_child_eq d b hbd j hj1 i id _]
          exact hP (b.child i.val i.isLt hbd) j hjd
    _ = _ := by simp [sum_const]

theorem hFromChildren0_of_subset (hb : 1 ≤ b.l)
    (S : Finset (Fin (64 ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin 64 => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅) :
    (b.strangers 1 id S : Rat) ≤
      invMu * invDelta * (64 : Rat) * (4096 : Rat) ^ 2 * capacity d (b.l - 1) t := by
  by_cases hbd : b.l < d
  · refine (strangers_children_le d t pl hP b hbd 1 le_rfl (by omega) S (hS hbd)).trans
      (le_of_eq ?_)
    rw [capacity_two_levels d t b hb]; ring
  · rw [hleaf (Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)), KBag.strangers_empty, Nat.cast_zero]
    have := (capacity_pos d (b.l - 1) t).le
    have := invMu_pos.le; have := invDelta_pos.le
    positivity

theorem hFromChildrenR_of_subset (hb : 1 ≤ b.l)
    (S : Finset (Fin (64 ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin 64 => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅)
    (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    (b.strangers (r + 1) id S : Rat) ≤
      invDelta ^ 2 * (4096 : Rat) * (64 : Rat) / (1 / 64 : Rat) *
        (invMu * invDelta ^ (r - 1) * ((4096 : Rat) * (1 / 64 : Rat) * capacity d (b.l - 1) t)) := by
  have hnn : (0 : Rat) ≤ invDelta ^ 2 * (4096 : Rat) * (64 : Rat) / (1 / 64 : Rat) *
        (invMu * invDelta ^ (r - 1) * ((4096 : Rat) * (1 / 64 : Rat) * capacity d (b.l - 1) t)) := by
    have := (capacity_pos d (b.l - 1) t).le
    have := invMu_pos.le; have := invDelta_pos.le
    positivity
  by_cases hbd : b.l < d
  · by_cases hrd' : r + 1 ≤ d
    · refine (strangers_children_le d t pl hP b hbd (r + 1) (by omega) hrd' S
        (hS hbd)).trans (le_of_eq ?_)
      rw [capacity_two_levels d t b hb]
      exact childrenR_scale (capacity d (b.l - 1) t) r hr1
    · rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) id S (by norm_num) (by omega) (by omega),
        Nat.cast_zero]
      exact hnn
  · rw [hleaf (Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)), KBag.strangers_empty, Nat.cast_zero]
    exact hnn

end Children

/-- A high outsider (address `≥ Ihi`) has rank at least `|K| - |Hhi|`. -/
theorem keyRank_ge_of_hi {N : ℕ} (K : Finset (Fin N)) (Ihi : ℕ) {κ : Fin N}
    (hκ : Ihi ≤ (κ : ℕ)) :
    K.card - (K.filter fun (x : Fin N) => Ihi ≤ (x : ℕ)).card ≤ rankIn K κ := by
  have h1 := Finset.card_filter_add_card_filter_not (s := K) (fun x : Fin N => Ihi ≤ (x : ℕ))
  have h2 : (K.filter fun x : Fin N => ¬ Ihi ≤ (x : ℕ)).card ≤ rankIn K κ :=
    Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by rw [Fin.lt_def]; omega⟩
  omega

/-- A low outsider (address `< Ilo`) has rank below `|Hlo|`. -/
theorem keyRank_lt_of_lo {N : ℕ} (K : Finset (Fin N)) (Ilo : ℕ) {κ : Fin N} (hκK : κ ∈ K)
    (hκ : (κ : ℕ) < Ilo) :
    rankIn K κ < (K.filter fun (x : Fin N) => (x : ℕ) < Ilo).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by have := hx.2; rw [Fin.lt_def] at this; omega⟩).2
      ⟨κ, by simp [hκK, hκ], by simp⟩)

/-- Fringe part (Lemma 4.4, parent part): keys sent down outside the address interval are
bounded by the F-property applied to the top `|Hhi|` and bottom `|Hlo|` ranks.
(`π ≤ a`, injectivity of `pos` and `pos < a` are not needed.) -/
theorem sent_outside_le {N : ℕ} (K : Finset (Fin N)) (pos : Fin N → ℕ) (π Ilo Ihi Jmax : ℕ)
    (εF : ℝ)
    (hfH : ∀ j, 0 < j → j ≤ Jmax → j ≤ K.card →
      ((K.filter fun (κ : Fin N) => K.card - j ≤ rankIn K κ ∧ pos κ < K.card - π / 2).card : ℝ) < εF * j)
    (hfL : ∀ j, 0 < j → j ≤ Jmax → j ≤ K.card →
      ((K.filter fun (κ : Fin N) => rankIn K κ < j ∧ π / 2 ≤ pos κ).card : ℝ) < εF * j)
    (hHhi : (K.filter fun (κ : Fin N) => Ihi ≤ (κ : ℕ)).card ≤ Jmax)
    (hHlo : (K.filter fun (κ : Fin N) => (κ : ℕ) < Ilo).card ≤ Jmax) :
    (((K.filter fun (κ : Fin N) => π / 2 ≤ pos κ ∧ pos κ < K.card - π / 2).filter
        fun (κ : Fin N) => ¬ (Ilo ≤ (κ : ℕ) ∧ (κ : ℕ) < Ihi)).card : ℝ) ≤
      εF * (((K.filter fun (κ : Fin N) => Ihi ≤ (κ : ℕ)).card : ℝ) +
        ((K.filter fun (κ : Fin N) => (κ : ℕ) < Ilo).card : ℝ)) := by
  classical
  set Hhi := K.filter fun κ : Fin N => Ihi ≤ (κ : ℕ) with hHhidef
  set Hlo := K.filter fun κ : Fin N => (κ : ℕ) < Ilo with hHlodef
  set Sent := K.filter fun κ : Fin N => π / 2 ≤ pos κ ∧ pos κ < K.card - π / 2 with hSent
  have hsub : Sent.filter (fun (κ : Fin N) => ¬ (Ilo ≤ (κ : ℕ) ∧ (κ : ℕ) < Ihi)) ⊆
      (K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ rankIn K κ ∧ pos κ < K.card - π / 2) ∪
      (K.filter fun (κ : Fin N) => rankIn K κ < Hlo.card ∧ π / 2 ≤ pos κ) := by
    intro κ hκ
    simp only [hSent, Finset.mem_filter, Finset.mem_union] at hκ ⊢
    obtain ⟨⟨hK, hp1, hp2⟩, hn⟩ := hκ
    by_cases hhi : Ihi ≤ (κ : ℕ)
    · left
      exact ⟨hK, keyRank_ge_of_hi K Ihi hhi, hp2⟩
    · right
      have hlo : (κ : ℕ) < Ilo := by omega
      exact ⟨hK, keyRank_lt_of_lo K Ilo hK hlo, hp1⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcast := (Nat.cast_le (α := ℝ)).2 hcard
  push_cast at hcast
  have hHa : Hhi.card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hLa : Hlo.card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have h1 : ((K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ rankIn K κ ∧
      pos κ < K.card - π / 2).card : ℝ) ≤ εF * (Hhi.card : ℝ) := by
    rcases Nat.eq_zero_or_pos Hhi.card with h0 | hpos
    · rw [Finset.filter_eq_empty_iff.2 (fun κ hκ h => by have := rankIn_lt_card hκ; omega), h0]
      simp
    · exact (hfH _ hpos hHhi hHa).le
  have h2 : ((K.filter fun (κ : Fin N) => rankIn K κ < Hlo.card ∧ π / 2 ≤ pos κ).card : ℝ) ≤
      εF * (Hlo.card : ℝ) := by
    rcases Nat.eq_zero_or_pos Hlo.card with h0 | hpos
    · rw [Finset.filter_eq_empty_iff.2 (fun κ hκ h => by omega), h0]
      simp
    · exact (hfL _ hpos hHlo hLa).le
  linarith

end Chvatal
