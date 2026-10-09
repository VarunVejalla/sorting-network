module

public import AKS.Chvatal.ChildSend
public import AKS.Chvatal.WireFlow
public import AKS.Chvatal.OutsiderInduction

@[expose] public section

/-! Stranger-count bounds for instantiating `StageKernel`. (A) Children part (Chvátal Lemmas
4.3-4.4): an outsider of order `r+1` that arrived from a child was an outsider of order `r+2`
there, so it is counted by the invariant `P` at the children. (B) Fringe part: a finite-set lemma
bounding the keys sent down outside the fringes that fall outside the address interval. -/

namespace Chvatal

open Finset

section Children

theorem capacity_two_levels (p : ScheduleParams) (d t : Nat) (b : KBag p.br d) (hb : 1 ≤ b.l) :
    capacity p d (b.l + 1) t = p.A * (p.A * capacity p d (b.l - 1) t) := by
  rw [capacity_succ_level, show b.l = (b.l - 1) + 1 by omega, capacity_succ_level]
  simp

variable (p : ScheduleParams) (ip : InvariantParams) (d : Nat) (sched : LevelSchedule p d) (t : Nat)
  (pl : Placement p.br d) (hP : OutsiderBoundLe p ip d sched t pl id) (b : KBag p.br d)

include hP

/-- Common core: order-`j` strangers of a set of child registers. -/
theorem strangers_children_le (hbd : b.l < d) (j : Nat) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (S : Finset (Fin (p.br ^ d)))
    (hS : S ⊆ Finset.univ.biUnion (fun i : Fin p.br => pl.regs (b.child i.val i.isLt hbd))) :
    (b.strangers j id S (br_ge_one p) : Rat) ≤
      (p.br : Rat) * (ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t) := by
  have hbr := br_ge_one p
  calc (b.strangers j id S hbr : Rat)
      ≤ ∑ i : Fin p.br, (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) hbr : Rat) := by
        exact_mod_cast (b.strangers_mono j id hS hbr).trans
          (strangers_biUnion_le p d b j id fun i => pl.regs (b.child i.val i.isLt hbd))
    _ ≤ ∑ _i : Fin p.br, ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t :=
        sum_le_sum fun i _ => by
          rw [strangers_child_eq p d b hbd j hj1 i id _ hbr]
          exact hP (b.child i.val i.isLt hbd) j hjd
    _ = _ := by simp [sum_const]

theorem hFromChildren0_of_subset (hb : 1 ≤ b.l)
    (S : Finset (Fin (p.br ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin p.br => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅) :
    (b.strangers 1 id S (br_ge_one p) : Rat) ≤
      ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * capacity p d (b.l - 1) t := by
  have hbr := br_ge_one p
  by_cases hbd : b.l < d
  · refine (strangers_children_le p ip d sched t pl hP b hbd 1 le_rfl (by omega) S (hS hbd)).trans
      (le_of_eq ?_)
    rw [capacity_two_levels p d t b hb]; ring
  · rw [hleaf (Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)), KBag.strangers_empty, Nat.cast_zero]
    have := (capacity_pos p d (b.l - 1) t).le
    have := ip.mu_nonneg; have := ip.delta_nonneg; have := p.br_cast_pos.le
    positivity

theorem hFromChildrenR_of_subset (hb : 1 ≤ b.l)
    (S : Finset (Fin (p.br ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin p.br => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅)
    (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    (b.strangers (r + 1) id S (br_ge_one p) : Rat) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * capacity p d (b.l - 1) t)) := by
  have hbr := br_ge_one p
  have hnn : (0 : Rat) ≤ ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * capacity p d (b.l - 1) t)) := by
    have := (capacity_pos p d (b.l - 1) t).le
    have := ip.mu_nonneg; have := ip.delta_nonneg; have := p.br_cast_pos.le
    have := p.A_pos.le; have := p.hnu_pos.le
    positivity
  by_cases hbd : b.l < d
  · by_cases hrd' : r + 1 ≤ d
    · refine (strangers_children_le p ip d sched t pl hP b hbd (r + 1) (by omega) hrd' S
        (hS hbd)).trans (le_of_eq ?_)
      rw [capacity_two_levels p d t b hb]
      exact childrenR_scale p ip (capacity p d (b.l - 1) t) r hr1
    · rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) id S (br_ge_one p) (by omega) (by omega),
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
