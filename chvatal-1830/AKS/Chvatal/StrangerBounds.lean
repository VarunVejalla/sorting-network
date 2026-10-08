module

/-
  # Stranger-count bounds for instantiating `StageKernel` (task K1)

  (A) Worst-case children part (Chvátal, DCS-TR-294, Lemmas 4.3-4.4): every outsider of order
  `r+1` in a bag `b` that arrived from a child was an outsider of order `r+2` there, so it is
  counted by the invariant `P` at the `br` children; no fairness is used.

  (B) Fringe part (Lemma 4.4, parent part): a pure finite-set lemma bounding the keys sent down
  by a node (outside its two fringes) that fall outside the address interval, by the F-property.
-/

public import AKS.Chvatal.ChildSend
public import AKS.Chvatal.OutsiderInduction

@[expose] public section

namespace Chvatal

open Finset

/-! ## (A) children part -/

/-- Common core: order-`j` strangers of a set of child registers. -/
theorem strangers_children_le (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (pl : Placement p.br d)
    (hP : OutsiderBoundLe p ip d sched t pl id)
    (b : KBag p.br d) (hbd : b.l < d) (j : Nat) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (S : Finset (Fin (p.br ^ d)))
    (hS : S ⊆ Finset.univ.biUnion (fun i : Fin p.br => pl.regs (b.child i.val i.isLt hbd))) :
    (b.strangers j id S (br_ge_one p) : Rat) ≤
      (p.br : Rat) * (ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t) := by
  have hbr := br_ge_one p
  have hmono := b.strangers_mono j id hS hbr
  have hunion := strangers_biUnion_le p d b j id
    (fun i => pl.regs (b.child i.val i.isLt hbd))
  have hnat := Nat.le_trans hmono hunion
  have hcast : (b.strangers j id S hbr : Rat) ≤
      ∑ i : Fin p.br, (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) hbr : Rat) := by
    exact_mod_cast hnat
  have hterm : ∀ i : Fin p.br,
      (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) hbr : Rat) ≤
        ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t := by
    intro i
    have heq := strangers_child_eq p d b hbd j hj1 i id
      (pl.regs (b.child i.val i.isLt hbd)) hbr
    have hPch := hP (b.child i.val i.isLt hbd) j hjd
    have hcl : (b.child i.val i.isLt hbd).l = b.l + 1 := rfl
    rw [hcl] at hPch
    rw [heq]
    exact hPch
  calc (b.strangers j id S hbr : Rat)
      ≤ ∑ i : Fin p.br, (b.strangers j id (pl.regs (b.child i.val i.isLt hbd)) hbr : Rat) :=
        hcast
    _ ≤ ∑ _i : Fin p.br, ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t :=
        sum_le_sum (fun i _ => hterm i)
    _ = (p.br : Rat) * (ip.mu * ip.delta ^ j * capacity p d (b.l + 1) t) := by
        simp [sum_const]

theorem hFromChildren0_of_subset (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (pl : Placement p.br d)
    (hP : OutsiderBoundLe p ip d sched t pl id)
    (b : KBag p.br d) (hb : 1 ≤ b.l)
    (S : Finset (Fin (p.br ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin p.br => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅) :
    (b.strangers 1 id S (br_ge_one p) : Rat) ≤
      ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * capacity p d (b.l - 1) t := by
  have hbr := br_ge_one p
  have hcap1 : capacity p d (b.l + 1) t = p.A * capacity p d b.l t :=
    capacity_succ_level p d b.l t
  have hcap0 : capacity p d b.l t = p.A * capacity p d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega]
    exact capacity_succ_level p d (b.l - 1) t
  by_cases hbd : b.l < d
  · have h := strangers_children_le p ip d sched t pl hP b hbd 1 le_rfl (by omega) S (hS hbd)
    refine h.trans (le_of_eq ?_)
    rw [hcap1, hcap0]; ring
  · have hl : b.l = d := Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)
    rw [hleaf hl, KBag.strangers_empty, Nat.cast_zero]
    have := (capacity_pos p d (b.l - 1) t).le
    have := ip.mu_nonneg; have := ip.delta_nonneg; have := p.br_cast_pos.le
    positivity

theorem hFromChildrenR_of_subset (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (pl : Placement p.br d)
    (hP : OutsiderBoundLe p ip d sched t pl id)
    (b : KBag p.br d) (hb : 1 ≤ b.l)
    (S : Finset (Fin (p.br ^ d)))
    (hS : ∀ hbd : b.l < d,
      S ⊆ Finset.univ.biUnion (fun j : Fin p.br => pl.regs (b.child j.val j.isLt hbd)))
    (hleaf : b.l = d → S = ∅)
    (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    (b.strangers (r + 1) id S (br_ge_one p) : Rat) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * capacity p d (b.l - 1) t)) := by
  have hbr := br_ge_one p
  have hcap1 : capacity p d (b.l + 1) t = p.A * capacity p d b.l t :=
    capacity_succ_level p d b.l t
  have hcap0 : capacity p d b.l t = p.A * capacity p d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega]
    exact capacity_succ_level p d (b.l - 1) t
  have hnn : (0 : Rat) ≤ ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * capacity p d (b.l - 1) t)) := by
    have := (capacity_pos p d (b.l - 1) t).le
    have := ip.mu_nonneg; have := ip.delta_nonneg; have := p.br_cast_pos.le
    have := p.A_pos.le; have := p.hnu_pos.le
    positivity
  by_cases hbd : b.l < d
  · by_cases hrd' : r + 1 ≤ d
    · have h := strangers_children_le p ip d sched t pl hP b hbd (r + 1) (by omega) hrd' S
        (hS hbd)
      refine h.trans (le_of_eq ?_)
      rw [hcap1, hcap0]
      exact childrenR_scale p ip (capacity p d (b.l - 1) t) r hr1
    · have hz := KBag.strangers_eq_zero_of_lt_order b (r + 1) id S hbr (by omega)
        (by omega)
      rw [hz, Nat.cast_zero]; exact hnn
  · have hl : b.l = d := Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)
    rw [hleaf hl, KBag.strangers_empty, Nat.cast_zero]; exact hnn

/-! ## (B) fringe part (pure finite-set lemma) -/

/-- Rank of a key within the key set `K` (number of smaller keys). -/
def keyRank {N : ℕ} (K : Finset (Fin N)) (κ : Fin N) : ℕ := (K.filter (· < κ)).card

/-- A high outsider (address `≥ Ihi`) has rank at least `|K| - |Hhi|`. -/
theorem keyRank_ge_of_hi {N : ℕ} (K : Finset (Fin N)) (Ihi : ℕ) {κ : Fin N}
    (hκ : Ihi ≤ (κ : ℕ)) :
    K.card - (K.filter fun (x : Fin N) => Ihi ≤ (x : ℕ)).card ≤ keyRank K κ := by
  unfold keyRank
  have h1 := Finset.card_filter_add_card_filter_not (s := K) (fun x : Fin N => Ihi ≤ (x : ℕ))
  have h2 : (K.filter fun x : Fin N => ¬ Ihi ≤ (x : ℕ)).card ≤ (K.filter (· < κ)).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [Fin.lt_def]; omega
  omega

/-- A low outsider (address `< Ilo`) has rank below `|Hlo|`. -/
theorem keyRank_lt_of_lo {N : ℕ} (K : Finset (Fin N)) (Ilo : ℕ) {κ : Fin N} (hκK : κ ∈ K)
    (hκ : (κ : ℕ) < Ilo) :
    keyRank K κ < (K.filter fun (x : Fin N) => (x : ℕ) < Ilo).card := by
  unfold keyRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨κ, by simp [hκK, hκ], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have := hx.2; rw [Fin.lt_def] at this; omega

theorem keyRank_lt_card {N : ℕ} (K : Finset (Fin N)) {κ : Fin N} (hκ : κ ∈ K) :
    keyRank K κ < K.card := by
  unfold keyRank
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨κ, hκ, by simp⟩)

/-- Fringe part (Lemma 4.4, parent part): keys sent down outside the address interval are
bounded by the F-property applied to the top `|Hhi|` and bottom `|Hlo|` ranks.
(`π ≤ a`, injectivity of `pos` and `pos < a` are not needed.) -/
theorem sent_outside_le {N : ℕ} (K : Finset (Fin N)) (pos : Fin N → ℕ) (π Ilo Ihi Jmax : ℕ)
    (εF : ℝ)
    (hfH : ∀ j, 0 < j → j ≤ Jmax → j ≤ K.card →
      ((K.filter fun (κ : Fin N) => K.card - j ≤ keyRank K κ ∧ pos κ < K.card - π / 2).card : ℝ) < εF * j)
    (hfL : ∀ j, 0 < j → j ≤ Jmax → j ≤ K.card →
      ((K.filter fun (κ : Fin N) => keyRank K κ < j ∧ π / 2 ≤ pos κ).card : ℝ) < εF * j)
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
      (K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ keyRank K κ ∧ pos κ < K.card - π / 2) ∪
      (K.filter fun (κ : Fin N) => keyRank K κ < Hlo.card ∧ π / 2 ≤ pos κ) := by
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
  have hcast : ((Sent.filter (fun (κ : Fin N) => ¬ (Ilo ≤ (κ : ℕ) ∧ (κ : ℕ) < Ihi))).card : ℝ) ≤
      ((K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ keyRank K κ ∧ pos κ < K.card - π / 2).card : ℝ) +
      ((K.filter fun (κ : Fin N) => keyRank K κ < Hlo.card ∧ π / 2 ≤ pos κ).card : ℝ) := by
    exact_mod_cast hcard
  have hHa : Hhi.card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hLa : Hlo.card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have h1 : ((K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ keyRank K κ ∧
      pos κ < K.card - π / 2).card : ℝ) ≤ εF * (Hhi.card : ℝ) := by
    rcases Nat.eq_zero_or_pos Hhi.card with h0 | hpos
    · have hnone : (K.filter fun (κ : Fin N) => K.card - Hhi.card ≤ keyRank K κ ∧
          pos κ < K.card - π / 2) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro κ hκ
        simp only [Finset.mem_filter] at hκ
        have hlt := keyRank_lt_card K hκ.1
        have := hκ.2.1
        omega
      rw [hnone, h0]; simp
    · exact (hfH _ hpos hHhi hHa).le
  have h2 : ((K.filter fun (κ : Fin N) => keyRank K κ < Hlo.card ∧ π / 2 ≤ pos κ).card : ℝ) ≤
      εF * (Hlo.card : ℝ) := by
    rcases Nat.eq_zero_or_pos Hlo.card with h0 | hpos
    · have hnone : (K.filter fun (κ : Fin N) => keyRank K κ < Hlo.card ∧ π / 2 ≤ pos κ) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro κ hκ
        simp only [Finset.mem_filter] at hκ
        omega
      rw [hnone, h0]; simp
    · exact (hfL _ hpos hHlo hLa).le
  calc _ ≤ _ := hcast
    _ ≤ εF * (Hhi.card : ℝ) + εF * (Hlo.card : ℝ) := add_le_add h1 h2
    _ = _ := by ring

end Chvatal
