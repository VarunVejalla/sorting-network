module

public import AKS.Paterson.RankTransfer
public import AKS.Separator.PatersonFlip

/-! # Large-cohort control of fresh strangers

The first halver controls a chosen prefix even when the actual input prefix
is larger than its supported size. The complement estimate below is the
rank-balance bridge used in Paterson's first-stranger argument. In particular,
it does not require the entire native half to satisfy the halver support bound.
-/

@[expose] public section

namespace Paterson

open Finset

theorem good_left_complement {m : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)} (hnet : IsEpsilonAlphaHalver net ε α)
    (v : Equiv.Perm (Fin (2 * m))) {r a : ℕ}
    (hr : r ≤ 2 * m) (hra : r ≤ a) (hs : (r : ℝ) ≤ (α : ℝ) * m) :
    ((univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ a ≤ (net.exec v pos).val)).card : ℝ) ≤
      (m : ℝ) - r + (ε : ℝ) * r := by
  let w := net.exec v
  have hinj : Function.Injective w := ComparatorNetwork.exec_injective net v.injective
  have htotal : (univ.filter (fun pos : Fin (2 * m) ↦ (w pos).val < r)).card = r := by
    rw [bijection_count_val_lt w hinj, card_filter_val_lt (2 * m) r hr]
  have hp := count_val_partition w m r
  have hhalf :
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ (w pos).val < r)).card +
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ r ≤ (w pos).val)).card = m := by
    rw [← card_union_of_disjoint]
    · have heq :
          univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ (w pos).val < r) ∪
          univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ r ≤ (w pos).val) =
          univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m) := by
        ext pos
        simp only [mem_union, mem_filter, mem_univ, true_and]
        omega
      rw [heq, card_filter_val_lt (2 * m) m (by omega)]
    · rw [disjoint_filter]
      intro pos _ h₁ h₂
      omega
  have hsub :
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ a ≤ (w pos).val)).card ≤
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ r ≤ (w pos).val)).card := by
    apply card_le_card
    intro pos hpos
    simp only [mem_filter, mem_univ, true_and] at hpos ⊢
    exact ⟨hpos.1, hra.trans hpos.2⟩
  have herr := (hnet v).1 r hs
  have hpR :
      (r : ℝ) =
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ (w pos).val < r)).card +
      (univ.filter (fun pos : Fin (2 * m) ↦ m ≤ pos.val ∧ (w pos).val < r)).card := by
    exact_mod_cast htotal.symm.trans hp
  have hhR :
      ((univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ (w pos).val < r)).card : ℝ) +
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ r ≤ (w pos).val)).card = m := by
    exact_mod_cast hhalf
  have hsR :
      ((univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ a ≤ (w pos).val)).card : ℝ) ≤
      (univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m ∧ r ≤ (w pos).val)).card := by
    exact_mod_cast hsub
  change ((univ.filter (fun pos : Fin (2 * m) ↦
    pos.val < m ∧ a ≤ (w pos).val)).card : ℝ) ≤ _
  change ((univ.filter (fun pos : Fin (2 * m) ↦
    m ≤ pos.val ∧ (w pos).val < r)).card : ℝ) ≤ _ at herr
  linarith

/-- If the parent has at least `r` values below the child's upper native
boundary, the number sent to the wrong left half is bounded by the first
halver's error plus the unsupported remainder of that half. -/
theorem good_injective_left_complement {m n : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)} (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold r : ℕ)
    (hr : r ≤ 2 * m)
    (hbalance : r ≤ (univ.filter (fun i ↦ (u i).val < threshold)).card)
    (hs : (r : ℝ) ≤ (α : ℝ) * m) :
    ((univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ threshold ≤ (net.exec u pos).val)).card : ℝ) ≤
      (m : ℝ) - r + (ε : ℝ) * r := by
  obtain ⟨g, σ, hg, _, hexec, hcount⟩ := injective_monotone_perm_decomp net u hu
  let a := (univ.filter (fun i ↦ (u i).val < threshold)).card
  have ha_eq : a = (univ.filter (fun i ↦ (g i).val < threshold)).card :=
    hcount (fun v ↦ v.val < threshold)
  have hthresh (i : Fin (2 * m)) : threshold ≤ (g i).val ↔ a ≤ i.val := by
    have hh : (g i).val < threshold ↔ i.val < a := by
      rw [ha_eq]
      exact strictMono_threshold hg threshold i
    omega
  have heq :
      univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ threshold ≤ (net.exec u pos).val) =
      univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ a ≤ (net.exec σ pos).val) := by
    ext pos
    simp only [mem_filter, mem_univ, true_and]
    apply and_congr_right
    intro _
    rw [hexec]
    exact hthresh _
  rw [heq]
  exact good_left_complement hnet σ hr hbalance hs

/-- Fresh strangers in the middle-left output have two sources: residual
values below the parent's native interval and values native to its sibling.
Both terms are retained; fringe filtering has a nonzero error. -/
theorem middle_left_strangers {m n fringe : ℕ} {ε α : ℚ}
    {support err : ℝ} {net : ComparatorNetwork (2 * m)}
    (hsmall : IsSupportedSeparator net fringe support err)
    (hgood : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (lo hi r : ℕ)
    (hlo : ((univ.filter (fun i ↦ (u i).val < lo)).card : ℝ) ≤ support * (2 * m))
    (hr : r ≤ 2 * m)
    (hbalance : r ≤ (univ.filter (fun i ↦ (u i).val < hi)).card)
    (hs : (r : ℝ) ≤ (α : ℝ) * m) :
    ((univ.filter (fun pos : Fin (2 * m) ↦
      fringe ≤ pos.val ∧ pos.val < m ∧
        ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val))).card : ℝ) ≤
      err * (univ.filter (fun i ↦ (u i).val < lo)).card +
        ((m : ℝ) - r + (ε : ℝ) * r) := by
  have hcover :
      univ.filter (fun pos : Fin (2 * m) ↦
        fringe ≤ pos.val ∧ pos.val < m ∧
          ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val)) ⊆
      univ.filter (fun pos : Fin (2 * m) ↦
        fringe ≤ pos.val ∧ (net.exec u pos).val < lo) ∪
      univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ hi ≤ (net.exec u pos).val) := by
    intro pos hp
    simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
    rcases hp.2.2 with h | h
    · exact Or.inl ⟨hp.1, h⟩
    · exact Or.inr ⟨hp.2.1, h⟩
  have hcard := (card_le_card hcover).trans (card_union_le _ _)
  have hcardR :
      ((univ.filter (fun pos : Fin (2 * m) ↦
        fringe ≤ pos.val ∧ pos.val < m ∧
          ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val))).card : ℝ) ≤
      (univ.filter (fun pos : Fin (2 * m) ↦
        fringe ≤ pos.val ∧ (net.exec u pos).val < lo)).card +
      (univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ hi ≤ (net.exec u pos).val)).card := by
    exact_mod_cast hcard
  exact hcardR.trans (add_le_add
    (supported_injective_initial hsmall u hu lo (by simpa using hlo))
    (good_injective_left_complement hgood u hu hi r hr hbalance hs))

/-- Complementing ranks and reversing wires exchanges the two native
cohorts, without changing their cardinalities. -/
theorem reverseFin_prefix_card {wires values : ℕ}
    (u : Fin wires → Fin values) {threshold : ℕ} (ht : threshold ≤ values) :
    (univ.filter (fun i ↦ (reverseFin u i).val < values - threshold)).card =
      (univ.filter (fun i ↦ threshold ≤ (u i).val)).card := by
  apply card_nbij' Fin.rev Fin.rev
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin, Fin.val_rev] at hi ⊢
    have hv := (u i.rev).isLt
    omega
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin,
      Fin.rev_rev, Fin.val_rev] at hi ⊢
    have hv := (u i).isLt
    omega
  · intro i _; simp
  · intro i _; simp

/-- The right-half fresh-stranger complement estimate follows from the
left estimate by exact wire/rank reversal. -/
theorem good_injective_right_complement {m n : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)} (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold r : ℕ)
    (ht : threshold ≤ n) (hr : r ≤ 2 * m)
    (hbalance : r ≤ (univ.filter (fun i ↦ threshold ≤ (u i).val)).card)
    (hs : (r : ℝ) ≤ (α : ℝ) * m) :
    ((univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ (net.exec u pos).val < threshold)).card : ℝ) ≤
      (m : ℝ) - r + (ε : ℝ) * r := by
  have hu' : Function.Injective (reverseFin u) := by
    intro i j hij
    exact Fin.rev_injective (hu (Fin.rev_injective hij))
  have hb : r ≤ (univ.filter (fun i ↦ (reverseFin u i).val < n - threshold)).card := by
    rw [reverseFin_prefix_card u ht]
    exact hbalance
  have h := good_injective_left_complement (flip_isEpsilonAlphaHalver hnet)
    (reverseFin u) hu' (n - threshold) r hr hb hs
  rw [flip_exec_reverseFin] at h
  have heq :
      (univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ n - threshold ≤ (reverseFin (net.exec u) pos).val)).card =
      (univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ (net.exec u pos).val < threshold)).card := by
    apply card_nbij' Fin.rev Fin.rev
    · intro i hi
      simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin, Fin.val_rev] at hi ⊢
      have hv := (net.exec u i.rev).isLt
      have hi' := i.isLt
      constructor <;> omega
    · intro i hi
      simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin,
        Fin.rev_rev, Fin.val_rev] at hi ⊢
      have hv := (net.exec u i).isLt
      have hi' := i.isLt
      constructor <;> omega
    · intro i _; simp
    · intro i _; simp
  rw [heq] at h
  exact h

/-- The middle-right estimate retains residual high strangers and the
wrong-half portion of the selected large final cohort. -/
theorem middle_right_strangers {m n fringe : ℕ} {ε α : ℚ}
    {support err : ℝ} {net : ComparatorNetwork (2 * m)}
    (hsmall : IsSupportedSeparator net fringe support err)
    (hgood : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (lo hi r : ℕ)
    (hhi : ((univ.filter (fun i ↦ hi ≤ (u i).val)).card : ℝ) ≤ support * (2 * m))
    (ht : lo ≤ n) (hr : r ≤ 2 * m)
    (hbalance : r ≤ (univ.filter (fun i ↦ lo ≤ (u i).val)).card)
    (hs : (r : ℝ) ≤ (α : ℝ) * m) :
    ((univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ pos.val < 2 * m - fringe ∧
        ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val))).card : ℝ) ≤
      err * (univ.filter (fun i ↦ hi ≤ (u i).val)).card +
        ((m : ℝ) - r + (ε : ℝ) * r) := by
  have hcover :
      univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ pos.val < 2 * m - fringe ∧
          ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val)) ⊆
      univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < 2 * m - fringe ∧ hi ≤ (net.exec u pos).val) ∪
      univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ (net.exec u pos).val < lo) := by
    intro pos hp
    simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
    rcases hp.2.2 with h | h
    · exact Or.inr ⟨hp.1, h⟩
    · exact Or.inl ⟨hp.2.1, h⟩
  have hcard := (card_le_card hcover).trans (card_union_le _ _)
  have hcardR :
      ((univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ pos.val < 2 * m - fringe ∧
          ((net.exec u pos).val < lo ∨ hi ≤ (net.exec u pos).val))).card : ℝ) ≤
      (univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < 2 * m - fringe ∧ hi ≤ (net.exec u pos).val)).card +
      (univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ (net.exec u pos).val < lo)).card := by
    exact_mod_cast hcard
  exact hcardR.trans (add_le_add
    (supported_injective_final hsmall u hu hi (by simpa using hhi))
    (good_injective_right_complement hgood u hu lo r ht hr hbalance hs))

end Paterson
