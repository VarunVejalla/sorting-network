module

public import AKS.Paterson.GoodRouting
public import AKS.Paterson.Interior
public import AKS.Paterson.LatticeRounding

/-! # The actual local separator in a rounded bag

This module connects the supported separator to register sets and the bag
stranger predicate. The output can be that of a whole parallel stage: only
its restriction to this bag must agree with the local separator execution.
Source: Paterson (1990), Sections 4 and 7.
-/

@[expose] public section

namespace Paterson

open Finset

/-- Simultaneous filtering of both tails of an ambient rank interval. -/
theorem supported_injective_interval {m n fringe : ℕ}
    {net : ComparatorNetwork m} {support err : ℝ}
    (hnet : IsSupportedSeparator net fringe support err)
    (u : Fin m → Fin n) (hu : Function.Injective u) (lo hi : ℕ)
    (hlh : lo ≤ hi)
    (hs : ((univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val)).card : ℝ) ≤
      support * m) :
    ((univ.filter (fun i ↦ fringe ≤ i.val ∧ i.val < m - fringe ∧
      ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val))).card : ℝ) ≤
      err * (univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val)).card := by
  have hlow := card_le_card (show
      univ.filter (fun i ↦ (u i).val < lo) ⊆
        univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val) from by
    intro i h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    exact Or.inl h)
  have hhigh := card_le_card (show
      univ.filter (fun i ↦ hi ≤ (u i).val) ⊆
        univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val) from by
    intro i h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    exact Or.inr h)
  have hL := supported_injective_initial hnet u hu lo
    ((Nat.cast_le.mpr hlow).trans hs)
  have hH := supported_injective_final hnet u hu hi
    ((Nat.cast_le.mpr hhigh).trans hs)
  have hcover :
      univ.filter (fun i ↦ fringe ≤ i.val ∧ i.val < m - fringe ∧
        ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val)) ⊆
      univ.filter (fun i ↦ fringe ≤ i.val ∧ (net.exec u i).val < lo) ∪
        univ.filter (fun i ↦ i.val < m - fringe ∧ hi ≤ (net.exec u i).val) := by
    intro i h
    simp only [mem_filter, mem_univ, true_and, mem_union] at h ⊢
    rcases h.2.2 with h' | h'
    · exact Or.inl ⟨h.1, h'⟩
    · exact Or.inr ⟨h.2.1, h'⟩
  have hsum :
      (univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val)).card =
      (univ.filter (fun i ↦ (u i).val < lo)).card +
        (univ.filter (fun i ↦ hi ≤ (u i).val)).card := by
    rw [show univ.filter (fun i ↦ (u i).val < lo ∨ hi ≤ (u i).val) =
        univ.filter (fun i ↦ (u i).val < lo) ∪
          univ.filter (fun i ↦ hi ≤ (u i).val) from by ext i; simp]
    apply card_union_of_disjoint
    rw [disjoint_filter]
    intro i _ h₁ h₂
    omega
  have hc :
      ((univ.filter (fun i ↦ fringe ≤ i.val ∧ i.val < m - fringe ∧
        ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val))).card : ℝ) ≤
      (univ.filter (fun i ↦ fringe ≤ i.val ∧ (net.exec u i).val < lo)).card +
        (univ.filter (fun i ↦ i.val < m - fringe ∧ hi ≤ (net.exec u i).val)).card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  rw [hsum, Nat.cast_add, mul_add]
  exact hc.trans (add_le_add hL hH)

namespace Bags

/-- Transport a filtered count through the canonical enumeration of a bag. -/
theorem filter_image_card {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (s : Finset (Fin regs.card)) (P : Fin (2 ^ k) → Prop) [DecidablePred P] :
    (((s.image (regs.orderEmbOfFin rfl)).filter P).card) =
      (s.filter (fun i ↦ P (regs.orderEmbOfFin rfl i))).card := by
  rw [filter_image, card_image_of_injective _ (regs.orderEmbOfFin rfl).injective]

theorem filter_regs_card {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (P : Fin (2 ^ k) → Prop) [DecidablePred P] :
    (regs.filter P).card =
      (univ.filter (fun i ↦ P (regs.orderEmbOfFin rfl i))).card := by
  have himage : univ.image (regs.orderEmbOfFin rfl) = regs := by
    ext r
    simp only [mem_image, mem_univ, true_and]
    exact (show (∃ i, regs.orderEmbOfFin rfl i = r) ↔ r ∈ regs from by
      rw [← Set.mem_range, range_orderEmbOfFin]; rfl)
  conv_lhs => rw [← himage]
  exact filter_image_card regs univ P

/-- Scattered local network used by a full lattice bag. -/
noncomputable def bagSeparator {k : ℕ} (regs : Finset (Fin (2 ^ k))) :
    ComparatorNetwork (2 ^ k) :=
  (separatorNetwork regs.card).scatterEmbed (2 ^ k) (regs.orderEmbOfFin rfl)

/-- The separator has the fixed per-stage depth budget on every register set. -/
theorem bagSeparator_depth_le {k : ℕ} (regs : Finset (Fin (2 ^ k))) :
    (bagSeparator regs).depth ≤ 989 :=
  (depth_scatterEmbed_le _ _ _).trans (separatorNetwork_depth_le _)

/-- Supported old strangers are filtered in the actual middle output.
`hview` is an execution equality, rather than a stranger-bound assumption. -/
theorem bagNetwork_filters {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (heven : 2 ∣ regs.card) (net : ComparatorNetwork regs.card)
    {fringe : ℕ} {support err : ℝ}
    (hsmall : IsSupportedSeparator net fringe support err)
    (f : ℕ) (hf : fringe ≤ f)
    (hhalf : f ≤ regs.card / 2)
    (w w' : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hview : ∀ i, w' (regs.orderEmbOfFin rfl i) =
      net.exec (w ∘ regs.orderEmbOfFin rfl) i)
    (b : Bag k) (j : ℕ) (hj : 1 ≤ j)
    (hs : (b.strangers j w regs : ℝ) ≤ support * regs.card) :
    (b.strangers j w' ((split regs f).toLeft ∪ (split regs f).toRight) : ℝ) ≤
      err * b.strangers j w regs := by
  let anc := b.ancestor (j - 1)
  have hstrange (v : Fin (2 ^ k) → Fin (2 ^ k)) (r : Fin (2 ^ k)) :
      b.Strange j r v ↔ (v r).val < anc.lo ∨ anc.hi ≤ (v r).val := by
    simp only [Bag.Strange, show j ≠ 0 by omega, false_or]
    rw [Bag.native_iff]
    simp only [not_and_or, Nat.not_le, Nat.not_lt]
    rfl
  have hcount (v : Fin (2 ^ k) → Fin (2 ^ k)) :
      b.strangers j v regs =
        (univ.filter (fun i ↦ (v (regs.orderEmbOfFin rfl i)).val < anc.lo ∨
          anc.hi ≤ (v (regs.orderEmbOfFin rfl i)).val)).card := by
    unfold Bag.strangers
    rw [filter_regs_card]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact hstrange v _
  have hmiddle : (split regs f).toLeft ∪ (split regs f).toRight =
      (univ.filter (fun i : Fin regs.card ↦ f ≤ i.val ∧ i.val < regs.card - f)).image
        (regs.orderEmbOfFin rfl) := by
    have hc : 2 * (regs.card / 2) = regs.card := Nat.mul_div_cancel' heven
    simp only [split, ← image_union]
    congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    omega
  have houtput : b.strangers j w'
      ((split regs f).toLeft ∪ (split regs f).toRight) =
      (univ.filter (fun i : Fin regs.card ↦ f ≤ i.val ∧ i.val < regs.card - f ∧
        ((net.exec (w ∘ regs.orderEmbOfFin rfl) i).val < anc.lo ∨
          anc.hi ≤ (net.exec
            (w ∘ regs.orderEmbOfFin rfl) i).val))).card := by
    unfold Bag.strangers
    rw [hmiddle, filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [hstrange, hview]
    tauto
  rw [hcount] at hs
  rw [houtput, hcount]
  exact supported_injective_interval
    (supported_separator_mono_fringe hsmall hf)
    (w ∘ regs.orderEmbOfFin rfl) (hw.comp (regs.orderEmbOfFin rfl).injective)
    anc.lo anc.hi anc.lo_lt_hi.le hs

theorem bagSeparator_filters {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (hdvd : 32 ∣ regs.card) (f : ℕ) (hf : regs.card / 32 ≤ f)
    (hhalf : f ≤ regs.card / 2)
    (w w' : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hview : ∀ i, w' (regs.orderEmbOfFin rfl i) =
      (separatorNetwork regs.card).exec (w ∘ regs.orderEmbOfFin rfl) i)
    (b : Bag k) (j : ℕ) (hj : 1 ≤ j)
    (hs : (b.strangers j w regs : ℝ) ≤ (patersonMu : ℝ) * regs.card) :
    (b.strangers j w' ((split regs f).toLeft ∪ (split regs f).toRight) : ℝ) ≤
      (patersonTailError : ℝ) * b.strangers j w regs :=
  bagNetwork_filters regs (dvd_trans (by norm_num) hdvd) (separatorNetwork regs.card)
    (separatorNetwork_certificate_of_dvd32 _ hdvd).1 f hf hhalf w w' hw hview b j hj hs

end Bags
end Paterson
