module

public import AKS.Halver.Paterson
public import AKS.Halver.FromExpander

/-! # From matching expansion to restricted halvers

The deterministic part of Paterson's argument: a set of misplaced extreme
values would force every matching to carry a small set into another small set.
Ruling out those traps proves the halver property.
-/

@[expose] public section

open Finset

namespace Paterson

/-- Both orientations of the matching graph escape every possible bad pair
of small vertex sets. -/
def HasNoSmallTraps {m : ℕ} (gs : List (Equiv.Perm (Fin m))) (ε α : ℚ) : Prop :=
  ∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m →
    ∀ X Y : Finset (Fin m), (ε : ℝ) * k < X.card → X.card + Y.card ≤ k →
      (∃ g ∈ gs, ∃ x ∈ X, g x ∉ Y) ∧
      (∃ g ∈ gs, ∃ x ∈ X, g.symm x ∉ Y)

/-- Every comparison used by a matching network crosses the two halves. -/
theorem matchingNetwork_bipartite {m : ℕ} (gs : List (Equiv.Perm (Fin m)))
    (c : Comparator (2 * m)) (hc : c ∈ (patersonMatchingNetwork gs).comparators) :
    c.i.val < m ∧ m ≤ c.j.val := by
  simp only [patersonMatchingNetwork, List.mem_flatMap, patersonMatchingLayer,
    List.mem_ofFn] at hc
  obtain ⟨g, _, i, rfl⟩ := hc
  exact ⟨i.isLt, Nat.le_add_right m _⟩

/-- All matching edges are ordered at the end of the network, including
edges used before the last layer. -/
theorem matchingNetwork_edge_order {m : ℕ} {V : Type*} [LinearOrder V]
    (gs : List (Equiv.Perm (Fin m))) (w : Fin (2 * m) → V)
    (g : Equiv.Perm (Fin m)) (hg : g ∈ gs) (i : Fin m) :
    (patersonMatchingNetwork gs).exec w ⟨i.val, by omega⟩ ≤
      (patersonMatchingNetwork gs).exec w ⟨m + (g i).val, by omega⟩ := by
  apply foldl_member_order (patersonMatchingNetwork gs).comparators
    (patersonMatchingComparator g i) _ (matchingNetwork_bipartite gs) w
  simp only [patersonMatchingNetwork, List.mem_flatMap, patersonMatchingLayer,
    List.mem_ofFn]
  exact ⟨g, hg, i, rfl⟩

/-- Bottom-half counting in the local `Fin m` coordinates. -/
theorem card_filter_bottom_half {m : ℕ} (P : Fin (2 * m) → Prop)
    [DecidablePred P] :
    (univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ P i)).card =
      (univ.filter (fun i : Fin m => P ⟨m + i.val, by omega⟩)).card := by
  have htotal := card_filter_fin_double P
  have hsplit := card_filter_add_card_filter_not
    (fun i : Fin (2 * m) => i.val < m) (s := univ.filter P)
  have htop := card_filter_top_half P
  simp only [filter_filter] at hsplit htop
  have heq : (univ.filter (fun i : Fin (2 * m) => P i ∧ i.val < m)) =
      (univ.filter (fun i : Fin (2 * m) => i.val < m ∧ P i)) := by
    ext i
    simp [and_comm]
  have heq' : (univ.filter (fun i : Fin (2 * m) => P i ∧ ¬i.val < m)) =
      (univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ P i)) := by
    ext i
    simp [and_comm]
  rw [heq, heq', htop, htotal] at hsplit
  omega

/-- The absence of small traps gives both directional restricted-halver
guarantees. This is the deterministic implication used by the random-matching
existence proof. -/
theorem isHalver_of_noSmallTraps {m : ℕ} (gs : List (Equiv.Perm (Fin m)))
    {ε α : ℚ} (hα : α ≤ 1) (h : HasNoSmallTraps gs ε α) :
    IsEpsilonAlphaHalver (patersonMatchingNetwork gs) ε α := by
  intro v
  let w := (patersonMatchingNetwork gs).exec (v : Fin (2 * m) → Fin (2 * m))
  have hkm : ∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m → k ≤ m := by
    intro k hk
    have ha : (α : ℝ) ≤ 1 := by exact_mod_cast hα
    have hm : (k : ℝ) ≤ m := by
      calc
        (k : ℝ) ≤ (α : ℝ) * m := hk
        _ ≤ 1 * m := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg m)
        _ = m := one_mul _
    exact_mod_cast hm
  have hcount : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) => (w i).val < k)).card = k := by
    intro k hk
    exact exec_perm_card_lt (patersonMatchingNetwork gs) v k hk
  constructor
  · intro k hk
    let L := univ.filter (fun i : Fin m => (w ⟨i.val, by omega⟩).val < k)
    let R := univ.filter (fun i : Fin m => (w ⟨m + i.val, by omega⟩).val < k)
    have hcard : R.card + L.card = k := by
      have ht := hcount k (by have := hkm k hk; omega)
      rw [card_filter_fin_double] at ht
      change L.card + R.card = k at ht
      omega
    change ((univ.filter (fun i : Fin (2 * m) =>
      m ≤ i.val ∧ (w i).val < k)).card : ℝ) ≤ (ε : ℝ) * k
    rw [card_filter_bottom_half]
    change (R.card : ℝ) ≤ (ε : ℝ) * k
    by_contra hfail
    obtain ⟨g, hg, x, hx, hxy⟩ :=
      (h k hk R L (lt_of_not_ge hfail) hcard.le).2
    have hx' : (w ⟨m + x.val, by omega⟩).val < k := by
      simpa only [R, mem_filter, mem_univ, true_and] using hx
    have he := matchingNetwork_edge_order gs (v : Fin (2 * m) → Fin (2 * m))
      g hg (g.symm x)
    simp only [Equiv.apply_symm_apply] at he
    apply hxy
    simp only [L, mem_filter, mem_univ, true_and]
    exact lt_of_le_of_lt (show (w ⟨(g.symm x).val, by omega⟩).val ≤
      (w ⟨m + x.val, by omega⟩).val from he) hx'
  · intro k hk
    let L := univ.filter (fun i : Fin m => 2 * m - k ≤ (w ⟨i.val, by omega⟩).val)
    let R := univ.filter (fun i : Fin m => 2 * m - k ≤ (w ⟨m + i.val, by omega⟩).val)
    have htotal : (univ.filter (fun i : Fin (2 * m) =>
        2 * m - k ≤ (w i).val)).card = k := by
      have hc := hcount (2 * m - k) (by omega)
      have hs := card_filter_add_card_filter_not
        (fun i : Fin (2 * m) => (w i).val < 2 * m - k) (s := univ)
      simp only [not_lt, card_univ, Fintype.card_fin] at hs
      have := hkm k hk
      omega
    have hcard : L.card + R.card = k := by
      rw [card_filter_fin_double] at htotal
      exact htotal
    change ((univ.filter (fun i : Fin (2 * m) =>
      i.val < m ∧ 2 * m - k ≤ (w i).val)).card : ℝ) ≤ (ε : ℝ) * k
    have htop := card_filter_top_half (fun i : Fin (2 * m) =>
      2 * m - k ≤ (w i).val)
    simp only [filter_filter] at htop
    rw [htop]
    change (L.card : ℝ) ≤ (ε : ℝ) * k
    by_contra hfail
    obtain ⟨g, hg, x, hx, hxy⟩ :=
      (h k hk L R (lt_of_not_ge hfail) hcard.le).1
    have hx' : 2 * m - k ≤ (w ⟨x.val, by omega⟩).val := by
      simpa only [L, mem_filter, mem_univ, true_and] using hx
    have he := matchingNetwork_edge_order gs (v : Fin (2 * m) → Fin (2 * m)) g hg x
    apply hxy
    simp only [R, mem_filter, mem_univ, true_and]
    exact le_trans hx' (show (w ⟨x.val, by omega⟩).val ≤
      (w ⟨m + (g x).val, by omega⟩).val from he)

end Paterson
