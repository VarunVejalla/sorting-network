module

public import AKS.Paterson.StoredFresh

/-! # Mixed-network supported and large-cohort source estimates -/

@[expose] public section

namespace Paterson.Bags

open Finset

def FirstContract {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ m (h : n = 2 * m), IsEpsilonAlphaHalver (h ▸ net) patersonDelta0 patersonAlpha0

theorem even_middle_left {n ambient f : ℕ} (heven : 2 ∣ n)
    {net : ComparatorNetwork n} {support err : ℝ}
    (hsmall : IsSupportedSeparator net f support err) (hgood : FirstContract net)
    (u : Fin n → Fin ambient) (hu : Function.Injective u) (lo hi r : ℕ)
    (hlo : ((univ.filter (fun i ↦ (u i).val < lo)).card : ℝ) ≤ support * n)
    (hr : r ≤ n) (hb : r ≤ (univ.filter (fun i ↦ (u i).val < hi)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * (n / 2 : ℕ)) :
    ((univ.filter (fun i ↦ f ≤ i.val ∧ i.val < n / 2 ∧
      ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val))).card : ℝ) ≤
      err * (univ.filter (fun i ↦ (u i).val < lo)).card +
        ((n / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  obtain ⟨m, rfl⟩ := heven
  simpa using middle_left_strangers hsmall (hgood m rfl) u hu lo hi r (by simpa using hlo) hr hb
    (by simpa using hs)

theorem even_middle_right {n ambient f : ℕ} (heven : 2 ∣ n)
    {net : ComparatorNetwork n} {support err : ℝ}
    (hsmall : IsSupportedSeparator net f support err) (hgood : FirstContract net)
    (u : Fin n → Fin ambient) (hu : Function.Injective u) (lo hi r : ℕ)
    (hhi : ((univ.filter (fun i ↦ hi ≤ (u i).val)).card : ℝ) ≤ support * n)
    (ht : lo ≤ ambient) (hr : r ≤ n)
    (hb : r ≤ (univ.filter (fun i ↦ lo ≤ (u i).val)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * (n / 2 : ℕ)) :
    ((univ.filter (fun i ↦ n / 2 ≤ i.val ∧ i.val < n - f ∧
      ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val))).card : ℝ) ≤
      err * (univ.filter (fun i ↦ hi ≤ (u i).val)).card +
        ((n / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  obtain ⟨m, rfl⟩ := heven
  simpa using middle_right_strangers hsmall (hgood m rfl) u hu lo hi r (by simpa using hhi) ht hr hb
    (by simpa using hs)


theorem supported_left_interval {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card)
    (parent : Bag k)
    (heven : 2 ∣ (pl.regs parent).card) (f : ℕ)
    {support err : ℝ}
    (hsmall : IsSupportedSeparator (nets parent) f support err)
    (hgood : FirstContract (nets parent))
    (hhalf : f ≤ (pl.regs parent).card / 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) (lo hi r : ℕ)
    (hlo : (((pl.regs parent).filter (fun i ↦ (w i).val < lo)).card : ℝ) ≤
      support * (pl.regs parent).card)
    (hr : r ≤ (pl.regs parent).card)
    (hbalance : r ≤ ((pl.regs parent).filter (fun i ↦ (w i).val < hi)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs parent).card / 2 : ℕ)) :
    ((((split (pl.regs parent) f).toLeft).filter (fun i ↦
      ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card : ℝ) ≤
      err *
        ((pl.regs parent).filter (fun i ↦ (w i).val < lo)).card +
      (((pl.regs parent).card / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  let regs := pl.regs parent
  let emb := regs.orderEmbOfFin rfl
  have hhalf' : f ≤ regs.card / 2 := hhalf
  have hout :
      (((split regs f).toLeft).filter (fun i ↦
        ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card =
      (univ.filter (fun i : Fin regs.card ↦ f ≤ i.val ∧ i.val < regs.card / 2 ∧
        (((nets parent).exec (w ∘ emb) i).val < lo ∨
          hi ≤ ((nets parent).exec (w ∘ emb) i).val))).card := by
    change (((univ.filter (fun i : Fin regs.card ↦
      f ≤ i.val ∧ i.val < f + (regs.card / 2 - f))).image emb).filter _).card = _
    rw [filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [pl.compare_exec_view nets parent]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    rw [heq]
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hlo hbalance
  exact even_middle_left heven hsmall hgood (w ∘ emb) (hw.comp emb.injective)
    lo hi r hlo hr hbalance hs

theorem supported_right_interval {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card)
    (parent : Bag k)
    (heven : 2 ∣ (pl.regs parent).card) (f : ℕ)
    {support err : ℝ}
    (hsmall : IsSupportedSeparator (nets parent) f support err)
    (hgood : FirstContract (nets parent))
    (hhalf : f ≤ (pl.regs parent).card / 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) (lo hi r : ℕ)
    (hhi : (((pl.regs parent).filter (fun i ↦ hi ≤ (w i).val)).card : ℝ) ≤
      support * (pl.regs parent).card)
    (ht : lo ≤ 2 ^ k) (hr : r ≤ (pl.regs parent).card)
    (hbalance : r ≤ ((pl.regs parent).filter (fun i ↦ lo ≤ (w i).val)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs parent).card / 2 : ℕ)) :
    ((((split (pl.regs parent) f).toRight).filter (fun i ↦
      ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card : ℝ) ≤
      err *
        ((pl.regs parent).filter (fun i ↦ hi ≤ (w i).val)).card +
      (((pl.regs parent).card / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  let regs := pl.regs parent
  let emb := regs.orderEmbOfFin rfl
  have hhalf' : f ≤ regs.card / 2 := hhalf
  have hcard : 2 * (regs.card / 2) = regs.card := Nat.mul_div_cancel' heven
  have hout :
      (((split regs f).toRight).filter (fun i ↦
        ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card =
      (univ.filter (fun i : Fin regs.card ↦ regs.card / 2 ≤ i.val ∧ i.val < regs.card - f ∧
        (((nets parent).exec (w ∘ emb) i).val < lo ∨
          hi ≤ ((nets parent).exec (w ∘ emb) i).val))).card := by
    change (((univ.filter (fun i : Fin regs.card ↦
      f + (regs.card / 2 - f) ≤ i.val ∧ i.val < f + 2 * (regs.card / 2 - f))).image
      emb).filter _).card = _
    rw [filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [pl.compare_exec_view nets parent]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    have heq' : f + 2 * (regs.card / 2 - f) = regs.card - f := by omega
    rw [heq, heq']
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hhi hbalance
  exact even_middle_right heven hsmall hgood (w ∘ emb) (hw.comp emb.injective)
    lo hi r hhi ht hr hbalance hs

end Paterson.Bags
