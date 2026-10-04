module

public import AKS.Kahale.RankInterval
public import Mathlib.Order.Interval.Finset.Fin

/-! # Rank covers imply approximate selection

The interval lemma converts a bound on the number of attainable ranks into
a positional displacement bound. A suffix of `s` parallel layers will supply
a rank cover of cardinality at most `2^s`; that fan-out bridge is separate.
-/

@[expose] public section

namespace Kahale

open Finset

def ApproxSelect {n : ℕ} (net : ComparatorNetwork n) (t slack : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ i,
    ((net.exec σ i).val < t → i.val < t + slack) ∧
    (t ≤ (net.exec σ i).val → t ≤ i.val + slack)

theorem rank_interval_card_le {n : ℕ} (net : ComparatorNetwork n) (wire : Fin n)
    (R : Finset (Fin n))
    (hR : ∀ σ : Equiv.Perm (Fin n), net.exec σ wire ∈ R)
    (σ τ : Equiv.Perm (Fin n)) :
    (net.exec τ wire).val + 1 - (net.exec σ wire).val ≤ R.card := by
  have hsub : Icc (net.exec σ wire) (net.exec τ wire) ⊆ R := by
    intro k hk
    obtain ⟨π, hp⟩ := wire_rank_interval net wire k σ τ (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    rw [← hp]
    exact hR π
  simpa only [Fin.card_Icc] using card_le_card hsub

theorem rank_cover_displacement {n B : ℕ} (net : ComparatorNetwork n) (wire : Fin n)
    (R : Finset (Fin n))
    (hR : ∀ σ : Equiv.Perm (Fin n), net.exec σ wire ∈ R) (hB : R.card ≤ B)
    (σ : Equiv.Perm (Fin n)) :
    (net.exec σ wire).val < wire.val + B ∧ wire.val < (net.exec σ wire).val + B := by
  have hid : net.exec (Equiv.refl (Fin n)) wire = wire := by
    have he := net.exec_eq_of_monotone (v := id) monotone_id
    exact congrFun he wire
  have h₁ := rank_interval_card_le net wire R hR (Equiv.refl _) σ
  have h₂ := rank_interval_card_le net wire R hR σ (Equiv.refl _)
  rw [hid] at h₁ h₂
  have hpos : 0 < R.card := card_pos.mpr ⟨wire, hid ▸ hR (Equiv.refl _)⟩
  omega

theorem rank_covers_approx_select {n B : ℕ} (net : ComparatorNetwork n)
    (R : Fin n → Finset (Fin n))
    (hR : ∀ i, ∀ σ : Equiv.Perm (Fin n), net.exec σ i ∈ R i)
    (hB : ∀ i, (R i).card ≤ B) (t : ℕ) : ApproxSelect net t B := by
  intro σ i
  have hh := rank_cover_displacement net i (R i) (hR i) (hB i) σ
  constructor <;> intro h <;> omega

end Kahale
