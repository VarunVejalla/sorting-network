module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Counting constrained perfect matchings

A perfect bipartite matching is a permutation. The basic event in Paterson's
existence argument asks that a fixed set of left vertices be mapped into a
fixed set of right vertices. We count this event by first choosing the
restricted injection, then an injection into the unused vertices.
-/

@[expose] public section

open Finset
open scoped Classical

namespace Paterson

/-- Count embeddings on a disjoint union whose first part lands in `Y`. -/
theorem card_restricted_sum_embeddings
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (Y : Finset C) :
    Fintype.card {f : A ⊕ B ↪ C // ∀ a, f (Sum.inl a) ∈ Y} =
      Y.card.descFactorial (Fintype.card A) *
        (Fintype.card C - Fintype.card A).descFactorial (Fintype.card B) := by
  classical
  let e := (Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted :
    (A ⊕ B ↪ C) ≃ Σ f : A ↪ C, B ↪ ↥(Set.range f)ᶜ)
  let p := fun f : A ↪ C => B ↪ ↥(Set.range f)ᶜ
  let q := fun f : A ↪ C => ∀ a, f a ∈ Y
  have hc : Fintype.card {f : A ⊕ B ↪ C // ∀ a, f (Sum.inl a) ∈ Y} =
      Fintype.card (Σ f : {f : A ↪ C // q f}, p f.val) := by
    apply Fintype.card_congr
    exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
      (Equiv.subtypeSigmaEquiv p q)
  rw [hc, Fintype.card_sigma]
  have hf : ∀ f : {f : A ↪ C // q f}, Fintype.card (p f.val) =
      (Fintype.card C - Fintype.card A).descFactorial (Fintype.card B) := by
    intro f
    change Fintype.card (B ↪ ↥(Set.range f.val)ᶜ) = _
    rw [Fintype.card_embedding_eq, Fintype.card_compl_set,
      Fintype.card_range f.val]
  simp_rw [hf]
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul]
  congr 1
  calc
    Fintype.card {f : A ↪ C // q f} = Fintype.card (A ↪ ↥Y) :=
      Fintype.card_congr (Equiv.codRestrict A (Y : Set C))
    _ = Y.card.descFactorial (Fintype.card A) := by simp

/-- Exact count of perfect matchings carrying `X` into `Y`. The expression
uses a descending factorial so it also covers the impossible case `|Y| < |X|`.
-/
theorem card_restricted_permutations {A : Type*} [Fintype A]
    (X Y : Finset A) :
    Fintype.card {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y} =
      Y.card.descFactorial X.card * (Fintype.card A - X.card).factorial := by
  classical
  let e : Equiv.Perm A ≃ (↥X ⊕ ↥(X : Set A)ᶜ ↪ A) :=
    (Equiv.embeddingEquivOfFinite A).symm.trans
      (Equiv.embeddingCongr (Equiv.Set.sumCompl (X : Set A)).symm (Equiv.refl A))
  have hc : Fintype.card {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y} =
      Fintype.card {f : ↥X ⊕ ↥(X : Set A)ᶜ ↪ A //
        ∀ x, f (Sum.inl x) ∈ Y} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv e
    intro g
    change (∀ x ∈ X, g x ∈ Y) ↔ (∀ x : X, g x.val ∈ Y)
    exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  rw [hc, card_restricted_sum_embeddings]
  simp only [Fintype.card_coe, Fintype.card_compl_set, Finset.coe_sort_coe,
    Nat.descFactorial_self]

/-- Sampling without replacement is no more likely to stay inside a fixed
subset than independent sampling with replacement. Written without division,
the inequality remains valid at zero and for all sample sizes. -/
theorem descFactorial_ratio_le_pow (m b r : ℕ) (hb : b ≤ m) :
    m ^ r * b.descFactorial r ≤ b ^ r * m.descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hr : r ≤ b
    · have hrm : r ≤ m := hr.trans hb
      have hstep : m * (b - r) ≤ b * (m - r) := by
        have hbr : b - r + r = b := Nat.sub_add_cancel hr
        have hmr : m - r + r = m := Nat.sub_add_cancel hrm
        nlinarith
      calc
        m ^ (r + 1) * b.descFactorial (r + 1) =
            (m ^ r * b.descFactorial r) * (m * (b - r)) := by
              rw [Nat.descFactorial_succ, pow_succ]
              ring
        _ ≤ (b ^ r * m.descFactorial r) * (b * (m - r)) :=
          Nat.mul_le_mul ih hstep
        _ = b ^ (r + 1) * m.descFactorial (r + 1) := by
          rw [Nat.descFactorial_succ, pow_succ]
          ring
    · have hz : b.descFactorial (r + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz, Nat.mul_zero]
      exact Nat.zero_le _

/-- The one-matching probability estimate, with denominators cleared. -/
theorem card_restricted_permutations_mul_pow_le {A : Type*} [Fintype A]
    (X Y : Finset A) :
    Fintype.card {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y} *
        Fintype.card A ^ X.card ≤
      (Fintype.card A).factorial * Y.card ^ X.card := by
  classical
  have hratio := descFactorial_ratio_le_pow (Fintype.card A) Y.card X.card
    (Finset.card_le_univ Y)
  have hfactor := Nat.factorial_mul_descFactorial (Finset.card_le_univ X)
  rw [card_restricted_permutations]
  calc
    Y.card.descFactorial X.card * (Fintype.card A - X.card).factorial *
        Fintype.card A ^ X.card =
      (Fintype.card A - X.card).factorial *
        (Fintype.card A ^ X.card * Y.card.descFactorial X.card) := by ring
    _ ≤ (Fintype.card A - X.card).factorial *
        (Y.card ^ X.card * (Fintype.card A).descFactorial X.card) :=
      Nat.mul_le_mul_left _ hratio
    _ = (Fintype.card A).factorial * Y.card ^ X.card := by
      rw [mul_left_comm, hfactor]
      exact Nat.mul_comm _ _

/-- Independent choices of matching layers raise the exact event count to
the number of layers. -/
theorem card_restricted_matching_sequences {A : Type*} [Fintype A]
    (X Y : Finset A) (c : ℕ) :
    Fintype.card {gs : Fin c → Equiv.Perm A // ∀ i, ∀ x ∈ X, gs i x ∈ Y} =
      (Y.card.descFactorial X.card * (Fintype.card A - X.card).factorial) ^ c := by
  classical
  calc
    _ = Fintype.card (Fin c → {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by rw [Fintype.card_fun, Fintype.card_fin, card_restricted_permutations]

/-- Total number of `c`-layer bipartite matching networks on two copies of A. -/
theorem card_matching_sequences (A : Type*) [Fintype A] (c : ℕ) :
    Fintype.card (Fin c → Equiv.Perm A) = (Fintype.card A).factorial ^ c := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_perm]

/-- For uniformly chosen perfect matchings, the chance that every edge out
of `X` lands in `Y` is at most `(|Y| / |A|)^|X|`. -/
theorem restricted_matching_density_le {A : Type*} [Fintype A]
    (X Y : Finset A) (hm : 0 < Fintype.card A) :
    (Fintype.card {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y} : ℚ) /
        (Fintype.card A).factorial ≤
      ((Y.card : ℚ) / Fintype.card A) ^ X.card := by
  have hmQ : (0 : ℚ) < Fintype.card A := by exact_mod_cast hm
  have hfQ : (0 : ℚ) < (Fintype.card A).factorial := by
    exact_mod_cast Nat.factorial_pos (Fintype.card A)
  rw [div_pow]
  apply (div_le_div_iff₀ hfQ (pow_pos hmQ _)).mpr
  have h := card_restricted_permutations_mul_pow_le X Y
  rw [Nat.mul_comm (Fintype.card A).factorial] at h
  exact_mod_cast h

/-- The corresponding density bound for `c` independent matching layers.
This is the per-event estimate in the finite union bound. -/
theorem restricted_matching_sequence_density_le {A : Type*} [Fintype A]
    (X Y : Finset A) (c : ℕ) (hm : 0 < Fintype.card A) :
    (Fintype.card {gs : Fin c → Equiv.Perm A // ∀ i, ∀ x ∈ X, gs i x ∈ Y} : ℚ) /
        Fintype.card (Fin c → Equiv.Perm A) ≤
      ((Y.card : ℚ) / Fintype.card A) ^ (X.card * c) := by
  have h := restricted_matching_density_le X Y hm
  have hn : (0 : ℚ) ≤
    (Fintype.card {g : Equiv.Perm A // ∀ x ∈ X, g x ∈ Y} : ℚ) /
      (Fintype.card A).factorial := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp := pow_le_pow_left₀ hn h c
  rw [card_restricted_permutations] at hp
  simpa only [card_restricted_matching_sequences, card_matching_sequences,
    Nat.cast_pow, div_pow, pow_mul] using hp

/-- Inverting every matching preserves its uniform distribution. Thus the
same density estimate applies to traps in the opposite orientation. -/
theorem inverse_matching_sequence_density_le {A : Type*} [Fintype A]
    (X Y : Finset A) (c : ℕ) (hm : 0 < Fintype.card A) :
    (Fintype.card {gs : Fin c → Equiv.Perm A //
      ∀ i, ∀ x ∈ X, (gs i).symm x ∈ Y} : ℚ) /
        Fintype.card (Fin c → Equiv.Perm A) ≤
      ((Y.card : ℚ) / Fintype.card A) ^ (X.card * c) := by
  let e : {gs : Fin c → Equiv.Perm A // ∀ i, ∀ x ∈ X, (gs i).symm x ∈ Y} ≃
      {gs : Fin c → Equiv.Perm A // ∀ i, ∀ x ∈ X, gs i x ∈ Y} := {
    toFun := fun gs => ⟨fun i => (gs.val i).symm, gs.property⟩
    invFun := fun gs => ⟨fun i => (gs.val i).symm, gs.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  exact restricted_matching_sequence_density_le X Y c hm

end Paterson
