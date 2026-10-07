module
/-
  # Chvátal Lemma 6.3 + (6.1) — Hoeffding bound for scrambles

  Source: V. Chvátal, Lecture Notes on the New AKS Sorting Network,
  Rutgers DCS-TR-294 (1992), §6.

  Status: kernel-checked combinatorial fiber/average/count lemmas, hypergeometric→binomial
  row MGF, Bernoulli Hoeffding, scramble product Chernoff, and `lemma63ExpBound`.
-/

public import AKS.Chvatal.Lemma61
public import AKS.Halver.MatchingCount
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

namespace Chvatal

/-! ## Row hits -/

def rowHit {m n : Nat} (c : MonotoneColumnSums m n)
    (S : Finset (Fin n)) (r : Fin m) (π : Equiv.Perm (Fin n)) : ℕ :=
  (((monotoneRowOnes c r).image π) ∩ S).card

theorem onesInColumns_eq_sum_rowHit {m n : Nat}
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n) :
    onesInColumns c σ S = ∑ r : Fin m, rowHit c S r (σ r) := by
  simp [onesInColumns, rowHit, scrambledRowOnes]

theorem rowHit_le {m n : Nat} (c : MonotoneColumnSums m n)
    (S : Finset (Fin n)) (r : Fin m) (π : Equiv.Perm (Fin n)) :
    rowHit c S r π ≤ S.card :=
  Finset.card_le_card Finset.inter_subset_right

/-! ## Fiber counts -/

def permFiberEquiv {n : Nat} (a b1 b2 : Fin n) (τ : Equiv.Perm (Fin n))
    (hτ : τ b1 = b2) :
    {π : Equiv.Perm (Fin n) // π a = b1} ≃
      {π : Equiv.Perm (Fin n) // π a = b2} where
  toFun := fun ⟨π, hπ⟩ => ⟨π.trans τ, by simp [hπ, hτ]⟩
  invFun := fun ⟨π, hπ⟩ => ⟨π.trans τ.symm, by simp [← hτ, hπ]⟩
  left_inv := by intro ⟨π, _⟩; ext x; simp
  right_inv := by intro ⟨π, _⟩; ext x; simp

theorem card_perm_apply_eq {n : Nat} (a b : Fin n) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b).card * n =
      Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hfiber (b1 b2 : Fin n) :
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b1).card =
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b2).card := by
    obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), τ b1 = b2 :=
      ⟨Equiv.swap b1 b2, Equiv.swap_apply_left _ _⟩
    simpa [Fintype.card_subtype] using
      Fintype.card_congr (permFiberEquiv a b1 b2 τ hτ)
  have hdisj (b1 b2 : Fin n) (hne : b1 ≠ b2) :
      Disjoint
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b1)
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b2) := by
    refine Finset.disjoint_left.2 fun π h1 h2 => ?_
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hcover :
      (Finset.univ.biUnion fun b' : Fin n =>
        Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b') =
        (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
    ext π; simp
  have hsum :
      ∑ b' : Fin n,
          (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a = b').card =
        Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← Finset.card_biUnion (fun b1 _ b2 _ h => hdisj b1 b2 h), hcover,
      Finset.card_univ]
  simp_rw [hfiber _ b] at hsum
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, Fintype.card_fin] using hsum

theorem card_perm_hit {n : Nat} (A : Finset (Fin n)) (j : Fin n) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) => j ∈ A.image π).card * n =
      A.card * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hEq :
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) => j ∈ A.image π) =
        A.biUnion fun a => Finset.univ.filter fun π => π a = j := by
    ext π; simp [Finset.mem_image]
  rw [hEq]
  have hdisj : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 →
      Disjoint
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a1 = j)
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π a2 = j) := by
    intro a1 _ a2 _ hne
    refine Finset.disjoint_left.2 fun π h1 h2 => ?_
    have h1' : π a1 = j := (Finset.mem_filter.mp h1).2
    have h2' : π a2 = j := (Finset.mem_filter.mp h2).2
    exact hne (π.injective (h1'.trans h2'.symm))
  rw [Finset.card_biUnion hdisj, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun a _ => card_perm_apply_eq a j).trans ?_
  simp [Finset.sum_const]

theorem avg_rowHit {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (r : Fin m) :
    (∑ π : Equiv.Perm (Fin n), (rowHit c S r π : ℝ)) /
        Fintype.card (Equiv.Perm (Fin n)) =
      ((monotoneRowOnes c r).card : ℝ) * S.card / n := by
  classical
  have htot : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum :
      ∑ π : Equiv.Perm (Fin n), (rowHit c S r π : ℝ) =
        ∑ j ∈ S,
          ((Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
              j ∈ (monotoneRowOnes c r).image π).card : ℝ) := by
    calc ∑ π : Equiv.Perm (Fin n), (rowHit c S r π : ℝ)
        = ∑ π : Equiv.Perm (Fin n),
            ∑ j ∈ S, (if j ∈ (monotoneRowOnes c r).image π then (1 : ℝ) else 0) := by
              refine Fintype.sum_congr _ _ fun π => ?_
              simp only [rowHit]
              rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_boole]
      _ = ∑ j ∈ S, ∑ π : Equiv.Perm (Fin n),
            (if j ∈ (monotoneRowOnes c r).image π then (1 : ℝ) else 0) :=
              Finset.sum_comm
      _ = ∑ j ∈ S,
            ((Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
                j ∈ (monotoneRowOnes c r).image π).card : ℝ) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp [Finset.sum_boole]
  have hhit (j : Fin n) :
      ((Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
          j ∈ (monotoneRowOnes c r).image π).card : ℝ) =
        ((monotoneRowOnes c r).card : ℝ) *
          Fintype.card (Equiv.Perm (Fin n)) / n := by
    have h := congrArg (fun x : ℕ => (x : ℝ))
      (card_perm_hit (monotoneRowOnes c r) j)
    push_cast at h
    field_simp [hn0] at h ⊢
    linarith
  rw [hsum]; simp_rw [hhit]
  simp [Finset.sum_const]
  field_simp [htot, hn0]

theorem sum_avg_rowHit {m n : Nat} (hn : 0 < n) (hm : 0 < m)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) :
    let p := (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)
    ∑ r : Fin m,
        (∑ π : Equiv.Perm (Fin n), (rowHit c S r π : ℝ)) /
          Fintype.card (Equiv.Perm (Fin n)) =
      p * m * S.card := by
  intro p
  simp_rw [avg_rowHit hn c S]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h :
      ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) * S.card / n =
        ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) * S.card) / n := by
    simp_rw [mul_div_assoc, ← Finset.sum_mul]
  rw [h]
  change ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) * S.card) / n =
    ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)) * m * S.card
  field_simp [hm0, hn0]

/-! ## Containing a fixed image set -/

theorem mem_filter_supset_image_iff {n : Nat}
    (A T : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    T ⊆ A.image π ↔ ∀ t ∈ T, π.symm t ∈ A := by
  constructor
  · intro h t ht
    rcases Finset.mem_image.mp (h ht) with ⟨a, ha, hπ⟩
    have : π.symm t = a := by rw [← hπ, Equiv.symm_apply_apply]
    exact this ▸ ha
  · intro h t ht
    exact Finset.mem_image.mpr ⟨π.symm t, h t ht, Equiv.apply_symm_apply π t⟩

theorem card_perm_maps_into {n : Nat} (A T : Finset (Fin n)) :
    Fintype.card {π : Equiv.Perm (Fin n) // ∀ t ∈ T, π t ∈ A} =
      A.card.descFactorial T.card * (n - T.card).factorial := by
  classical
  convert Paterson.card_restricted_permutations T A using 2
  simp [Fintype.card_fin]

theorem card_perm_supset_image {n : Nat} (A T : Finset (Fin n)) :
    Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} =
      A.card.descFactorial T.card * (n - T.card).factorial := by
  classical
  refine (Fintype.card_congr ?e).trans (card_perm_maps_into A T)
  exact {
    toFun := fun ⟨π, h⟩ =>
      ⟨π.symm, fun t ht => (mem_filter_supset_image_iff A T π).mp h t ht⟩
    invFun := fun ⟨π, h⟩ =>
      ⟨π.symm, fun t ht =>
        Finset.mem_image.mpr ⟨π t, h t ht, Equiv.symm_apply_apply π t⟩⟩
    left_inv := by intro ⟨π, _⟩; simp
    right_inv := by intro ⟨π, _⟩; simp
  }

/-! ## Falling-factorial moments -/

theorem powersetCard_filter_subset_image {n : Nat}
    (A S : Finset (Fin n)) (k : Nat) (π : Equiv.Perm (Fin n)) :
    ((Finset.powersetCard k S).filter fun T => T ⊆ A.image π) =
      Finset.powersetCard k ((A.image π) ∩ S) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
  constructor
  · intro ⟨⟨hS, hc⟩, hA⟩
    exact ⟨⟨hA, hS⟩, hc⟩
  · intro ⟨⟨hA, hS⟩, hc⟩
    exact ⟨⟨hS, hc⟩, hA⟩

theorem sum_hit_choose {n : Nat} (A S : Finset (Fin n)) (k : Nat) :
    ∑ π : Equiv.Perm (Fin n), (((A.image π) ∩ S).card.choose k) =
      S.card.choose k * A.card.descFactorial k * (n - k).factorial := by
  classical
  have h1 :
      ∑ π : Equiv.Perm (Fin n), (((A.image π) ∩ S).card.choose k) =
        ∑ π : Equiv.Perm (Fin n),
          ((Finset.powersetCard k S).filter fun T => T ⊆ A.image π).card := by
    refine Fintype.sum_congr _ _ fun π => ?_
    rw [← Finset.card_powersetCard, ← powersetCard_filter_subset_image]
  have h2 :
      ∑ π : Equiv.Perm (Fin n),
          ((Finset.powersetCard k S).filter fun T => T ⊆ A.image π).card =
        ∑ T ∈ Finset.powersetCard k S,
          Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} := by
    -- Expand via ℝ to avoid Nat-ite pitfalls
    have hL :
        ((∑ π : Equiv.Perm (Fin n),
            (((Finset.powersetCard k S).filter fun T =>
                T ⊆ A.image π).card : ℝ))) =
          ∑ T ∈ Finset.powersetCard k S,
            ∑ π : Equiv.Perm (Fin n),
              (if T ⊆ A.image π then (1 : ℝ) else 0) := by
      calc ∑ π : Equiv.Perm (Fin n),
              ((((Finset.powersetCard k S).filter fun T =>
                  T ⊆ A.image π).card : ℝ))
          = ∑ π : Equiv.Perm (Fin n),
              ∑ T ∈ Finset.powersetCard k S,
                (if T ⊆ A.image π then (1 : ℝ) else 0) := by
                refine Fintype.sum_congr _ _ fun π => ?_
                simp [Finset.sum_boole]
        _ = ∑ T ∈ Finset.powersetCard k S, ∑ π : Equiv.Perm (Fin n),
              (if T ⊆ A.image π then (1 : ℝ) else 0) := Finset.sum_comm
    have hR :
        ∑ T ∈ Finset.powersetCard k S,
            ∑ π : Equiv.Perm (Fin n),
              (if T ⊆ A.image π then (1 : ℝ) else 0) =
          ∑ T ∈ Finset.powersetCard k S,
            (Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} : ℝ) := by
      refine Finset.sum_congr rfl fun T _ => ?_
      simp [Finset.sum_boole, Fintype.card_subtype]
    have hReal := hL.trans hR
    -- Cast the ℕ sums to ℝ and compare with `hReal`.
    have hEqR :
        ((∑ π : Equiv.Perm (Fin n),
            ((Finset.powersetCard k S).filter fun T =>
              T ⊆ A.image π).card : ℕ) : ℝ) =
          ((∑ T ∈ Finset.powersetCard k S,
              Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} : ℕ) : ℝ) := by
      calc ((∑ π : Equiv.Perm (Fin n),
                ((Finset.powersetCard k S).filter fun T =>
                  T ⊆ A.image π).card : ℕ) : ℝ)
          = ∑ π : Equiv.Perm (Fin n),
              ((((Finset.powersetCard k S).filter fun T =>
                  T ⊆ A.image π).card : ℝ)) := by simp
        _ = ∑ T ∈ Finset.powersetCard k S,
              (Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} : ℝ) := hReal
        _ = ((∑ T ∈ Finset.powersetCard k S,
                Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} : ℕ) : ℝ) := by
              simp
    exact_mod_cast hEqR
  rw [h1, h2]
  have hterm (T : Finset (Fin n)) (hT : T ∈ Finset.powersetCard k S) :
      Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} =
        A.card.descFactorial k * (n - k).factorial := by
    have hk : T.card = k := (Finset.mem_powersetCard.mp hT).2
    rw [← hk]
    exact card_perm_supset_image A T
  refine (Finset.sum_congr rfl fun T hT => hterm T hT).trans ?_
  simp [Finset.card_powersetCard, Finset.sum_const]
  ring

theorem avg_hit_descFactorial {n : Nat} (_hn : 0 < n) (A S : Finset (Fin n)) (k : Nat)
    (hk : k ≤ n) :
    (∑ π : Equiv.Perm (Fin n),
        (((A.image π) ∩ S).card.descFactorial k : ℝ)) /
      Fintype.card (Equiv.Perm (Fin n)) =
      ((S.card.descFactorial k : ℝ) * (A.card.descFactorial k : ℝ)) /
        (n.descFactorial k : ℝ) := by
  classical
  have hnfac : (n.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.mpr (not_lt.mpr hk)
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (n.factorial : ℝ) := by
    simp [Fintype.card_perm, Fintype.card_fin]
  have hsplit : (n.factorial : ℝ) =
      (n.descFactorial k : ℝ) * ((n - k).factorial : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.factorial_mul_descFactorial hk)
    push_cast at this; linarith
  have hS : (k.factorial : ℝ) * (S.card.choose k : ℝ) =
      (S.card.descFactorial k : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
  have hsum :
      ∑ π : Equiv.Perm (Fin n),
          (((A.image π) ∩ S).card.descFactorial k : ℝ) =
        (S.card.descFactorial k : ℝ) * (A.card.descFactorial k : ℝ) *
          ((n - k).factorial : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (sum_hit_choose A S k)
    push_cast at h
    calc ∑ π : Equiv.Perm (Fin n),
            ((((A.image π) ∩ S).card.descFactorial k : ℝ))
        = ∑ π : Equiv.Perm (Fin n),
            (k.factorial : ℝ) * ((((A.image π) ∩ S).card.choose k : ℝ)) := by
              refine Fintype.sum_congr _ _ fun π => ?_
              rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
      _ = (k.factorial : ℝ) *
            ∑ π : Equiv.Perm (Fin n),
              ((((A.image π) ∩ S).card.choose k : ℝ)) := by
              rw [Finset.mul_sum]
      _ = (k.factorial : ℝ) * ((S.card.choose k : ℝ) *
            (A.card.descFactorial k : ℝ) * ((n - k).factorial : ℝ)) := by
              rw [h]
      _ = ((k.factorial : ℝ) * (S.card.choose k : ℝ)) *
            (A.card.descFactorial k : ℝ) * ((n - k).factorial : ℝ) := by ring
      _ = (S.card.descFactorial k : ℝ) * (A.card.descFactorial k : ℝ) *
            ((n - k).factorial : ℝ) := by rw [hS]
  have htot : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  rw [hsum, hcard, hsplit]
  field_simp [htot, hnfac]

theorem avg_hit_descFactorial_le {n : Nat} (hn : 0 < n)
    (A S : Finset (Fin n)) (k : Nat) :
    (∑ π : Equiv.Perm (Fin n),
        (((A.image π) ∩ S).card.descFactorial k : ℝ)) /
      Fintype.card (Equiv.Perm (Fin n)) ≤
      (S.card.descFactorial k : ℝ) * ((A.card : ℝ) / n) ^ k := by
  classical
  by_cases hk : k ≤ n
  · have havg := avg_hit_descFactorial hn A S k hk
    have hratio := Paterson.descFactorial_ratio_le_pow n A.card k (by
      simpa [Fintype.card_fin] using Finset.card_le_univ A)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hdf : (n.descFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.mpr (not_lt.mpr hk)
    have hle :
        (A.card.descFactorial k : ℝ) / (n.descFactorial k : ℝ) ≤
          ((A.card : ℝ) / n) ^ k := by
      have h' : (n : ℝ) ^ k * (A.card.descFactorial k : ℝ) ≤
          (A.card : ℝ) ^ k * (n.descFactorial k : ℝ) := by exact_mod_cast hratio
      have hnden : (0 : ℝ) < (n.descFactorial k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero fun h => hdf (by exact_mod_cast h)
      have hnpow : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) _
      -- (A/n)^k = A^k / n^k
      rw [div_pow, div_le_div_iff₀ hnden hnpow]
      linarith [h']
    rw [havg]
    calc ((S.card.descFactorial k : ℝ) * (A.card.descFactorial k : ℝ)) /
            (n.descFactorial k : ℝ)
        = (S.card.descFactorial k : ℝ) *
            ((A.card.descFactorial k : ℝ) / (n.descFactorial k : ℝ)) := by
              field_simp [hdf]
      _ ≤ (S.card.descFactorial k : ℝ) * ((A.card : ℝ) / n) ^ k :=
            mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
  · have h0 :
        ∑ π : Equiv.Perm (Fin n),
            ((((A.image π) ∩ S).card.descFactorial k : ℝ)) = 0 := by
      refine Fintype.sum_eq_zero _ fun π => ?_
      have : ((A.image π) ∩ S).card < k := by
        have hle := Finset.card_le_univ ((A.image π) ∩ S)
        simp [Fintype.card_fin] at hle
        omega
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr this]
    have hnonneg : (0 : ℝ) ≤
        (S.card.descFactorial k : ℝ) * ((A.card : ℝ) / n) ^ k := by positivity
    simpa [h0] using hnonneg

/-! ## Bernoulli MGF (Hoeffding) -/

/-- Hoeffding bound for a Bernoulli trial: `(1-p+p e^t) ≤ exp(p t + t²/8)`. -/
theorem bernoulli_one_sub_add_mul_exp_le {prob t : ℝ} (hprob0 : 0 ≤ prob) (hprob1 : prob ≤ 1)
    (_ht : 0 ≤ t) :
    1 - prob + prob * Real.exp t ≤ Real.exp (prob * t + t ^ 2 / 8) := by
  open ProbabilityTheory MeasureTheory in
  by_cases hprob : prob = 0
  · subst hprob
    simp only [zero_mul, sub_zero, add_zero]
    exact Real.one_le_exp (by positivity)
  by_cases hprob1' : prob = 1
  · subst hprob1'
    simp only [one_mul, sub_self, zero_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [sq_nonneg t]
  have hprob_pos : 0 < prob := by
    by_contra h
    have : prob = 0 := le_antisymm (not_lt.mp h) hprob0
    exact hprob this
  let pnn : NNReal := ⟨prob, hprob0⟩
  have hpnn_le_one : pnn ≤ 1 := by exact_mod_cast hprob1
  let μ : Measure Bool := (PMF.bernoulli pnn hpnn_le_one).toMeasure
  haveI : IsProbabilityMeasure μ := inferInstance
  let X : Bool → ℝ := fun b => cond b 1 0
  have hm : AEMeasurable X μ := .of_discrete
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc 0 1 := by
    filter_upwards with b
    cases b <;> simp [X, Set.mem_Icc]
  have hEX : ∫ x, X x ∂μ = prob := by
    simpa [X, μ, pnn, hpnn_le_one] using PMF.bernoulli_expectation hpnn_le_one
  have hsub := hasSubgaussianMGF_of_mem_Icc hm hb
  have hcoeff : ((‖(1 : ℝ) - 0‖₊ / 2 : NNReal) ^ 2 : ℝ) * t ^ 2 / 2 = t ^ 2 / 8 := by
    have h₁ : (‖(1 : ℝ) - 0‖₊ / 2 : NNReal) = 1 / 2 := by ext; norm_num
    simp only [h₁]
    norm_num
    ring
  have hcent : mgf (fun b => X b - prob) μ t ≤ Real.exp (t ^ 2 / 8) := by
    have h := hsub.mgf_le t
    convert h using 1
    · congr 1
      funext b
      simp [hEX]
    · congr 1
      exact hcoeff.symm
  have hcenter_eq : (fun b => X b - prob) = fun b => X b + (-prob) := funext fun _ => by ring
  have hmgfX : mgf X μ t = 1 - prob + prob * Real.exp t := by
    simp only [mgf]
    rw [PMF.integral_eq_sum, Fintype.sum_bool]
    simp [X, PMF.bernoulli_apply, pnn, hpnn_le_one]
    ring
  have hshift : mgf (fun b => X b - prob) μ t = Real.exp (-prob * t) * mgf X μ t := by
    rw [hcenter_eq, mgf_add_const]
    ring_nf
  rw [hshift, hmgfX] at hcent
  have hcancel : Real.exp (-prob * t) * Real.exp (prob * t) = 1 := by
    rw [← Real.exp_add, show -prob * t + prob * t = 0 by ring, Real.exp_zero]
  calc (1 - prob + prob * Real.exp t)
      = (1 - prob + prob * Real.exp t) * 1 := by ring
    _ = (1 - prob + prob * Real.exp t) * (Real.exp (-prob * t) * Real.exp (prob * t)) := by
        congr 1; exact hcancel.symm
    _ = Real.exp (-prob * t) * (1 - prob + prob * Real.exp t) * Real.exp (prob * t) := by ring
    _ ≤ Real.exp (t ^ 2 / 8) * Real.exp (prob * t) := by
        refine mul_le_mul_of_nonneg_right hcent (Real.exp_nonneg (prob * t))
    _ = Real.exp (prob * t + t ^ 2 / 8) := by rw [Real.exp_add, mul_comm]

/-! ## Hypergeometric MGF ≤ Binomial MGF -/

/-- `e^{lam·H} = ∑_k C(H,k) (e^{lam}-1)^k` for `H : ℕ`. -/
theorem exp_mul_nat_eq_sum_choose (lam : ℝ) (H : ℕ) :
    Real.exp (lam * H) =
      ∑ k ∈ Finset.range (H + 1),
        (H.choose k : ℝ) * (Real.exp lam - 1) ^ k := by
  have hpow : Real.exp (lam * H) = (Real.exp lam) ^ H := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [hpow, show (Real.exp lam) ^ H = ((Real.exp lam - 1) + 1) ^ H by ring]
  -- `add_pow x y n` = ∑ C(n,k) x^k y^{n-k}
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _hk => ?_
  rw [one_pow, mul_one, mul_comm]

/-- Choose-average bound via descending-factorial moments. -/
theorem avg_hit_choose {n : Nat} (hn : 0 < n) (A S : Finset (Fin n)) (k : Nat) :
    (∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k := by
  classical
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hπ (π : Equiv.Perm (Fin n)) :
      ((((A.image π) ∩ S).card.descFactorial k : ℝ)) =
        (k.factorial : ℝ) * ((((A.image π) ∩ S).card.choose k : ℝ)) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ k
  have hsum :
      ∑ π : Equiv.Perm (Fin n),
          ((((A.image π) ∩ S).card.descFactorial k : ℝ)) =
        (k.factorial : ℝ) *
          ∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ)) := by
    simp_rw [hπ]
    rw [← Finset.mul_sum]
  have hS :
      (S.card.descFactorial k : ℝ) =
        (k.factorial : ℝ) * (S.card.choose k : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose S.card k
  have hle := avg_hit_descFactorial_le hn A S k
  have hgoal :
      (k.factorial : ℝ) *
          ((∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) ≤
        (k.factorial : ℝ) * ((S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k) := by
    calc (k.factorial : ℝ) *
            ((∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
              Fintype.card (Equiv.Perm (Fin n)))
        = ((k.factorial : ℝ) *
              ∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n)) := by
              field_simp
      _ = (∑ π : Equiv.Perm (Fin n),
              ((((A.image π) ∩ S).card.descFactorial k : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n)) := by rw [← hsum]
      _ ≤ (S.card.descFactorial k : ℝ) * ((A.card : ℝ) / n) ^ k := hle
      _ = (k.factorial : ℝ) * ((S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k) := by
            rw [hS]; ring
  exact (le_of_mul_le_mul_left hgoal hfac)

/-- Average row-hit MGF ≤ binomial MGF `(1-p+p e^lam)^|S|`. -/
theorem avg_exp_hit_le {n : Nat} (hn : 0 < n) (A S : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∑ π : Equiv.Perm (Fin n), Real.exp (lam * (((A.image π) ∩ S).card : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (1 - ((A.card : ℝ) / n) + ((A.card : ℝ) / n) * Real.exp lam) ^ S.card := by
  classical
  have hexpand' (π : Equiv.Perm (Fin n)) :
      Real.exp (lam * ((((A.image π) ∩ S).card : ℝ))) =
        ∑ k ∈ Finset.range (S.card + 1),
          ((((A.image π) ∩ S).card.choose k : ℝ) * (Real.exp lam - 1) ^ k) := by
    have hle : ((A.image π) ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    rw [exp_mul_nat_eq_sum_choose]
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle)) ?_
    intro k _hk hk'
    have : ((A.image π) ∩ S).card < k := by
      have : ¬ k < ((A.image π) ∩ S).card + 1 := fun h => hk' (Finset.mem_range.mpr h)
      omega
    simp [Nat.choose_eq_zero_of_lt this]
  have havg :
      (∑ π : Equiv.Perm (Fin n), Real.exp (lam * ((((A.image π) ∩ S).card : ℝ)))) /
          Fintype.card (Equiv.Perm (Fin n)) =
        ∑ k ∈ Finset.range (S.card + 1),
          (Real.exp lam - 1) ^ k *
            ((∑ π : Equiv.Perm (Fin n),
                ((((A.image π) ∩ S).card.choose k : ℝ))) /
              Fintype.card (Equiv.Perm (Fin n))) := by
    have hrewrite :
        ∑ π : Equiv.Perm (Fin n), Real.exp (lam * ((((A.image π) ∩ S).card : ℝ))) =
          ∑ π : Equiv.Perm (Fin n), ∑ k ∈ Finset.range (S.card + 1),
            ((((A.image π) ∩ S).card.choose k : ℝ) * (Real.exp lam - 1) ^ k) :=
      Fintype.sum_congr _ _ hexpand'
    rw [hrewrite, Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpull :
        ∑ π : Equiv.Perm (Fin n),
            ((((A.image π) ∩ S).card.choose k : ℝ) * (Real.exp lam - 1) ^ k) =
          (Real.exp lam - 1) ^ k *
            ∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ)) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_congr _ _ fun π => mul_comm _ _
    rw [hpull, mul_div_assoc]
  have hnonneg : 0 ≤ Real.exp lam - 1 := sub_nonneg.mpr (Real.one_le_exp hlam)
  rw [havg]
  calc ∑ k ∈ Finset.range (S.card + 1),
          (Real.exp lam - 1) ^ k *
            ((∑ π : Equiv.Perm (Fin n),
                ((((A.image π) ∩ S).card.choose k : ℝ))) /
              Fintype.card (Equiv.Perm (Fin n)))
      ≤ ∑ k ∈ Finset.range (S.card + 1),
          (Real.exp lam - 1) ^ k *
            ((S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k) := by
            refine Finset.sum_le_sum fun k _hk =>
              mul_le_mul_of_nonneg_left (avg_hit_choose hn A S k) (pow_nonneg hnonneg _)
    _ = ∑ k ∈ Finset.range (S.card + 1),
          (S.card.choose k : ℝ) *
            (((A.card : ℝ) / n) * (Real.exp lam - 1)) ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_pow]; ring
    _ = (((A.card : ℝ) / n) * (Real.exp lam - 1) + 1) ^ S.card := by
            -- add_pow z 1 n = ∑ C(n,k) z^k 1^{n-k}
            simpa [one_pow, mul_one, mul_comm] using
              (add_pow (((A.card : ℝ) / n) * (Real.exp lam - 1)) (1 : ℝ) S.card).symm
    _ = (1 - ((A.card : ℝ) / n) + ((A.card : ℝ) / n) * Real.exp lam) ^ S.card := by
            ring

/-! ## Product Chernoff over scrambles -/

theorem card_scramble (m n : Nat) :
    Fintype.card (Scramble m n) =
      Fintype.card (Equiv.Perm (Fin n)) ^ m := by
  simp [Scramble, Fintype.card_fin]

theorem avg_exp_rowHit_le {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (r : Fin m) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (1 - ((monotoneRowOnes c r).card : ℝ) / n +
        ((monotoneRowOnes c r).card : ℝ) / n * Real.exp lam) ^ S.card := by
  simpa [rowHit] using avg_exp_hit_le hn (monotoneRowOnes c r) S lam hlam

theorem row_density_le_one {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (r : Fin m) :
    ((monotoneRowOnes c r).card : ℝ) / n ≤ 1 := by
  have hcard : (monotoneRowOnes c r).card ≤ n := by
    simpa [Fintype.card_fin] using (monotoneRowOnes c r).card_le_univ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_one hn0).mpr (by exact_mod_cast hcard)

theorem avg_exp_onesInColumns_le {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    let p := (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)
    (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
        Fintype.card (Scramble m n) ≤
      Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) := by
  intro p
  classical
  set totalOnes : ℝ := ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)
  have hp_eq : p = totalOnes / (m * n) := rfl
  have hcard :
      (Fintype.card (Scramble m n) : ℝ) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ m := by
    exact_mod_cast card_scramble m n
  have hrewrite :
      ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) =
        ∏ r : Fin m,
          ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ)) := by
    have hσ (σ : Scramble m n) :
        Real.exp (lam * (onesInColumns c σ S : ℝ)) =
          ∏ r : Fin m, Real.exp (lam * (rowHit c S r (σ r) : ℝ)) := by
      have hX : (onesInColumns c σ S : ℝ) =
          ∑ r : Fin m, (rowHit c S r (σ r) : ℝ) := by
        exact_mod_cast onesInColumns_eq_sum_rowHit c S σ
      rw [hX, Finset.mul_sum, Real.exp_sum]
    simp_rw [hσ]
    exact (Fintype.prod_sum
        (fun (r : Fin m) (π : Equiv.Perm (Fin n)) =>
          Real.exp (lam * (rowHit c S r π : ℝ)))).symm
  have havg_prod :
      (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
          Fintype.card (Scramble m n) =
        ∏ r : Fin m,
          ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) := by
    rw [hrewrite, hcard]
    have hpow :
        ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ m) =
          ∏ _r : Fin m, (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hpow, ← Finset.prod_div_distrib]
  have hrow (r : Fin m) :
      ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
          Fintype.card (Equiv.Perm (Fin n))) ≤
        Real.exp
          (((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) *
            (S.card : ℝ)) := by
    set pr : ℝ := ((monotoneRowOnes c r).card : ℝ) / n
    have hp0 : (0 : ℝ) ≤ pr := by positivity
    have hp1 : pr ≤ 1 := row_density_le_one hn c r
    have hbin := avg_exp_rowHit_le hn c S r lam hlam
    have hbern := bernoulli_one_sub_add_mul_exp_le hp0 hp1 hlam
    have hbase : (0 : ℝ) ≤ 1 - pr + pr * Real.exp lam := by
      have : (0 : ℝ) ≤ 1 - pr := sub_nonneg.mpr hp1
      linarith [mul_nonneg hp0 (Real.exp_nonneg lam)]
    have hpow :
        (1 - pr + pr * Real.exp lam) ^ S.card ≤
          (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card :=
      pow_le_pow_left₀ hbase hbern _
    have hexp_pow :
        (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card =
          Real.exp ((pr * lam + lam ^ 2 / 8) * S.card) := by
      rw [← Real.exp_nat_mul, mul_comm]
    calc ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n)))
        ≤ (1 - pr + pr * Real.exp lam) ^ S.card := by
            convert hbin
      _ ≤ (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card := hpow
      _ = Real.exp ((pr * lam + lam ^ 2 / 8) * S.card) := hexp_pow
  rw [havg_prod]
  have hprod :
      ∏ r : Fin m,
          ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) ≤
        ∏ r : Fin m,
          Real.exp
            (((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) *
              (S.card : ℝ)) :=
    Finset.prod_le_prod (fun _ _ => by positivity) (fun r _ => hrow r)
  refine hprod.trans ?_
  rw [← Real.exp_sum]
  refine (Real.exp_le_exp).mpr (le_of_eq ?_)
  have hsum :
      ∑ r : Fin m,
          ((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) * S.card =
        (totalOnes / n) * lam * S.card + (m : ℝ) * S.card * lam ^ 2 / 8 := by
    have htot : totalOnes = ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) := rfl
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, htot]
    ring
  have hsum_p : totalOnes / n = p * m := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hp_eq]
    field_simp [hm0, hn0]
  rw [hsum, hsum_p]
  ring

/-- Paper Lemma 6.3 + (6.1): Hoeffding/Chernoff bound on scramble column-ones. -/
theorem lemma63ExpBound {m n : Nat} (hm : 0 < m) (hn : 0 < n) : Lemma63ExpBound m n where
  bound := by
    intro c S t ht bad hbad
    classical
    set p : ℝ := (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)
    set lam : ℝ := 4 * t
    have hlam : 0 ≤ lam := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht.le
    set thresh : ℝ := (p + t) * m * S.card
    have hmarkov :
        (bad.card : ℝ) ≤
          Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
      have hone (σ : Scramble m n) (hσ : σ ∈ bad) :
          (1 : ℝ) ≤
            Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) := by
        have hX : thresh ≤ (onesInColumns c σ S : ℝ) := by
          simpa [thresh, p] using hbad σ hσ
        exact Real.one_le_exp (mul_nonneg hlam (sub_nonneg.mpr hX))
      have hsplit (σ : Scramble m n) :
          Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) =
            Real.exp (-lam * thresh) *
              Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
        have : lam * ((onesInColumns c σ S : ℝ) - thresh) =
            lam * (onesInColumns c σ S : ℝ) + (-lam * thresh) := by ring
        rw [this, Real.exp_add, mul_comm]
      calc (bad.card : ℝ)
          = ∑ σ ∈ bad, (1 : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ σ ∈ bad,
              Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) :=
                Finset.sum_le_sum fun σ hσ => hone σ hσ
        _ ≤ ∑ σ : Scramble m n,
              Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  fun _ _ _ => Real.exp_nonneg _
        _ = ∑ σ : Scramble m n,
              Real.exp (-lam * thresh) *
                Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
                  simp_rw [hsplit]
        _ = Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
                  rw [← Finset.mul_sum]
    have hmgf := avg_exp_onesInColumns_le hm hn c S lam hlam
    have htotpos : (0 : ℝ) < Fintype.card (Scramble m n) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
    have hcombine :
        Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
          Real.exp (-(2 * t ^ 2 * m * S.card)) *
            (Fintype.card (Scramble m n) : ℝ) := by
      have havg :
          (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
              Fintype.card (Scramble m n) ≤
            Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) := by
        simpa [p] using hmgf
      have hsum_le :
          ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
            Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := by
        have := (div_le_iff₀ htotpos).mp havg
        linarith
      have hexp_nonneg : 0 ≤ Real.exp (-lam * thresh) := Real.exp_nonneg _
      have hstep1 :
          Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
            Real.exp (-lam * thresh) *
              (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le hexp_nonneg
      have hstep2 :
          Real.exp (-lam * thresh) *
              (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) =
            Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
      have hstep3 :
          Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) =
            Real.exp (-(2 * t ^ 2 * m * S.card)) := by
        congr 1
        -- lam = 4t, thresh = (p+t) m |S|
        change -(4 * t) * ((p + t) * m * S.card) + (4 * t) * p * m * S.card +
            m * S.card * (4 * t) ^ 2 / 8 =
          -(2 * t ^ 2 * m * S.card)
        ring
      calc Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))
          ≤ Real.exp (-lam * thresh) *
              (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) := hstep1
        _ = Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := hstep2
        _ = Real.exp (-(2 * t ^ 2 * m * S.card)) *
              (Fintype.card (Scramble m n) : ℝ) := by rw [hstep3]
    exact hmarkov.trans hcombine

/-! ## Paper-threshold Hoeffding (Lemma 6.1 uses `p = i/m`) -/

noncomputable def monotoneOnesDensity {m n : Nat} (c : MonotoneColumnSums m n) : ℝ :=
  (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)

theorem monotoneOnesDensity_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    monotoneOnesDensity c * m =
      (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n := by
  unfold monotoneOnesDensity
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hm0, hn0]

theorem sum_rowOnes_le_m_mul_n {m n : Nat} (c : MonotoneColumnSums m n) :
    ∑ r : Fin m, (monotoneRowOnes c r).card ≤ m * n := by
  calc
    ∑ r : Fin m, (monotoneRowOnes c r).card ≤ ∑ _r : Fin m, n :=
      Finset.sum_le_sum fun r _ => by
        simpa [Fintype.card_fin] using (monotoneRowOnes c r).card_le_univ
    _ = m * n := by simp [Finset.sum_const, Finset.card_univ]

theorem avgRowOnes_le_m {m n : Nat} (_hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn0]
  exact_mod_cast sum_rowOnes_le_m_mul_n c

theorem monotoneOnesDensity_le_one_div_m_iff {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    monotoneOnesDensity c ≤ (1 : ℝ) / m ↔
      (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmul := monotoneOnesDensity_mul hm hn c
  constructor
  · intro h
    have hle : monotoneOnesDensity c * m ≤ 1 := (le_div_iff₀ hmpos).mp h
    rw [← hmul]
    exact hle
  · intro h
    have hle : monotoneOnesDensity c * m ≤ 1 := hmul.symm ▸ h
    exact (le_div_iff₀ hmpos).mpr hle

/-- Same Chernoff bound when every row has exactly `⌊p₀·n⌋` ones (constant density `p₀`). -/
theorem lemma63ExpBound_atDensity {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (p₀ : ℝ) (_hp₀0 : 0 ≤ p₀) (_hp₀1 : p₀ ≤ 1)
    (rowOnes : Nat)
    (hrowOnes : (rowOnes : ℝ) = p₀ * n)
    (hrows : ∀ (c : MonotoneColumnSums m n) (r : Fin m),
      (monotoneRowOnes c r).card = rowOnes) :
    ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (t : ℝ),
      0 < t →
      ∀ (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad, (p₀ + t) * m * S.card ≤ (onesInColumns c σ S : ℝ)) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * m * S.card)) *
              (Fintype.card (Scramble m n) : ℝ) := by
  intro c S t ht bad hbad
  have h63 := (lemma63ExpBound hm hn).bound c S t ht bad ?hbad'
  · exact h63
  intro σ hσ
  have hp_eq : monotoneOnesDensity c = p₀ := by
    unfold monotoneOnesDensity
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hsum :
        ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) = (m : ℝ) * rowOnes := by
      have h₁ : ∀ r : Fin m, ((monotoneRowOnes c r).card : ℝ) = rowOnes :=
        fun r => by exact_mod_cast hrows c r
      simp_rw [h₁, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum, hrowOnes]
    field_simp [hm0, hn0]
  rw [show ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)) = p₀ from hp_eq]
  exact hbad σ hσ

theorem onesInColumns_ge_paper_thresh {m n : Nat} (hm : 0 < m) (_hn : 0 < n)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (epsB : ℝ) (i : Nat)
    (hge : (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ)) :
    let S := excessColumnSet c σ i
    let s := S.card
    let t := (epsB / 2) * ((n : ℝ) / s)
    0 < s →
      0 < t →
        ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * s ≤ (onesInColumns c σ S : ℝ) := by
  intro S s t hs ht
  have hones := lemma61_excess_columns epsB c σ i hge
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsplit :
      ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * s = (i : ℝ) * s + t * m * s := by
    field_simp [hm0]
  have htms : t * m * s = (epsB / 2) * (m * n) := by
    show (epsB / 2) * ((n : ℝ) / s) * m * s = (epsB / 2) * (m * n)
    field_simp [hs0]
  have hthresh :
      ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * s = (i * s : ℝ) + (epsB / 2) * (m * n) := by
    rw [hsplit, htms]
  rw [hthresh]
  exact_mod_cast hones

theorem not_hasCombinatorialPropertyB_iff {m n : Nat} (σ : Scramble m n) (epsB : ℝ) :
    ¬ HasCombinatorialPropertyB σ epsB ↔
      ∃ (c : MonotoneColumnSums m n) (i : Nat),
        1 ≤ i ∧ i ≤ m ∧
          (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ) := by
  classical
  constructor
  · intro hnot
    by_contra hex
    push_neg at hex
    have hB : HasCombinatorialPropertyB σ epsB := by
      intro c i hi1 him
      exact hex c i hi1 him
    exact hnot hB
  · intro h
    rcases h with ⟨c, i, hi1, him, hge⟩
    intro hB
    linarith [hB c i hi1 him, hge]

/-- Paper Lemma 6.1 Hoeffding threshold at level `i` (Chvátal uses `p = i/m`). -/
structure Lemma63ExpBoundAtLevel (m n i : Nat) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (t : ℝ),
      0 < t →
      ∀ (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad,
          ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * S.card ≤ (onesInColumns c σ S : ℝ)) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * m * S.card)) *
              (Fintype.card (Scramble m n) : ℝ)

/-- Chernoff at level `i` for one monotone matrix with average row ones at most `i`. -/
theorem lemma63ExpBoundAtLevel_bound_for {m n i : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n)
    (havg : (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ (i : ℝ)) :
    ∀ (S : Finset (Fin n)) (t : ℝ) (ht : 0 < t) (bad : Finset (Scramble m n)),
      (∀ σ ∈ bad,
        ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * S.card ≤ (onesInColumns c σ S : ℝ)) →
        (bad.card : ℝ) ≤
          Real.exp (-(2 * t ^ 2 * m * S.card)) *
            (Fintype.card (Scramble m n) : ℝ) := by
  intro S t ht bad hbad
  have hpim : monotoneOnesDensity c ≤ (i : ℝ) / (m : ℝ) := by
    unfold monotoneOnesDensity
    have hm0 : (0 : ℝ) < (m : ℝ) * n := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
    rw [div_le_iff₀ hm0]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) ≤ (i : ℝ) * n := by
      rw [← div_le_iff₀ hn0]
      exact havg
    calc (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ))
        ≤ (i : ℝ) * n := hsum
      _ = ((i : ℝ) / (m : ℝ)) * ((m : ℝ) * n) := by field_simp [hm.ne']
  have hthresh :
      ∀ σ ∈ bad,
        (monotoneOnesDensity c + t) * m * S.card ≤ (onesInColumns c σ S : ℝ) := by
    intro σ hσ
    have hpaper := hbad σ hσ
    have hle : monotoneOnesDensity c + t ≤ (i : ℝ) / (m : ℝ) + t := by linarith
    have hnonneg : 0 ≤ (m : ℝ) * S.card := by positivity
    have hstep :
        (monotoneOnesDensity c + t) * m * S.card ≤
          ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * S.card := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hle hnonneg
    exact hstep.trans hpaper
  exact (lemma63ExpBound hm hn).bound c S t ht bad hthresh

/-- Chernoff at level `i` only for matrices in the pipeline mass class at that level. -/
structure Lemma63ExpBoundAtLevelOn (m n i : Nat) (P : MonotoneColumnSums m n → Prop) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n), P c →
      ∀ (S : Finset (Fin n)) (t : ℝ) (ht : 0 < t) (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad,
          ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * S.card ≤ (onesInColumns c σ S : ℝ)) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * m * S.card)) *
              (Fintype.card (Scramble m n) : ℝ)

theorem lemma63ExpBoundAtLevelOn_totalColumnOnesLeLevel {m n i : Nat} (hm : 0 < m) (hn : 0 < n) :
    Lemma63ExpBoundAtLevelOn m n i (TotalColumnOnesLeLevel m n i) where
  bound c hc S t ht bad hbad :=
    lemma63ExpBoundAtLevel_bound_for hm hn c
      (avgRowOnes_le_i_of_totalColumnOnes_le hn c hc) S t ht bad hbad

/-- Paper Chernoff threshold when average row ones `≤ i` (equivalently `p·m ≤ i`). -/
theorem lemma63ExpBoundAtLevel_of_avgRowOnes_le {m n i : Nat} (hm : 0 < m) (hn : 0 < n)
    (havg :
      ∀ (c : MonotoneColumnSums m n),
        (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ (i : ℝ)) :
    Lemma63ExpBoundAtLevel m n i where
  bound c S t ht bad hbad :=
    lemma63ExpBoundAtLevel_bound_for hm hn c (havg c) S t ht bad hbad

/-- Paper threshold Chernoff when every row has `i·n/m` ones (so density `p = i/m`). -/
theorem lemma63ExpBoundAtLevel_of_constantRows {m n i : Nat} (hm : 0 < m) (hn : 0 < n)
    (hi : i ≤ m) (rowOnes : Nat) (hrowOnes : rowOnes * m = i * n)
    (hrows : ∀ (c : MonotoneColumnSums m n) (r : Fin m),
      (monotoneRowOnes c r).card = rowOnes) :
    Lemma63ExpBoundAtLevel m n i where
  bound := by
    intro c S t ht bad hbad
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hrowOnesR : (rowOnes : ℝ) = (i : ℝ) / (m : ℝ) * n := by
      field_simp [hmpos.ne', hnpos.ne']
      rw [← Nat.cast_mul, hrowOnes, Nat.cast_mul]
    have hi0 : (0 : ℝ) ≤ (i : ℝ) / (m : ℝ) := by positivity
    have hi1 : (i : ℝ) / (m : ℝ) ≤ 1 :=
      (div_le_one hmpos).mpr (by exact_mod_cast hi)
    exact (lemma63ExpBound_atDensity hm hn ((i : ℝ) / (m : ℝ)) hi0 hi1 rowOnes hrowOnesR hrows)
      c S t ht bad hbad

/-- Paper level `i = m` Chernoff for every monotone matrix (average row ones always `≤ m`). -/
theorem lemma63ExpBoundAtLevel_top {m n : Nat} (hm : 0 < m) (hn : 0 < n) (_hm1 : 1 ≤ m) :
    Lemma63ExpBoundAtLevel m n m :=
  lemma63ExpBoundAtLevel_of_avgRowOnes_le hm hn fun c => avgRowOnes_le_m hm hn c

theorem lemma63ExpBoundAtLevel_one_of_avgRowOnes {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (havg : AvgRowOnesLeOne m n) :
    Lemma63ExpBoundAtLevel m n 1 :=
  lemma63ExpBoundAtLevel_of_avgRowOnes_le hm hn fun c =>
    by exact_mod_cast AvgRowOnesLeOne.sum_div_le_one havg c

/-- When every matrix has average row ones `≤ 1`, paper level `i` Chernoff holds for all `1 ≤ i ≤ m`. -/
theorem lemma63ExpBoundAtLevel_of_avgRowOnes_le_one {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (havg : AvgRowOnesLeOne m n) :
    ∀ (i : Nat), 1 ≤ i → i ≤ m → Lemma63ExpBoundAtLevel m n i := by
  intro i hi1 _him
  refine lemma63ExpBoundAtLevel_of_avgRowOnes_le hm hn fun c => ?_
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  exact (AvgRowOnesLeOne.sum_div_le_one havg c).trans hiR

/-- Residual: unrestricted `Lemma63ExpBoundAtLevel` at level `1` for arbitrary monotone `c`
    (paper `p = i/m` without the avg-row-ones hypothesis). When `AvgRowOnesLeOne m n`
    holds, use `of_avgRowOnes_le_one` instead. For the sort–scramble pipeline class,
    use `DecodeMatrixClassObligation` (no global `TotalColumnOnesLeN`). -/
structure Lemma61FailBoundObligation (m n : Nat) (epsB : ℝ) where
  hm : 0 < m
  hn : 0 < n
  hm1 : 1 ≤ m
  hn1 : 1 ≤ n
  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB
  /-- Bottom-level Chernoff (sufficient for the union after `failWitness_level_one`). -/
  levelExp1 : Lemma63ExpBoundAtLevel m n 1
  levelExp :
    ∀ (i : Nat), 1 ≤ i → i ≤ m → Lemma63ExpBoundAtLevel m n i

/-- Chernoff on the true pipeline mass class (`totalColumnOnes c ≤ n·i` at level `i`). -/
structure DecodeMatrixClassObligation (m n : Nat) (epsB : ℝ) where
  hm : 0 < m
  hn : 0 < n
  hm1 : 1 ≤ m
  hn1 : 1 ≤ n
  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB
  levelExpOn :
    ∀ (i : Nat), 1 ≤ i → i ≤ m →
      Lemma63ExpBoundAtLevelOn m n i (TotalColumnOnesLeLevel m n i)

theorem DecodeMatrixClassObligation.epsB_pos {m n : Nat} {epsB : ℝ}
    (O : DecodeMatrixClassObligation m n epsB) : 0 < epsB := by
  have hsqrt : 0 < Real.sqrt (2 * (1 + Real.log m) / m) :=
    Real.sqrt_pos.mpr (by positivity [O.hm1])
  linarith [O.heps, hsqrt]

/-- Kernel discharge: per-matrix `totalColumnOnes c ≤ n·i` ⇒ Chernoff at level `i`. -/
def DecodeMatrixClassObligation.standard {m n : Nat} {epsB : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    DecodeMatrixClassObligation m n epsB where
  hm := hm
  hn := hn
  hm1 := hm1
  hn1 := hn1
  heps := heps
  levelExpOn i _hi1 _him :=
    lemma63ExpBoundAtLevelOn_totalColumnOnesLeLevel hm hn

theorem Lemma61FailBoundObligation.epsB_pos {m n : Nat} {epsB : ℝ}
    (O : Lemma61FailBoundObligation m n epsB) : 0 < epsB := by
  have hsqrt : 0 < Real.sqrt (2 * (1 + Real.log m) / m) :=
    Real.sqrt_pos.mpr (by positivity [O.hm1])
  linarith [O.heps, hsqrt]

theorem Lemma61FailBoundObligation.of_avgRowOnes_le_one {m n : Nat} {epsB : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (havg : AvgRowOnesLeOne m n) :
    Lemma61FailBoundObligation m n epsB where
  hm := hm
  hn := hn
  hm1 := hm1
  hn1 := hn1
  heps := heps
  levelExp1 := lemma63ExpBoundAtLevel_one_of_avgRowOnes hm hn havg
  levelExp := lemma63ExpBoundAtLevel_of_avgRowOnes_le_one hm hn havg

theorem lemma63ExpBoundAtLevel_of_totalColumnOnes_le {m n i : Nat} (hm : 0 < m) (hn : 0 < n)
    (h :
      ∀ (c : MonotoneColumnSums m n),
        totalColumnOnes c ≤ n * i) :
    Lemma63ExpBoundAtLevel m n i :=
  lemma63ExpBoundAtLevel_of_avgRowOnes_le hm hn fun c =>
    avgRowOnes_le_i_of_totalColumnOnes_le hn c (h c)

theorem lemma63ExpBoundAtLevel_one_of_totalColumnOnesLeN {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : TotalColumnOnesLeN m n) :
    Lemma63ExpBoundAtLevel m n 1 :=
  lemma63ExpBoundAtLevel_of_totalColumnOnes_le hm hn fun c => by
    simpa [Nat.one_mul] using h c

theorem lemma63ExpBoundAtLevel_of_totalColumnOnesLeN {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : TotalColumnOnesLeN m n) :
    ∀ (i : Nat), 1 ≤ i → i ≤ m → Lemma63ExpBoundAtLevel m n i := by
  intro i hi1 _him
  refine lemma63ExpBoundAtLevel_of_totalColumnOnes_le hm hn fun c => ?_
  have hiR : (1 : Nat) ≤ i := hi1
  have hi0 : 0 < i := Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) hiR
  exact Nat.le_trans (h c) (Nat.le_mul_of_pos_right n hi0)

theorem Lemma61FailBoundObligation.of_totalColumnOnesLeN {m n : Nat} {epsB : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (h : TotalColumnOnesLeN m n) :
    Lemma61FailBoundObligation m n epsB :=
  Lemma61FailBoundObligation.of_avgRowOnes_le_one hm hn hm1 hn1 heps
    (AvgRowOnesLeOne.of_totalColumnOnesLeN hn h)

theorem Lemma61FailBoundObligation.of_totalColSumsLeN {m n : Nat} {epsB : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (h : TotalColSumsLeN m n) :
    Lemma61FailBoundObligation m n epsB :=
  Lemma61FailBoundObligation.of_totalColumnOnesLeN hm hn hm1 hn1 heps h

theorem DecodeMatrixClassObligation.of_totalColumnOnesLeN {m n : Nat} {epsB : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (_h : TotalColumnOnesLeN m n) :
    DecodeMatrixClassObligation m n epsB :=
  DecodeMatrixClassObligation.standard hm hn hm1 hn1 heps

end Chvatal
