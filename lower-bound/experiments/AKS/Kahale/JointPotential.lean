module

public import AKS.Kahale.CertificateCompatibility
public import Mathlib.Data.Finset.Max

/-! # Joint certificate-product bounds and exact finite counterexamples

The two exact minimum certificate sizes do not determine their next values,
even at nonredundant comparators in actual four-wire networks. The product
potential has a sharp factor-two local bound. Neither fact is a new asymptotic
sorting lower bound.
-/

@[expose] public section

namespace Kahale

theorem joint_product_scalar_bound (a b c d : ℕ) :
    min a c * (b + d) + (a + c) * min b d ≤ 2 * (a * b + c * d) := by
  rcases le_total a c with hac | hca <;> rcases le_total b d with hbd | hdb
  · rw [min_eq_left hac, min_eq_left hbd]
    nlinarith [Nat.mul_le_mul_right d hac, Nat.mul_le_mul_left c hbd]
  · rw [min_eq_left hac, min_eq_right hdb]
    nlinarith [Nat.mul_le_mul_left a hdb, Nat.mul_le_mul_right d hac]
  · rw [min_eq_right hca, min_eq_left hbd]
    nlinarith [Nat.mul_le_mul_left c hbd, Nat.mul_le_mul_right b hca]
  · rw [min_eq_right hca, min_eq_right hdb]
    nlinarith [Nat.mul_le_mul_right b hca, Nat.mul_le_mul_left a hdb]

theorem joint_product_pair_bound (a b c d loZ loO hiZ hiO : ℕ)
    (hloZ : loZ ≤ min a c) (hloO : loO ≤ b + d)
    (hhiZ : hiZ ≤ a + c) (hhiO : hiO ≤ min b d) :
    loZ * loO + hiZ * hiO ≤ 2 * (a * b + c * d) := by
  exact (Nat.add_le_add (Nat.mul_le_mul hloZ hloO) (Nat.mul_le_mul hhiZ hhiO)).trans
    (joint_product_scalar_bound a b c d)

/-- Exact support minimization; on monotone wire functions this is exactly
    minimum certificate size. The fallback is only for an empty support family. -/
def minimumSupportSize {n : ℕ} (f : (Fin n → Bool) → Bool) (value : Bool) : ℕ :=
  ((Finset.univ.filter (fun v ↦ f v = value)).image
    (fun v ↦ (Finset.univ.filter (fun i ↦ v i = value)).card)).min.untopD 0

def exactWireCertificatePair {n : ℕ} (net : ComparatorNetwork n) (i : Fin n) : ℕ × ℕ :=
  (minimumSupportSize (fun v ↦ net.exec v i) false,
   minimumSupportSize (fun v ↦ net.exec v i) true)

def independentPrefix : ComparatorNetwork 4 :=
  ⟨[⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩]⟩

def reconvergentPrefix : ComparatorNetwork 4 :=
  ⟨[⟨2, 3, by decide⟩, ⟨1, 2, by decide⟩]⟩

def independentNext : ComparatorNetwork 4 :=
  ⟨independentPrefix.comparators ++ [⟨1, 3, by decide⟩]⟩

def reconvergentNext : ComparatorNetwork 4 :=
  ⟨reconvergentPrefix.comparators ++ [⟨2, 3, by decide⟩]⟩

theorem identical_joint_statistics_different_updates :
    exactWireCertificatePair independentPrefix 1 = (2, 1) ∧
    exactWireCertificatePair independentPrefix 3 = (2, 1) ∧
    exactWireCertificatePair reconvergentPrefix 2 = (2, 1) ∧
    exactWireCertificatePair reconvergentPrefix 3 = (2, 1) ∧
    exactWireCertificatePair independentNext 1 = (2, 2) ∧
    exactWireCertificatePair independentNext 3 = (4, 1) ∧
    exactWireCertificatePair reconvergentNext 2 = (2, 2) ∧
    exactWireCertificatePair reconvergentNext 3 = (3, 1) := by decide +kernel

def firstPairNetwork : ComparatorNetwork 2 := ⟨[⟨0, 1, by decide⟩]⟩

theorem joint_product_factor_two_attained :
    exactWireCertificatePair (⟨[]⟩ : ComparatorNetwork 2) 0 = (1, 1) ∧
    exactWireCertificatePair (⟨[]⟩ : ComparatorNetwork 2) 1 = (1, 1) ∧
    exactWireCertificatePair firstPairNetwork 0 = (1, 2) ∧
    exactWireCertificatePair firstPairNetwork 1 = (2, 1) := by decide +kernel

end Kahale
