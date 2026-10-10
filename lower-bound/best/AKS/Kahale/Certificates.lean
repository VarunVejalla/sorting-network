module

public import AKS.Sort.Monotone

/-! # Zero certificates and their heights

A zero certificate is a set of input positions which, when all zero, forces
a given wire to be zero. Min-gates inherit one certificate; max-gates combine
two. Height `h` guarantees a certificate with at most `2^h` inputs.
-/

@[expose] public section

namespace Kahale

open Finset

def ZeroCertificate {n : ℕ} (net : ComparatorNetwork n) (i : Fin n)
    (S : Finset (Fin n)) : Prop :=
  ∀ v : Fin n → Bool, (∀ j ∈ S, v j = false) → net.exec v i = false

def HeightCertificates {n : ℕ} (net : ComparatorNetwork n) (h : Fin n → ℕ) : Prop :=
  ∀ i, ∃ S : Finset (Fin n), S.card ≤ 2 ^ h i ∧ ZeroCertificate net i S

def heightStep {n : ℕ} (h : Fin n → ℕ) (c : Comparator n) : Fin n → ℕ :=
  fun i ↦ if i = c.i then min (h c.i) (h c.j)
    else if i = c.j then max (h c.i) (h c.j) + 1 else h i

theorem heightCertificates_nil (n : ℕ) : HeightCertificates (⟨[]⟩ : ComparatorNetwork n)
    (fun _ ↦ 0) := by
  intro i
  refine ⟨{i}, by simp, ?_⟩
  intro v hv
  exact hv i (mem_singleton_self i)

theorem heightCertificates_append {n : ℕ} (net : ComparatorNetwork n)
    (h : Fin n → ℕ) (hc : HeightCertificates net h) (c : Comparator n) :
    HeightCertificates ⟨net.comparators ++ [c]⟩ (heightStep h c) := by
  intro i
  obtain ⟨Si, hSi, hzi⟩ := hc c.i
  obtain ⟨Sj, hSj, hzj⟩ := hc c.j
  have hex (v : Fin n → Bool) :
      (ComparatorNetwork.mk (net.comparators ++ [c])).exec v = c.apply (net.exec v) := by
    rw [ComparatorNetwork.exec_append]
    rfl
  by_cases hi : i = c.i
  · subst i
    by_cases hh : h c.i ≤ h c.j
    · refine ⟨Si, ?_, ?_⟩
      · simpa [heightStep, min_eq_left hh] using hSi
      · intro v hv
        rw [hex, Comparator.apply, if_pos rfl, hzi v hv]
        simp
    · refine ⟨Sj, ?_, ?_⟩
      · simpa [heightStep, min_eq_right (Nat.le_of_not_le hh)] using hSj
      · intro v hv
        rw [hex, Comparator.apply, if_pos rfl, hzj v hv]
        simp
  · by_cases hj : i = c.j
    · subst i
      refine ⟨Si ∪ Sj, ?_, ?_⟩
      · have h₁ : Si.card ≤ 2 ^ max (h c.i) (h c.j) :=
          hSi.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
        have h₂ : Sj.card ≤ 2 ^ max (h c.i) (h c.j) :=
          hSj.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
        have hu := card_union_le Si Sj
        simp only [heightStep, if_neg hi, if_true, pow_succ]
        omega
      · intro v hv
        have h₁ := hzi v (fun j hj ↦ hv j (mem_union_left Sj hj))
        have h₂ := hzj v (fun j hj ↦ hv j (mem_union_right Si hj))
        rw [hex, Comparator.apply, if_neg hi, if_pos rfl, h₁, h₂]
        rfl
    · obtain ⟨S, hS, hz⟩ := hc i
      refine ⟨S, by simpa [heightStep, hi, hj] using hS, ?_⟩
      intro v hv
      rw [hex, Comparator.apply, if_neg hi, if_neg hj]
      exact hz v hv

def certificateHeights {n : ℕ} (net : ComparatorNetwork n) : Fin n → ℕ :=
  net.comparators.foldl heightStep (fun _ ↦ 0)

theorem certificateHeights_correct {n : ℕ} (net : ComparatorNetwork n) :
    HeightCertificates net (certificateHeights net) := by
  obtain ⟨cs⟩ := net
  induction cs using List.reverseRecOn with
  | nil => exact heightCertificates_nil n
  | append_singleton cs c ih =>
    simpa only [certificateHeights, List.foldl_append, List.foldl_cons, List.foldl_nil] using
      heightCertificates_append ⟨cs⟩ _ ih c

end Kahale
