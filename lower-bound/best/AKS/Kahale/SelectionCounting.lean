module

public import AKS.Kahale.LayerPotential

/-! # The binomial constraint for approximate zero selection

This is the term of Kahale et al., Lemma 5.1 needed by the Fibonacci argument.
The depth parameter here is the length of an actual parallel decomposition.
-/

@[expose] public section

namespace Kahale

open Finset

def SelectZeros {n : ℕ} (net : ComparatorNetwork n) (t slack : ℕ) : Prop :=
  ∀ v : Fin n → Bool, (univ.filter (fun i ↦ v i = false)).card ≤ t →
    ∀ i, net.exec v i = false → i.val < t + slack

theorem selection_certificate_height {n s : ℕ} (net : ComparatorNetwork n)
    (hs : SelectZeros net (2 ^ s) (2 ^ s)) (i : Fin n) (hi : 2 ^ (s + 1) ≤ i.val) :
    s + 1 ≤ certificateHeights net i := by
  by_contra hh
  have hc : certificateHeights net i ≤ s := by omega
  obtain ⟨S, hS, hz⟩ := certificateHeights_correct net i
  let v : Fin n → Bool := fun j ↦ if j ∈ S then false else true
  have hv : univ.filter (fun j ↦ v j = false) = S := by
    ext j
    simp [v]
  have hcard : (univ.filter (fun j ↦ v j = false)).card ≤ 2 ^ s := by
    rw [hv]
    exact hS.trans (Nat.pow_le_pow_right (by omega) hc)
  have hzero := hz v (by intro j hj; simp [v, hj])
  have hout := hs v hcard i hzero
  rw [pow_succ'] at hi
  omega

theorem selection_deficit_sum {n s : ℕ} (net : ComparatorNetwork n)
    (hs : SelectZeros net (2 ^ s) (2 ^ s)) :
    (∑ i : Fin n, deficitPotential 0 (s + 1) (certificateHeights net i)) ≤
      2 ^ (s + 1) * (s + 1) := by
  let E := univ.filter (fun i : Fin n ↦ i.val < 2 ^ (s + 1))
  have hE : E.card ≤ 2 ^ (s + 1) := by
    by_cases hn : 2 ^ (s + 1) ≤ n
    · exact (card_filter_val_lt n _ hn).le
    · exact (card_filter_le _ _).trans (by simp only [card_univ, Fintype.card_fin]; omega)
  have heq : (∑ i ∈ E, deficitPotential 0 (s + 1) (certificateHeights net i)) =
      ∑ i : Fin n, deficitPotential 0 (s + 1) (certificateHeights net i) := by
    apply sum_subset (filter_subset _ _)
    intro i _ hi
    have hidx : 2 ^ (s + 1) ≤ i.val := by simpa only [E, mem_filter, mem_univ, true_and, not_lt] using hi
    exact deficitPotential_eq_zero _ _ _ (selection_certificate_height net hs i hidx)
  rw [← heq]
  calc (∑ i ∈ E, deficitPotential 0 (s + 1) (certificateHeights net i))
      ≤ ∑ _i ∈ E, (s + 1) := by
        apply sum_le_sum
        intro i _
        exact Nat.sub_le _ _
    _ = E.card * (s + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hE

theorem yao_binomial_constraint {n s : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs)
    (hs : SelectZeros ⟨layers.flatten⟩ (2 ^ s) (2 ^ s)) :
    n * Nat.choose layers.length s ≤ 2 ^ (layers.length + s + 1) * (s + 1) := by
  have hh := parallel_layers_potential layers hp (fun _ ↦ 0) (s + 1)
  have hlow := deficitPotential_choose_lower layers.length (s + 1) 0 s
  simp at hlow
  have hsum := selection_deficit_sum (ComparatorNetwork.mk layers.flatten) hs
  simp only [certificateHeights] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hh
  calc n * Nat.choose layers.length s
      ≤ n * deficitPotential layers.length (s + 1) 0 := Nat.mul_le_mul_left _ hlow
    _ ≤ 2 ^ layers.length * ∑ i, deficitPotential 0 (s + 1)
        (layers.flatten.foldl heightStep (fun _ ↦ 0) i) := hh
    _ ≤ 2 ^ layers.length * (2 ^ (s + 1) * (s + 1)) := Nat.mul_le_mul_left _ hsum
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.add_assoc]

end Kahale
