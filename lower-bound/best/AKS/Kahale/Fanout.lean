module

public import AKS.Kahale.ApproxSelection
public import AKS.Sort.Depth

/-! # A suffix of s parallel layers has fan-out at most 2^s -/

@[expose] public section

namespace Kahale

open Finset

def layerNeighbors {n : ℕ} : List (Comparator n) → Fin n → Finset (Fin n)
  | [], i => {i}
  | c :: cs, i => if i = c.i ∨ i = c.j then {c.i, c.j} else layerNeighbors cs i

theorem layerNeighbors_card {n : ℕ} (cs : List (Comparator n)) (i : Fin n) :
    (layerNeighbors cs i).card ≤ 2 := by
  induction cs with
  | nil => simp [layerNeighbors]
  | cons c cs ih =>
    simp only [layerNeighbors]
    split_ifs
    · exact (card_insert_le _ _).trans (by simp)
    · exact ih

theorem comparator_value_moves {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (i : Fin n) (hi : i = c.i ∨ i = c.j) :
    ∃ j ∈ ({c.i, c.j} : Finset (Fin n)), c.apply v j = v i := by
  have hne : c.j ≠ c.i := ne_of_gt c.h
  rcases hi with rfl | rfl <;> by_cases hv : v c.i ≤ v c.j
  · exact ⟨c.i, by simp, by simp [Comparator.apply, min_eq_left hv]⟩
  · exact ⟨c.j, by simp, by simp [Comparator.apply, hne, max_eq_left (le_of_not_ge hv)]⟩
  · exact ⟨c.j, by simp, by simp [Comparator.apply, hne, max_eq_right hv]⟩
  · exact ⟨c.i, by simp, by simp [Comparator.apply, min_eq_right (le_of_not_ge hv)]⟩

theorem parallel_layer_value_moves {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (hp : IsParallelLayer cs) (v : Fin n → α) (i : Fin n) :
    ∃ j ∈ layerNeighbors cs i, (ComparatorNetwork.mk cs).exec v j = v i := by
  induction cs generalizing v with
  | nil => exact ⟨i, mem_singleton_self i, rfl⟩
  | cons c cs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hp
    by_cases hi : i = c.i ∨ i = c.j
    · obtain ⟨j, hj, hv⟩ := comparator_value_moves c v i hi
      refine ⟨j, by simpa only [layerNeighbors, if_pos hi] using hj, ?_⟩
      change cs.foldl (fun w d ↦ d.apply w) (c.apply v) j = v i
      rw [foldl_comparators_outside]
      · exact hv
      · intro d hd
        have hn := hh d hd
        unfold Comparator.overlaps at hn
        rcases mem_insert.mp hj with rfl | hj
        · tauto
        · have he : j = c.j := mem_singleton.mp hj
          subst j
          tauto
    · obtain ⟨j, hj, hv⟩ := ih ht (c.apply v)
      refine ⟨j, by simpa only [layerNeighbors, if_neg hi] using hj, ?_⟩
      change (ComparatorNetwork.mk cs).exec (c.apply v) j = v i
      rw [hv]
      push_neg at hi
      simp [Comparator.apply, hi.1, hi.2]

def layerReach {n : ℕ} (cs : List (Comparator n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.biUnion (layerNeighbors cs)

theorem layerReach_card {n : ℕ} (cs : List (Comparator n)) (S : Finset (Fin n)) :
    (layerReach cs S).card ≤ 2 * S.card := by
  calc (layerReach cs S).card
      ≤ ∑ i ∈ S, (layerNeighbors cs i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ S, (2 : ℕ) := sum_le_sum (fun i _ ↦ layerNeighbors_card cs i)
    _ = _ := by simp [mul_comm]

def suffixReach {n : ℕ} (layers : List (List (Comparator n))) (S : Finset (Fin n)) :
    Finset (Fin n) := layers.foldl (fun T cs ↦ layerReach cs T) S

theorem suffixReach_card {n : ℕ} (layers : List (List (Comparator n))) (S : Finset (Fin n)) :
    (suffixReach layers S).card ≤ 2 ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [suffixReach]
  | cons cs layers ih =>
    change (suffixReach layers (layerReach cs S)).card ≤ 2 ^ (layers.length + 1) * S.card
    calc (suffixReach layers (layerReach cs S)).card
        ≤ 2 ^ layers.length * (layerReach cs S).card := ih _
      _ ≤ 2 ^ layers.length * (2 * S.card) := Nat.mul_le_mul_left _ (layerReach_card cs S)
      _ = _ := by rw [pow_succ']; ring

theorem suffix_value_moves {n : ℕ} {α : Type*} [LinearOrder α]
    (layers : List (List (Comparator n))) (hp : ∀ cs ∈ layers, IsParallelLayer cs)
    (S : Finset (Fin n)) (v : Fin n → α) (i : Fin n) (hi : i ∈ S) :
    ∃ j ∈ suffixReach layers S, (ComparatorNetwork.mk layers.flatten).exec v j = v i := by
  induction layers generalizing S v i with
  | nil => exact ⟨i, hi, rfl⟩
  | cons cs layers ih =>
    obtain ⟨j, hj, hv⟩ := parallel_layer_value_moves cs (hp cs List.mem_cons_self) v i
    have hmem : j ∈ layerReach cs S := mem_biUnion.mpr ⟨i, hi, hj⟩
    obtain ⟨l, hl, he⟩ := ih (fun ds hd ↦ hp ds (List.mem_cons_of_mem cs hd))
      (layerReach cs S) ((ComparatorNetwork.mk cs).exec v) j hmem
    refine ⟨l, hl, ?_⟩
    change (ComparatorNetwork.mk (cs ++ layers.flatten)).exec v l = v i
    rw [ComparatorNetwork.exec_append]
    exact he.trans hv

theorem sorted_suffix_rank_cover {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n))) (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec σ) = id) (i : Fin n)
    (σ : Equiv.Perm (Fin n)) : pre.exec σ i ∈ suffixReach suffix {i} := by
  obtain ⟨j, hj, hv⟩ := suffix_value_moves suffix hp {i} (pre.exec σ) i (mem_singleton_self i)
  rw [hs σ] at hv
  change j = pre.exec σ i at hv
  exact hv ▸ hj

theorem sorted_suffix_approx_select {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n))) (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec σ) = id) (t : ℕ) :
    ApproxSelect pre t (2 ^ suffix.length) := by
  apply rank_covers_approx_select pre (fun i ↦ suffixReach suffix {i})
  · exact sorted_suffix_rank_cover pre suffix hp hs
  · intro i
    simpa only [card_singleton, mul_one] using suffixReach_card suffix {i}

end Kahale
