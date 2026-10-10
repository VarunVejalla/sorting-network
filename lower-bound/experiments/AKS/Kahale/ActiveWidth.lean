module

public import AKS.Kahale.UnionCoupling
public import AKS.Kahale.Fanout

/-! # Active comparator width as a function of remaining suffix depth

Adjacent-rank crossing plus suffix rank covers bounds an active comparator's
width by 2^(s+1)-1 when s parallel stages remain. This is structural progress,
not an improved asymptotic sorting-depth coefficient.
-/

@[expose] public section

namespace Kahale

theorem active_comparator_width_le {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨(net.comparators ++ [c]) ++ suffix.flatten⟩)
    (hactive : ∃ v : Fin n → Bool, net.exec v c.i = true ∧ net.exec v c.j = false) :
    c.j.val - c.i.val ≤ 2 ^ (suffix.length + 1) - 1 := by
  let post : ComparatorNetwork n := ⟨net.comparators ++ [c]⟩
  have hsorted (σ : Equiv.Perm (Fin n)) :
      (ComparatorNetwork.mk suffix.flatten).exec (post.exec σ) = id := by
    rw [← ComparatorNetwork.exec_append]
    exact sorting_rank_identity _ hs σ
  have hdisp (σ : Equiv.Perm (Fin n)) (i : Fin n) :
      (post.exec σ i).val < i.val + 2 ^ suffix.length ∧
        i.val < (post.exec σ i).val + 2 ^ suffix.length := by
    apply rank_cover_displacement post i (suffixReach suffix {i})
      (sorted_suffix_rank_cover post suffix hp hsorted i)
    simpa only [Finset.card_singleton, mul_one] using suffixReach_card suffix {i}
  obtain ⟨v, hvi, hvj⟩ := hactive
  obtain ⟨τ, ht⟩ := boolean_inversion_rank_witness net c.i c.j v hvi hvj
  obtain ⟨σ, ha⟩ := inverted_ranks_have_adjacent_witness net c.i c.j c.h τ ht
  have he : post.exec σ = c.apply (net.exec σ) := by
    change (ComparatorNetwork.mk (net.comparators ++ [c])).exec σ = _
    rw [ComparatorNetwork.exec_append]
    rfl
  have hadj : (post.exec σ c.i).val + 1 = (post.exec σ c.j).val := by
    rw [he]
    have hc : c.j ≠ c.i := ne_of_gt c.h
    simp only [Comparator.apply, if_true, if_neg hc]
    rcases ha with ha | ha
    · have hle : net.exec σ c.i ≤ net.exec σ c.j := by change _ ≤ _; omega
      simpa only [min_eq_left hle, max_eq_right hle] using ha
    · have hle : net.exec σ c.j ≤ net.exec σ c.i := by change _ ≤ _; omega
      simpa only [min_eq_right hle, max_eq_left hle] using ha
  have hi := (hdisp σ c.i).1
  have hj := (hdisp σ c.j).2
  rw [pow_succ]
  omega

end Kahale
