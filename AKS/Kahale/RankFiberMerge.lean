module

public import AKS.Kahale.RankInformation
public import AKS.Kahale.ComparisonTrace

/-! # Exact merging of rank fibers

This counting identity is a foundation for entropy accounting, not an
improvement of the asymptotic depth lower bound.
-/

@[expose] public section

namespace Kahale

theorem rankFiberSize_append_comparator {n : ℕ} (pre : ComparatorNetwork n)
    (c : Comparator n) (w : Fin n → Fin n) (hw : w c.i < w c.j) :
    rankFiberSize ⟨pre.comparators ++ [c]⟩ w =
      rankFiberSize pre w + rankFiberSize pre (fun i ↦ w (Equiv.swap c.i c.j i)) := by
  classical
  let A := Finset.univ.filter (fun v : Fin n → Fin n ↦
    Function.Injective v ∧ pre.exec v = w)
  let B := Finset.univ.filter (fun v : Fin n → Fin n ↦
    Function.Injective v ∧ pre.exec v = fun i ↦ w (Equiv.swap c.i c.j i))
  have hsplit : Finset.univ.filter (fun v : Fin n → Fin n ↦
      Function.Injective v ∧ (ComparatorNetwork.mk (pre.comparators ++ [c])).exec v = w)
      = A ∪ B := by
    ext v
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    have he : (ComparatorNetwork.mk (pre.comparators ++ [c])).exec v = c.apply (pre.exec v) := by
      simp [ComparatorNetwork.exec, List.foldl_append]
    rw [he, comparator_strict_preimages c w (pre.exec v) hw]
    exact and_or_left
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v ha hb
    have ha' : pre.exec v = w := (Finset.mem_filter.mp ha).2.2
    have hb' : pre.exec v = fun i ↦ w (Equiv.swap c.i c.j i) :=
      (Finset.mem_filter.mp hb).2.2
    have hi := congrFun (ha'.symm.trans hb') c.i
    have heq : w c.i = w c.j := by simpa using hi
    exact (ne_of_lt hw) heq
  unfold rankFiberSize
  rw [hsplit, Finset.card_union_of_disjoint hd]

end Kahale
