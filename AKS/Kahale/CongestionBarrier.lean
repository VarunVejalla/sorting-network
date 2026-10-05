module

public import AKS.Kahale.RankCongestion

/-! # A limitation of the suffix reachability relaxation

If every source reaches every output, coalition Hall capacity supplies only
the total target cardinality constraint. This does not rule out improvements
from shorter suffixes or from intermediate-layer routing capacity.
-/

@[expose] public section

namespace Kahale

theorem complete_cover_hall {n : ℕ} (A B : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (hcard : A.card ≤ B.card)
    (hR : ∀ i ∈ A, R i = Finset.univ) :
    A.card ≤ ((A.biUnion R) ∩ B).card := by
  classical
  by_cases hA : A = ∅
  · simp [hA]
  have hu : A.biUnion R = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    rw [hR i hi]
    exact Finset.mem_univ j
  simpa only [hu, Finset.univ_inter] using hcard

theorem complete_cover_deficit_zero {n : ℕ} (A B : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (hcard : A.card ≤ B.card)
    (hR : ∀ i ∈ A, R i = Finset.univ) :
    A.card - ((A.biUnion R) ∩ B).card = 0 :=
  Nat.sub_eq_zero_of_le (complete_cover_hall A B R hcard hR)

end Kahale
