module

public import AKS.Paterson.Subtree
public import AKS.Paterson.Fresh

/-! # Rank balance by finite global counting

A parent and a sibling subtree occupy disjoint registers. The subtree's
native values use part of a fixed global cohort, so at most the unused part
can occur in the parent. This connects the geometric intrusion estimate to
the large-cohort halver hypothesis. The subtree deficit must still be proved
for the rounded scheduler, including its cold storage.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem disjoint_cohort_count {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    (P : Fin n → Prop) [DecidablePred P] :
    ((S.filter P).card : ℚ) + T.card ≤
      (univ.filter P).card + (T.filter (fun i ↦ ¬ P i)).card := by
  have hp : (T.filter P).card + (T.filter (fun i ↦ ¬ P i)).card = T.card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_union, mem_filter]
      tauto
    · rw [disjoint_filter]
      intro i _ hi hni
      exact hni hi
  have hsum : (S.filter P).card + (T.filter P).card ≤ (univ.filter P).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter hST)]
    apply card_le_card
    intro i hi
    simp only [mem_union, mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.elim And.right And.right
  have hpQ : ((T.filter P).card : ℚ) + (T.filter (fun i ↦ ¬ P i)).card = T.card := by
    exact_mod_cast hp
  have hsQ : ((S.filter P).card : ℚ) + (T.filter P).card ≤ (univ.filter P).card := by
    exact_mod_cast hsum
  linarith

/-- Count enough members of the complementary input cohort from the sibling
deficit, subtree intrusion, and old parent strangers. This is independent of
any comparator network or assumption about destination stranger counts. -/
theorem cohort_balance {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    (P Q O : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred O]
    (hcover : ∀ i ∈ S, Q i → P i ∨ O i)
    {half reserve intrusion old : ℚ}
    (hsize : (S.card : ℚ) = 2 * half)
    (hdeficit : ((univ.filter P).card : ℚ) - T.card ≤ half + reserve)
    (hintrusion : ((T.filter (fun i ↦ ¬ P i)).card : ℚ) ≤ intrusion)
    (hold : ((S.filter O).card : ℚ) ≤ old) :
    half - reserve - intrusion - old ≤ ((S.filter (fun i ↦ ¬ Q i)).card : ℚ) := by
  have hcohort := disjoint_cohort_count S T hST P
  have hsub : S.filter Q ⊆ S.filter P ∪ S.filter O := by
    intro i hi
    obtain ⟨hiS, hiQ⟩ := mem_filter.mp hi
    exact (hcover i hiS hiQ).elim
      (fun h ↦ mem_union_left _ (mem_filter.mpr ⟨hiS, h⟩))
      (fun h ↦ mem_union_right _ (mem_filter.mpr ⟨hiS, h⟩))
  have hq : ((S.filter Q).card : ℚ) ≤ (S.filter P).card + (S.filter O).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hpartition : ((S.filter Q).card : ℚ) + (S.filter (fun i ↦ ¬ Q i)).card = S.card := by
    have h : (S.filter Q).card + (S.filter (fun i ↦ ¬ Q i)).card = S.card := by
      rw [← card_union_of_disjoint]
      · congr 1
        ext i
        simp only [mem_union, mem_filter]
        tauto
      · rw [disjoint_filter]
        intro i _ hi hni
        exact hni hi
    exact_mod_cast h
  linarith

/-- The narrower rounded invariant leaves room for bounded errors in subtree
conservation and in the parent's actual half size. The resulting supported
cohort is the same one used in the depth-263 first halver. -/
theorem fast_cohort_slack {cap half reserve intrusion old : ℚ}
    (hcap : fastParams.minCapacity ≤ cap)
    (hhalf : cap / 2 - 64 ≤ half)
    (hreserve : reserve ≤ cap / (4 * fastParams.A ^ 2 - 1) / 2 + 32)
    (hintrusion : intrusion ≤
      2 * fastParams.mu * fastParams.delta * fastParams.A ^ 2 /
        (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) * cap)
    (hold : old ≤ fastParams.mu * cap) :
    patersonAlpha0 * half ≤ half - reserve - intrusion - old := by
  norm_num [fastParams, patersonAlpha0_eq, patersonDelta0,
    patersonTailError, patersonDelta1, patersonDelta2, patersonDelta3,
    patersonDelta4, patersonDelta5] at *
  linarith

end Paterson.Bags
