module

public import AKS.Paterson.SortedBins

/-! # Remaining prefix counts from a fixed deep allocation

Only deep wires with different actual and assigned coarse intervals can change
the expected prefix count left for the exactly sorted upper region.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem remaining_prefix_discrepancy {n : ℕ} (U D E : Finset (Fin n))
    (hdis : Disjoint U D) (hcover : U ∪ D = univ)
    (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (hsame : ∀ i ∈ D, i ∉ E → (P i ↔ Q i))
    {R C : ℕ} (hglobal : (univ.filter P).card = R)
    (hdeep : (D.filter Q).card = C) (hC : C ≤ R) :
    ((U.filter P).card : ℚ) - (R - C : ℕ) ≤ E.card ∧
      ((R - C : ℕ) : ℚ) - (U.filter P).card ≤ E.card := by
  have hPsub : D.filter P ⊆ D.filter Q ∪ E := by
    intro i hi
    obtain ⟨hiD, hiP⟩ := mem_filter.mp hi
    by_cases hiE : i ∈ E
    · exact mem_union_right _ hiE
    · exact mem_union_left _ (mem_filter.mpr ⟨hiD, (hsame i hiD hiE).mp hiP⟩)
  have hQsub : D.filter Q ⊆ D.filter P ∪ E := by
    intro i hi
    obtain ⟨hiD, hiQ⟩ := mem_filter.mp hi
    by_cases hiE : i ∈ E
    · exact mem_union_right _ hiE
    · exact mem_union_left _ (mem_filter.mpr ⟨hiD, (hsame i hiD hiE).mpr hiQ⟩)
  have hPcard := (card_le_card hPsub).trans (card_union_le _ _)
  have hQcard := (card_le_card hQsub).trans (card_union_le _ _)
  rw [hdeep] at hPcard hQcard
  have htotal : (U.filter P).card + (D.filter P).card = R := by
    rw [← card_union_of_disjoint (disjoint_filter_filter hdis), ← filter_union, hcover, hglobal]
  have hPcardQ : ((D.filter P).card : ℚ) ≤ C + E.card := by exact_mod_cast hPcard
  have hQcardQ : (C : ℚ) ≤ (D.filter P).card + E.card := by exact_mod_cast hQcard
  have htotalQ : ((U.filter P).card : ℚ) + (D.filter P).card = R := by exact_mod_cast htotal
  rw [Nat.cast_sub hC]
  constructor <;> linarith

theorem sorted_network_bin_wrong_bound {m n : ℕ} (net : ComparatorNetwork m)
    (hsort : ComparatorNetwork.Sorts.{0} net) (u : Fin m → Fin n)
    (a b lo hi : ℕ) (hb : b ≤ m) {E : ℚ} (hE : 0 ≤ E)
    (hlow : ((univ.filter (fun i ↦ (u i).val < lo)).card : ℚ) - a ≤ E)
    (hhigh : (b : ℚ) - (univ.filter (fun i ↦ (u i).val < hi)).card ≤ E) :
    ((univ.filter (fun i ↦ a ≤ i.val ∧ i.val < b ∧
      ((net.exec u i).val < lo ∨ hi ≤ (net.exec u i).val))).card : ℚ) ≤ 2 * E := by
  apply sorted_bin_wrong_bound (net.exec u) (hsort _ u) a b lo hi hb hE
  · rw [exec_filter_card net u (fun v ↦ v.val < lo)]
    exact hlow
  · rw [exec_filter_card net u (fun v ↦ v.val < hi)]
    exact hhigh

end Paterson.Bags
