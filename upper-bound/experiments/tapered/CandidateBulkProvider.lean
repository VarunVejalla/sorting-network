import CandidateBulkFail
import PaddedSeparator
import AKS.Chvatal.PackNodeSpec2

namespace Tapered945
open Chvatal

open Classical in
theorem conjunction_fail_fraction {m n : Nat} (P Q : Scramble m n → Prop)
    (bP bQ : Real)
    (hP : ((Finset.univ.filter (fun σ : Scramble m n => ¬ P σ)).card : Real) ≤
      bP*(Fintype.card (Scramble m n) : Real))
    (hQ : ((Finset.univ.filter (fun σ : Scramble m n => ¬ Q σ)).card : Real) ≤
      bQ*(Fintype.card (Scramble m n) : Real)) :
    ((Finset.univ.filter (fun σ : Scramble m n => ¬ (P σ ∧ Q σ))).card : Real) ≤
      (bP+bQ)*(Fintype.card (Scramble m n) : Real) := by
  simp only [not_and_or, Finset.filter_or]
  have hc := (Nat.cast_le (α := Real)).mpr (Finset.card_union_le
    (Finset.univ.filter (fun σ : Scramble m n => ¬ P σ))
    (Finset.univ.filter (fun σ : Scramble m n => ¬ Q σ)))
  push_cast at hc
  linarith

open Classical in
/-- Separate auxiliary contracts can be imposed on both physical scrambles,
in both flip orientations, using their actual failure fractions. -/
theorem bulk_pair_with_two_aux_of_gaps {m n : Nat} (hm : 0 < m) (hn : 16 ≤ n)
    (E d lam F₁ F₂ : Real) (hE : 0 < E) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hgap1 : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*E^2)
    (hgap2 : Real.log (2*((m : Real)+1))+1/2 ≤ (m : Real)*
      (lam*d/2-lam^2*(1/2+2*lam/9)*E/2))
    (PF₁ PF₂ : Scramble m n → Prop) (hF₁ : 1/1000+F₁ < 1/2) (hF₂ : 1/1000+F₂ < 1/2)
    (hPF₁ : ((Finset.univ.filter (fun σ : Scramble m n => ¬ PF₁ σ)).card : Real) ≤
      F₁*(Fintype.card (Scramble m n) : Real))
    (hPF₂ : ((Finset.univ.filter (fun σ : Scramble m n => ¬ PF₂ σ)).card : Real) ≤
      F₂*(Fintype.card (Scramble m n) : Real)) :
    ∃ σ₁ σ₂ : Scramble m n,
      (PF₁ σ₁ ∧ PF₂ σ₂ ∧ HasPackSemanticPropertyB2 (by omega : 0<n) σ₁ σ₂ d) ∧
      (PF₁ (flipScramble σ₁) ∧ PF₂ (flipScramble σ₂) ∧
        HasPackSemanticPropertyB2 (by omega : 0<n) (flipScramble σ₁) (flipScramble σ₂) d) := by
  have h1 := conjunction_fail_fraction
    (fun σ : Scramble m n => ExactBulk σ (fun _ _ => True) E) PF₁ (1/1000) F₁
    (exact_round1_fail_fraction hm hn E hE hgap1) hPF₁
  have h2 := conjunction_fail_fraction
    (fun σ : Scramble m n => ExactBulk σ (IntermediateAdm E) d) PF₂ (1/1000) F₂
    (exact_round2_fail_fraction hm hn E d lam hl0 hl1 hgap2) hPF₂
  obtain ⟨σ₁, hs1, hs1f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (fun _ _ => True) E ∧ PF₁ σ)
    (c := 1/1000+F₁) hF₁ (by convert h1 using 2; congr 1; ext σ; simp)
  obtain ⟨σ₂, hs2, hs2f⟩ := exists_and_flip
    (fun σ : Scramble m n => ExactBulk σ (IntermediateAdm E) d ∧ PF₂ σ)
    (c := 1/1000+F₂) hF₂ (by convert h2 using 2; congr 1; ext σ; simp)
  exact ⟨σ₁, σ₂, ⟨hs1.2, hs2.2, semantic_B2_of_exact (by omega) hs1.1 hs2.1⟩,
    ⟨hs1f.2, hs2f.2, semantic_B2_of_exact (by omega) hs1f.1 hs2f.1⟩⟩

/-- Actual padded B-only separators at the candidate price. This theorem
asserts no fringe F guarantee and no global sorting bound. -/
theorem candidate_padded_separator_exists (a : Nat) (ha : 2^38 ≤ a) :
    ∃ w : PaddedSeparatorWitness a (1/2^21), w.network.depth ≤ 1890 := by
  obtain ⟨w⟩ := large_padded_separator_nonempty a ha (1/2^21) (by norm_num)
    (fun m n _ hn hm _ _ => candidate_bulk_pair_exists hm hn)
  refine ⟨w, ?_⟩
  have hp := pack2_depth_le w.rows w.columns w.column_pos w.scramble₁ w.scramble₂ 35 w.rows_hi
  have hd := w.depth_le.trans hp
  norm_num at hd
  exact hd

end Tapered945
