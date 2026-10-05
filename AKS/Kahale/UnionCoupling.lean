module

public import AKS.Kahale.RankCrossing
public import AKS.Kahale.CertificateCompatibility

/-! # Shared-universe coupling of the two certificate union costs

An active standard comparator has a one certificate on its min output and a
zero certificate on its max output with total size at most n+2. The proof
crosses adjacent ranks and uses two complementary rank thresholds.
This local constraint is not an improved asymptotic depth bound.
-/

@[expose] public section

namespace Kahale

open Finset

theorem rank_threshold_certificate_pair {n : ℕ} (net : ComparatorNetwork n)
    (i j : Fin n) (σ : Equiv.Perm (Fin n)) (lo hi : Fin n)
    (hadj : lo.val + 1 = hi.val)
    (hloi : lo ≤ net.exec σ i) (hloj : lo ≤ net.exec σ j)
    (hhii : net.exec σ i ≤ hi) (hhij : net.exec σ j ≤ hi) :
    ∃ S T : Finset (Fin n), ZeroCertificate net i S ∧ ZeroCertificate net j S ∧
      OneCertificate net i T ∧ OneCertificate net j T ∧ S.card + T.card = n + 2 := by
  classical
  let f : Fin n → Bool := fun k ↦ decide (hi < k)
  let g : Fin n → Bool := fun k ↦ decide (lo ≤ k)
  have hf : Monotone f := by
    intro a b hab
    by_cases h : hi < a
    · simp [f, h, lt_of_lt_of_le h hab]
    · simp [f, h]
  have hg : Monotone g := by
    intro a b hab
    by_cases h : lo ≤ a
    · simp [g, h, h.trans hab]
    · simp [g, h]
  let S := univ.filter (fun k ↦ σ k ≤ hi)
  let T := univ.filter (fun k ↦ lo ≤ σ k)
  have heS : univ.filter (fun k ↦ (f ∘ σ) k = false) = S := by
    ext k
    simp [S, f, not_lt]
  have heT : univ.filter (fun k ↦ (g ∘ σ) k = true) = T := by
    ext k
    simp [T, g]
  have hzi : ZeroCertificate net i S := by
    rw [← heS]
    apply input_support_zero_certificate
    rw [ComparatorNetwork.exec_comp_mono net hf]
    simp [f, not_lt, hhii]
  have hzj : ZeroCertificate net j S := by
    rw [← heS]
    apply input_support_zero_certificate
    rw [ComparatorNetwork.exec_comp_mono net hf]
    simp [f, not_lt, hhij]
  have hoi : OneCertificate net i T := by
    rw [← heT]
    apply input_support_one_certificate
    rw [ComparatorNetwork.exec_comp_mono net hg]
    simp [g, hloi]
  have hoj : OneCertificate net j T := by
    rw [← heT]
    apply input_support_one_certificate
    rw [ComparatorNetwork.exec_comp_mono net hg]
    simp [g, hloj]
  have hcS : S.card = (Iic hi).card := by
    apply card_nbij' σ σ.symm
    · intro k hk
      exact mem_Iic.mpr (mem_filter.mp hk).2
    · intro k hk
      simp only [S, mem_coe, mem_filter, mem_univ, true_and, σ.apply_symm_apply]
      exact mem_Iic.mp hk
    · intro k _; exact σ.symm_apply_apply k
    · intro k _; exact σ.apply_symm_apply k
  have hcT : T.card = (Ici lo).card := by
    apply card_nbij' σ σ.symm
    · intro k hk
      exact mem_Ici.mpr (mem_filter.mp hk).2
    · intro k hk
      simp only [T, mem_coe, mem_filter, mem_univ, true_and, σ.apply_symm_apply]
      exact mem_Ici.mp hk
    · intro k _; exact σ.symm_apply_apply k
    · intro k _; exact σ.apply_symm_apply k
  refine ⟨S, T, hzi, hzj, hoi, hoj, ?_⟩
  rw [hcS, hcT, Fin.card_Iic, Fin.card_Ici]
  have hl := lo.isLt
  omega

theorem active_comparator_union_cost_coupling {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n)
    (hactive : ∃ v : Fin n → Bool, net.exec v c.i = true ∧ net.exec v c.j = false) :
    ∃ S T : Finset (Fin n),
      ZeroCertificate ⟨net.comparators ++ [c]⟩ c.j S ∧
      OneCertificate ⟨net.comparators ++ [c]⟩ c.i T ∧
      S.card + T.card ≤ n + 2 := by
  obtain ⟨v, hvi, hvj⟩ := hactive
  obtain ⟨τ, ht⟩ := boolean_inversion_rank_witness net c.i c.j v hvi hvj
  obtain ⟨σ, ha | ha⟩ := inverted_ranks_have_adjacent_witness net c.i c.j c.h τ ht
  · have hle : net.exec σ c.i ≤ net.exec σ c.j := by change _ ≤ _; omega
    obtain ⟨S, T, hzi, hzj, hoi, hoj, hc⟩ := rank_threshold_certificate_pair net c.i c.j σ
      (net.exec σ c.i) (net.exec σ c.j) ha le_rfl hle hle le_rfl
    exact ⟨S, T, (zero_certificate_max_append net c S).2 ⟨hzi, hzj⟩,
      (one_certificate_min_append net c T).2 ⟨hoi, hoj⟩, hc.le⟩
  · have hle : net.exec σ c.j ≤ net.exec σ c.i := by change _ ≤ _; omega
    obtain ⟨S, T, hzi, hzj, hoi, hoj, hc⟩ := rank_threshold_certificate_pair net c.i c.j σ
      (net.exec σ c.j) (net.exec σ c.i) ha hle le_rfl le_rfl hle
    exact ⟨S, T, (zero_certificate_max_append net c S).2 ⟨hzi, hzj⟩,
      (one_certificate_min_append net c T).2 ⟨hoi, hoj⟩, hc.le⟩

theorem active_final_comparator_adjacent {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n)
    (hs : ComparatorNetwork.Sorts.{0} ⟨net.comparators ++ [c]⟩)
    (hactive : ∃ v : Fin n → Bool, net.exec v c.i = true ∧ net.exec v c.j = false) :
    c.j.val = c.i.val + 1 := by
  obtain ⟨S, T, hz, ho, hc⟩ := active_comparator_union_cost_coupling net c hactive
  have hS := sorting_zero_certificate_card _ hs c.j S hz
  have hT := sorting_one_certificate_card _ hs c.i T ho
  have hi := c.i.isLt
  have hj : c.i.val < c.j.val := c.h
  omega

end Kahale
