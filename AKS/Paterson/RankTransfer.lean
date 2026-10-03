module

public import AKS.Separator.PatersonGood
public import AKS.Bags.SepBridge

/-! # Supported separators on ambient rank intervals

Bag inputs are injective selections of global ranks, rather than local
permutations. These lemmas transfer the separator guarantee to their actual
extreme cohorts, following the local-rank argument of Paterson (1990).
-/

@[expose] public section

namespace Paterson

theorem supported_injective_initial {m n fringe : ℕ}
    {net : ComparatorNetwork m} {support err : ℝ}
    (hnet : IsSupportedSeparator net fringe support err)
    (u : Fin m → Fin n) (hu : Function.Injective u) (threshold : ℕ)
    (ha : ((Finset.univ.filter (fun i ↦ (u i).val < threshold)).card : ℝ) ≤
      support * m) :
    ((Finset.univ.filter (fun pos : Fin m ↦
      fringe ≤ pos.val ∧ (net.exec u pos).val < threshold)).card : ℝ) ≤
      err * ↑(Finset.univ.filter (fun i ↦ (u i).val < threshold)).card := by
  obtain ⟨g, σ, hg, _, hexec, hcount⟩ := injective_monotone_perm_decomp net u hu
  let a := (Finset.univ.filter (fun i ↦ (u i).val < threshold)).card
  have ha_eq : a = (Finset.univ.filter (fun r ↦ (g r).val < threshold)).card :=
    hcount (fun v ↦ v.val < threshold)
  have hthresh (r : Fin m) : (g r).val < threshold ↔ r.val < a := by
    rw [ha_eq]
    exact strictMono_threshold hg threshold r
  have hfilter : Finset.univ.filter (fun pos : Fin m ↦
      fringe ≤ pos.val ∧ (net.exec u pos).val < threshold) =
      Finset.univ.filter (fun pos : Fin m ↦
      fringe ≤ pos.val ∧ (net.exec σ pos).val < a) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply and_congr_right
    intro _
    rw [hexec]
    exact hthresh _
  rw [hfilter]
  exact (hnet σ).1 a ha

theorem supported_injective_final {m n fringe : ℕ}
    {net : ComparatorNetwork m} {support err : ℝ}
    (hnet : IsSupportedSeparator net fringe support err)
    (u : Fin m → Fin n) (hu : Function.Injective u) (threshold : ℕ)
    (ha : ((Finset.univ.filter (fun i ↦ threshold ≤ (u i).val)).card : ℝ) ≤
      support * m) :
    ((Finset.univ.filter (fun pos : Fin m ↦
      pos.val < m - fringe ∧ threshold ≤ (net.exec u pos).val)).card : ℝ) ≤
      err * ↑(Finset.univ.filter (fun i ↦ threshold ≤ (u i).val)).card := by
  obtain ⟨g, σ, hg, _, hexec, hcount⟩ := injective_monotone_perm_decomp net u hu
  let a := (Finset.univ.filter (fun i ↦ threshold ≤ (u i).val)).card
  have ha_eq : a = (Finset.univ.filter (fun r ↦ threshold ≤ (g r).val)).card :=
    hcount (fun v ↦ threshold ≤ v.val)
  have hthresh (r : Fin m) : threshold ≤ (g r).val ↔ m - a ≤ r.val := by
    rw [ha_eq]
    exact strictMono_reverse_threshold hg threshold r
  have hfilter : Finset.univ.filter (fun pos : Fin m ↦
      pos.val < m - fringe ∧ threshold ≤ (net.exec u pos).val) =
      Finset.univ.filter (fun pos : Fin m ↦
      pos.val < m - fringe ∧ m - a ≤ (net.exec σ pos).val) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply and_congr_right
    intro _
    rw [hexec]
    exact hthresh _
  rw [hfilter]
  exact (hnet σ).2 a ha

end Paterson
