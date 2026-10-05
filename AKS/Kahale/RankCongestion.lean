module

public import AKS.Kahale.Fanout
public import AKS.Kahale.CertificateCompatibility

/-! # Simultaneous rank capacity at a suffix cut

Rank values are distinct, so a coalition of prefix wires cannot share too
few reachable output ranks. The Boolean and certificate versions specialize
this necessary Hall inequality to the first k output ranks. This is not an
improved asymptotic sorting-depth lower bound.
-/

@[expose] public section

namespace Kahale

open Finset

theorem rank_cover_hall {n : ℕ} (pre : ComparatorNetwork n)
    (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (k : ℕ)
    (hA : ∀ i ∈ A, (pre.exec σ i).val < k)
    (hR : ∀ i ∈ A, pre.exec σ i ∈ R i) :
    A.card ≤ ((A.biUnion R).filter (fun j ↦ j.val < k)).card := by
  classical
  have hi := pre.exec_injective σ.injective
  calc
    A.card = (A.image (pre.exec σ)).card := (card_image_of_injective A hi).symm
    _ ≤ ((A.biUnion R).filter (fun j ↦ j.val < k)).card := by
      apply card_le_card
      intro j hj
      obtain ⟨i, hiA, rfl⟩ := mem_image.mp hj
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, hiA, hR i hiA⟩, hA i hiA⟩

theorem sorted_suffix_zero_hall {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨pre.comparators ++ suffix.flatten⟩)
    (v : Fin n → Bool) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, pre.exec v i = false) :
    A.card ≤ ((A.biUnion (fun i ↦ suffixReach suffix {i})).filter
      (fun j ↦ j.val < (univ.filter (fun i ↦ v i = false)).card)).card := by
  classical
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g := v ∘ σ.symm
  have hv : v = g ∘ σ := by funext i; simp [g]
  have hsorted (τ : Equiv.Perm (Fin n)) :
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec τ) = id := by
    rw [← ComparatorNetwork.exec_append]
    exact sorting_rank_identity _ hs τ
  apply rank_cover_hall pre σ A (fun i ↦ suffixReach suffix {i})
  · intro i hi
    have hzero := hA i hi
    rw [hv, ComparatorNetwork.exec_comp_mono pre hg] at hzero
    have hr := monotone_zero_rank g hg (pre.exec σ i) hzero
    have hc := permuted_zero_count v σ
    change (univ.filter (fun j ↦ g j = false)).card = _ at hc
    rwa [hc] at hr
  · intro i _
    exact sorted_suffix_rank_cover pre suffix hp hsorted i σ

theorem sorted_suffix_certificate_hall {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨pre.comparators ++ suffix.flatten⟩)
    (A S : Finset (Fin n)) (hA : ∀ i ∈ A, ZeroCertificate pre i S) :
    A.card ≤ ((A.biUnion (fun i ↦ suffixReach suffix {i})).filter
      (fun j ↦ j.val < S.card)).card := by
  classical
  let v : Fin n → Bool := fun i ↦ if i ∈ S then false else true
  have hv : univ.filter (fun i ↦ v i = false) = S := by ext i; simp [v]
  have hzero (i : Fin n) (hi : i ∈ A) : pre.exec v i = false :=
    hA i hi v (by intro j hj; simp [v, hj])
  have hh := sorted_suffix_zero_hall pre suffix hp hs v A hzero
  simpa only [hv] using hh

end Kahale
