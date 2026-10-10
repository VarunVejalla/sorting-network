module

public import AKS.Kahale.CertificateCompatibility

/-! # Certificate witnesses for the closed pairwise union upper bound

A certificate for two wires, united with a certificate for a third wire,
certifies all three. Choosing each possible pair gives the three upper bounds
used in the experimental pair-matrix recurrence. This does not assert that
the pair matrix determines its exact next values or improve the depth bound.
-/

@[expose] public section

namespace Kahale

theorem zero_certificate_superset {n : ℕ} (net : ComparatorNetwork n)
    (i : Fin n) (S T : Finset (Fin n)) (hST : S ⊆ T)
    (hS : ZeroCertificate net i S) : ZeroCertificate net i T := by
  intro v hv
  exact hS v (fun j hj ↦ hv j (hST hj))

theorem one_certificate_superset {n : ℕ} (net : ComparatorNetwork n)
    (i : Fin n) (S T : Finset (Fin n)) (hST : S ⊆ T)
    (hS : OneCertificate net i S) : OneCertificate net i T := by
  intro v hv
  exact hS v (fun j hj ↦ hv j (hST hj))

theorem triple_zero_certificate_cover {n : ℕ} (net : ComparatorNetwork n)
    (i j k : Fin n) (S T : Finset (Fin n))
    (hi : ZeroCertificate net i S) (hj : ZeroCertificate net j S)
    (hk : ZeroCertificate net k T) :
    ∃ R : Finset (Fin n), R.card ≤ S.card + T.card ∧
      ZeroCertificate net i R ∧ ZeroCertificate net j R ∧
      ZeroCertificate net k R := by
  refine ⟨S ∪ T, Finset.card_union_le S T, ?_, ?_, ?_⟩
  · exact zero_certificate_superset net i S _ Finset.subset_union_left hi
  · exact zero_certificate_superset net j S _ Finset.subset_union_left hj
  · exact zero_certificate_superset net k T _ Finset.subset_union_right hk

theorem triple_one_certificate_cover {n : ℕ} (net : ComparatorNetwork n)
    (i j k : Fin n) (S T : Finset (Fin n))
    (hi : OneCertificate net i S) (hj : OneCertificate net j S)
    (hk : OneCertificate net k T) :
    ∃ R : Finset (Fin n), R.card ≤ S.card + T.card ∧
      OneCertificate net i R ∧ OneCertificate net j R ∧
      OneCertificate net k R := by
  refine ⟨S ∪ T, Finset.card_union_le S T, ?_, ?_, ?_⟩
  · exact one_certificate_superset net i S _ Finset.subset_union_left hi
  · exact one_certificate_superset net j S _ Finset.subset_union_left hj
  · exact one_certificate_superset net k T _ Finset.subset_union_right hk

theorem max_zero_certificate_pair_cover {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (k : Fin n) (S T : Finset (Fin n))
    (hi : ZeroCertificate net c.i S) (hk : ZeroCertificate net k S)
    (hj : ZeroCertificate net c.j T) :
    ∃ R : Finset (Fin n), R.card ≤ S.card + T.card ∧
      ZeroCertificate ⟨net.comparators ++ [c]⟩ c.j R ∧
      ZeroCertificate net k R := by
  obtain ⟨R, hcard, hiR, hkR, hjR⟩ :=
    triple_zero_certificate_cover net c.i k c.j S T hi hk hj
  exact ⟨R, hcard, (zero_certificate_max_append net c R).mpr ⟨hiR, hjR⟩, hkR⟩

theorem min_one_certificate_pair_cover {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (k : Fin n) (S T : Finset (Fin n))
    (hi : OneCertificate net c.i S) (hk : OneCertificate net k S)
    (hj : OneCertificate net c.j T) :
    ∃ R : Finset (Fin n), R.card ≤ S.card + T.card ∧
      OneCertificate ⟨net.comparators ++ [c]⟩ c.i R ∧
      OneCertificate net k R := by
  obtain ⟨R, hcard, hiR, hkR, hjR⟩ :=
    triple_one_certificate_cover net c.i k c.j S T hi hk hj
  exact ⟨R, hcard, (one_certificate_min_append net c R).mpr ⟨hiR, hjR⟩, hkR⟩

end Kahale
