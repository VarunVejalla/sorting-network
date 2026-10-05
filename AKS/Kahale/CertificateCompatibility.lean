module

public import AKS.Kahale.Certificates
public import AKS.Kahale.RankInputs
public import AKS.Sort.ZeroOne

/-! # Joint zero/one certificates and sorting

A zero certificate on a later output and a one certificate on an earlier
output must intersect in a sorting network. Disjoint certificates give an
explicit Boolean inversion. These statements retain input identities, which
the scalar height method discards.
-/

@[expose] public section

namespace Kahale

open Finset

def OneCertificate {n : ℕ} (net : ComparatorNetwork n) (i : Fin n)
    (S : Finset (Fin n)) : Prop :=
  ∀ v : Fin n → Bool, (∀ j ∈ S, v j = true) → net.exec v i = true

theorem exec_pointwise_mono {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (u v : Fin n → α) (h : ∀ i, u i ≤ v i) :
    ∀ i, net.exec u i ≤ net.exec v i := by
  obtain ⟨cs⟩ := net
  induction cs generalizing u v with
  | nil => exact h
  | cons c cs ih =>
    apply ih (c.apply u) (c.apply v)
    intro i
    simp only [Comparator.apply]
    split_ifs
    · exact min_le_min (h c.i) (h c.j)
    · exact max_le_max (h c.i) (h c.j)
    · exact h i

theorem input_support_zero_certificate {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → Bool) (i : Fin n) (hi : net.exec v i = false) :
    ZeroCertificate net i (univ.filter (fun k ↦ v k = false)) := by
  intro u hu
  have h : ∀ k, u k ≤ v k := by
    intro k
    cases hv : v k
    · simp [hu k (mem_filter.mpr ⟨mem_univ _, hv⟩)]
    · simp
  have ho := exec_pointwise_mono net u v h i
  rw [hi] at ho
  cases he : net.exec u i
  · rfl
  · rw [he] at ho
    exact False.elim ((show ¬(true : Bool) ≤ false by decide) ho)

theorem input_support_one_certificate {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → Bool) (i : Fin n) (hi : net.exec v i = true) :
    OneCertificate net i (univ.filter (fun k ↦ v k = true)) := by
  intro u hu
  have h : ∀ k, v k ≤ u k := by
    intro k
    cases hv : v k
    · simp
    · simp [hu k (mem_filter.mpr ⟨mem_univ _, hv⟩)]
  have ho := exec_pointwise_mono net v u h i
  rw [hi] at ho
  cases he : net.exec u i
  · rw [he] at ho
    exact False.elim ((show ¬(true : Bool) ≤ false by decide) ho)
  · rfl

theorem zero_certificate_iff_extremal_input {n : ℕ} (net : ComparatorNetwork n)
    (i : Fin n) (S : Finset (Fin n)) :
    ZeroCertificate net i S ↔
      net.exec (fun k ↦ if k ∈ S then false else true) i = false := by
  classical
  constructor
  · intro h
    exact h _ (by intro k hk; simp [hk])
  · intro h
    have hc := input_support_zero_certificate net _ i h
    have he : univ.filter (fun k : Fin n ↦ (if k ∈ S then false else true) = false) = S := by
      ext k
      simp
    rwa [he] at hc

theorem one_certificate_iff_extremal_input {n : ℕ} (net : ComparatorNetwork n)
    (i : Fin n) (T : Finset (Fin n)) :
    OneCertificate net i T ↔
      net.exec (fun k ↦ if k ∈ T then true else false) i = true := by
  classical
  constructor
  · intro h
    exact h _ (by intro k hk; simp [hk])
  · intro h
    have hc := input_support_one_certificate net _ i h
    have he : univ.filter (fun k : Fin n ↦ (if k ∈ T then true else false) = true) = T := by
      ext k
      simp
    rwa [he] at hc

theorem zero_certificate_min_append {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (S : Finset (Fin n)) :
    ZeroCertificate ⟨net.comparators ++ [c]⟩ c.i S ↔
      ZeroCertificate net c.i S ∨ ZeroCertificate net c.j S := by
  classical
  simp only [zero_certificate_iff_extremal_input]
  rw [ComparatorNetwork.exec_append]
  simp only [ComparatorNetwork.exec, List.foldl_cons, List.foldl_nil,
    Comparator.apply, if_true]
  cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ S then false else true) c.i <;>
    cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ S then false else true) c.j <;> decide

theorem zero_certificate_max_append {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (S : Finset (Fin n)) :
    ZeroCertificate ⟨net.comparators ++ [c]⟩ c.j S ↔
      ZeroCertificate net c.i S ∧ ZeroCertificate net c.j S := by
  classical
  simp only [zero_certificate_iff_extremal_input]
  rw [ComparatorNetwork.exec_append]
  have hc : c.j ≠ c.i := ne_of_gt c.h
  simp only [ComparatorNetwork.exec, List.foldl_cons, List.foldl_nil,
    Comparator.apply, if_neg hc]
  cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ S then false else true) c.i <;>
    cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ S then false else true) c.j <;> decide

theorem one_certificate_min_append {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (T : Finset (Fin n)) :
    OneCertificate ⟨net.comparators ++ [c]⟩ c.i T ↔
      OneCertificate net c.i T ∧ OneCertificate net c.j T := by
  classical
  simp only [one_certificate_iff_extremal_input]
  rw [ComparatorNetwork.exec_append]
  simp only [ComparatorNetwork.exec, List.foldl_cons, List.foldl_nil,
    Comparator.apply, if_true]
  cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ T then true else false) c.i <;>
    cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ T then true else false) c.j <;> decide

theorem one_certificate_max_append {n : ℕ} (net : ComparatorNetwork n)
    (c : Comparator n) (T : Finset (Fin n)) :
    OneCertificate ⟨net.comparators ++ [c]⟩ c.j T ↔
      OneCertificate net c.i T ∨ OneCertificate net c.j T := by
  classical
  simp only [one_certificate_iff_extremal_input]
  rw [ComparatorNetwork.exec_append]
  have hc : c.j ≠ c.i := ne_of_gt c.h
  simp only [ComparatorNetwork.exec, List.foldl_cons, List.foldl_nil,
    Comparator.apply, if_neg hc]
  cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ T then true else false) c.i <;>
    cases net.comparators.foldl (fun v c ↦ c.apply v)
      (fun k ↦ if k ∈ T then true else false) c.j <;> decide

theorem disjoint_certificates_inversion {n : ℕ} (net : ComparatorNetwork n)
    (i j : Fin n) (S T : Finset (Fin n))
    (hz : ZeroCertificate net j S) (ho : OneCertificate net i T)
    (hd : Disjoint S T) :
    ∃ v : Fin n → Bool, net.exec v i = true ∧ net.exec v j = false := by
  classical
  let v : Fin n → Bool := fun k ↦ if k ∈ T then true else false
  refine ⟨v, ho v (by intro k hk; simp [v, hk]), hz v ?_⟩
  intro k hk
  have ht : k ∉ T := fun hkt ↦ Finset.disjoint_left.mp hd hk hkt
  simp [v, ht]

/-- One certificates are exactly the hitting sets of the zero-certificate family. -/
theorem one_certificate_iff_hits_zero_family {n : ℕ} (net : ComparatorNetwork n)
    (i : Fin n) (T : Finset (Fin n)) :
    OneCertificate net i T ↔
      ∀ S : Finset (Fin n), ZeroCertificate net i S → ¬Disjoint S T := by
  constructor
  · intro ho S hz hd
    obtain ⟨v, hi, hj⟩ := disjoint_certificates_inversion net i i S T hz ho hd
    rw [hi] at hj
    contradiction
  · intro h v hv
    cases hi : net.exec v i
    · apply False.elim
      apply h _ (input_support_zero_certificate net v i hi)
      apply Finset.disjoint_left.mpr
      intro k hk hkt
      have hz := (mem_filter.mp hk).2
      have ho := hv k hkt
      rw [hz] at ho
      contradiction
    · rfl

theorem sorting_certificates_intersect {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (i j : Fin n) (hij : i ≤ j)
    (S T : Finset (Fin n)) (hz : ZeroCertificate net j S)
    (ho : OneCertificate net i T) : ¬Disjoint S T := by
  intro hd
  obtain ⟨v, hi, hj⟩ := disjoint_certificates_inversion net i j S T hz ho hd
  have h := hs Bool v hij
  rw [hi, hj] at h
  exact (show ¬(true : Bool) ≤ false by decide) h

theorem sorts_iff_certificates_intersect {n : ℕ} (net : ComparatorNetwork n) :
    ComparatorNetwork.Sorts.{0} net ↔
      ∀ (i j : Fin n), i ≤ j → ∀ (S T : Finset (Fin n)),
        ZeroCertificate net j S → OneCertificate net i T → ¬Disjoint S T := by
  constructor
  · exact sorting_certificates_intersect net
  · intro h
    apply zero_one_principle
    intro v i j hij
    cases hi : net.exec v i <;> cases hj : net.exec v j <;> try decide
    have hz := input_support_zero_certificate net v j hj
    have ho := input_support_one_certificate net v i hi
    apply False.elim
    apply h i j hij _ _ hz ho
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    have h₁ := (mem_filter.mp hk₁).2
    have h₂ := (mem_filter.mp hk₂).2
    rw [h₁] at h₂
    contradiction

theorem sorting_bool_zero_count {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (v : Fin n → Bool) :
    (univ.filter (fun k ↦ net.exec v k = false)).card =
      (univ.filter (fun k ↦ v k = false)).card := by
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g := v ∘ σ.symm
  have hv : v = g ∘ σ := by funext k; simp [g]
  have he : net.exec v = g := by
    rw [hv, ComparatorNetwork.exec_comp_mono net hg, sorting_rank_identity net hs σ]
    rfl
  rw [he]
  exact permuted_zero_count v σ

theorem sorting_zero_certificate_card {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (i : Fin n) (S : Finset (Fin n))
    (hz : ZeroCertificate net i S) : i.val + 1 ≤ S.card := by
  classical
  let v : Fin n → Bool := fun k ↦ if k ∈ S then false else true
  have hv : (univ.filter (fun k ↦ v k = false)) = S := by ext k; simp [v]
  have hzero := hz v (by intro k hk; simp [v, hk])
  have hr := monotone_zero_rank (net.exec v) (hs Bool v) i hzero
  rw [sorting_bool_zero_count net hs v, hv] at hr
  omega

theorem sorting_one_certificate_card {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (i : Fin n) (T : Finset (Fin n))
    (ho : OneCertificate net i T) : n - i.val ≤ T.card := by
  classical
  let v : Fin n → Bool := fun k ↦ if k ∈ T then true else false
  have hv : (univ.filter (fun k ↦ v k = false)) = Tᶜ := by ext k; simp [v]
  have hone := ho v (by intro k hk; simp [v, hk])
  have hsub : univ.filter (fun k ↦ net.exec v k = false) ⊆ Finset.Iio i := by
    intro k hk
    have hkz := (mem_filter.mp hk).2
    apply Finset.mem_Iio.mpr
    by_contra hki
    have hle := hs Bool v (le_of_not_gt hki)
    rw [hone, hkz] at hle
    exact (show ¬(true : Bool) ≤ false by decide) hle
  have hc := Finset.card_le_card hsub
  rw [sorting_bool_zero_count net hs v, hv, Finset.card_compl, Fin.card_Iio] at hc
  have ht : T.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  simp only [Fintype.card_fin] at hc
  omega

/-- Requiring the correct lower sizes for *all* zero and one certificates
    is already equivalent to full sorting, unlike one tracked height. -/
theorem sorts_iff_certificate_card_bounds {n : ℕ} (net : ComparatorNetwork n) :
    ComparatorNetwork.Sorts.{0} net ↔
      (∀ (i : Fin n) (S : Finset (Fin n)), ZeroCertificate net i S → i.val + 1 ≤ S.card) ∧
      (∀ (i : Fin n) (T : Finset (Fin n)), OneCertificate net i T → n - i.val ≤ T.card) := by
  constructor
  · intro hs
    exact ⟨sorting_zero_certificate_card net hs, sorting_one_certificate_card net hs⟩
  · rintro ⟨hz, ho⟩
    apply (sorts_iff_certificates_intersect net).2
    intro i j hij S T hS hT hd
    have hs := hz j S hS
    have ht := ho i T hT
    have hc : (S ∪ T).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (S ∪ T))
    rw [Finset.card_union_of_disjoint hd] at hc
    have hi := i.isLt
    have hijv : i.val ≤ j.val := hij
    omega

end Kahale
