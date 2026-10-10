module

public import AKS.Halver.PatersonJointTail
public import AKS.Separator.FromHalverDefs

/-! # Restricted-halver bounds for injective local inputs -/

@[expose] public section

open Finset

namespace Paterson

/-- The restricted initial halver guarantee also holds for an injective input
whose values lie in a larger ambient order. The restriction is measured by
the number of locally selected values, not by the ambient threshold. -/
theorem restricted_injective_initial {m n : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (k : ℕ) :
    let a := (Finset.univ.filter (fun i : Fin (2 * m) => (u i).val < k)).card
    (a : ℝ) ≤ (α : ℝ) * m →
    ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        m ≤ pos.val ∧ (net.exec u pos).val < k)).card : ℝ) ≤ (ε : ℝ) * a := by
  intro a ha
  let C := 2 * m
  let S := Finset.univ.image u
  have hcard : S.card = C := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  let gIso := S.orderIsoOfFin hcard
  let g : Fin C → Fin n := fun i => (gIso i).val
  have hg : StrictMono g := by
    intro x y hxy
    exact gIso.strictMono hxy
  have hmem : ∀ j, u j ∈ S :=
    fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let σfun : Fin C → Fin C := fun j => gIso.symm ⟨u j, hmem j⟩
  have hσinj : Function.Injective σfun := by
    intro i j hij
    have h := gIso.symm.injective hij
    exact hu (Subtype.ext_iff.mp h)
  let σ : Equiv.Perm (Fin C) := Equiv.ofBijective σfun
    ((Finite.injective_iff_bijective).mp hσinj)
  have hu_eq : ∀ j, u j = g (σ j) := by
    intro j
    show u j = (gIso (gIso.symm ⟨u j, hmem j⟩)).val
    simp [gIso.apply_symm_apply]
  have hexec : net.exec u = g ∘ net.exec (⇑σ) := by
    have heq : u = g ∘ ⇑σ := funext hu_eq
    rw [heq]
    exact ComparatorNetwork.exec_comp_mono net (StrictMono.monotone hg) (⇑σ)
  have ha_eq : a = (Finset.univ.filter (fun r : Fin C => (g r).val < k)).card := by
    apply Finset.card_nbij' σ σ.symm
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hu_eq i]
      exact hi
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rw [hu_eq (σ.symm r), σ.apply_symm_apply]
      exact hr
    · intro _ _
      simp
    · intro _ _
      simp
  have hthresh : ∀ r : Fin C, (g r).val < k ↔ r.val < a := by
    rw [ha_eq]
    exact strictMono_threshold hg k
  have hfilter : Finset.univ.filter (fun pos : Fin C =>
        m ≤ pos.val ∧ (net.exec u pos).val < k) =
      Finset.univ.filter (fun pos : Fin C =>
        m ≤ pos.val ∧ (net.exec (⇑σ) pos).val < a) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hm, hk⟩
      refine ⟨hm, ?_⟩
      have hh := congr_fun hexec pos
      simp only [Function.comp] at hh
      rw [hh] at hk
      exact (hthresh _).mp hk
    · intro ⟨hm, ha'⟩
      refine ⟨hm, ?_⟩
      have hh := congr_fun hexec pos
      simp only [Function.comp] at hh
      rw [hh]
      exact (hthresh _).mpr ha'
  rw [hfilter]
  exact (hnet σ).1 a ha

/-- Final-direction counterpart of `restricted_injective_initial`. -/
theorem restricted_injective_final {m n : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold : ℕ) :
    let a := (Finset.univ.filter (fun i : Fin (2 * m) =>
      threshold ≤ (u i).val)).card
    (a : ℝ) ≤ (α : ℝ) * m →
    ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        pos.val < m ∧ threshold ≤ (net.exec u pos).val)).card : ℝ) ≤
      (ε : ℝ) * a := by
  intro a ha
  let C := 2 * m
  let S := Finset.univ.image u
  have hcard : S.card = C := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  let gIso := S.orderIsoOfFin hcard
  let g : Fin C → Fin n := fun i => (gIso i).val
  have hg : StrictMono g := by
    intro x y hxy
    exact gIso.strictMono hxy
  have hmem : ∀ j, u j ∈ S :=
    fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let σfun : Fin C → Fin C := fun j => gIso.symm ⟨u j, hmem j⟩
  have hσinj : Function.Injective σfun := by
    intro i j hij
    have h := gIso.symm.injective hij
    exact hu (Subtype.ext_iff.mp h)
  let σ : Equiv.Perm (Fin C) := Equiv.ofBijective σfun
    ((Finite.injective_iff_bijective).mp hσinj)
  have hu_eq : ∀ j, u j = g (σ j) := by
    intro j
    show u j = (gIso (gIso.symm ⟨u j, hmem j⟩)).val
    simp [gIso.apply_symm_apply]
  have hexec : net.exec u = g ∘ net.exec (⇑σ) := by
    have heq : u = g ∘ ⇑σ := funext hu_eq
    rw [heq]
    exact ComparatorNetwork.exec_comp_mono net (StrictMono.monotone hg) (⇑σ)
  have ha_eq : a = (Finset.univ.filter (fun r : Fin C =>
      threshold ≤ (g r).val)).card := by
    apply Finset.card_nbij' σ σ.symm
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hu_eq i]
      exact hi
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rw [hu_eq (σ.symm r), σ.apply_symm_apply]
      exact hr
    · intro _ _
      simp
    · intro _ _
      simp
  have hthresh : ∀ r : Fin C,
      threshold ≤ (g r).val ↔ C - a ≤ r.val := by
    rw [ha_eq]
    exact strictMono_reverse_threshold hg threshold
  have hfilter : Finset.univ.filter (fun pos : Fin C =>
        pos.val < m ∧ threshold ≤ (net.exec u pos).val) =
      Finset.univ.filter (fun pos : Fin C =>
        pos.val < m ∧ C - a ≤ (net.exec (⇑σ) pos).val) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hm, hk⟩
      refine ⟨hm, ?_⟩
      have hh := congr_fun hexec pos
      simp only [Function.comp] at hh
      rw [hh] at hk
      exact (hthresh _).mp hk
    · intro ⟨hm, ha'⟩
      refine ⟨hm, ?_⟩
      have hh := congr_fun hexec pos
      simp only [Function.comp] at hh
      rw [hh]
      exact (hthresh _).mpr ha'
  rw [hfilter]
  exact (hnet σ).2 a ha

end Paterson
