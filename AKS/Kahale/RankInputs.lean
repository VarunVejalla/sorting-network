module

public import AKS.Kahale.ApproxSelection
public import AKS.Kahale.SelectionCounting
public import AKS.Sort.Perm
public import Mathlib.Order.Hom.Set

/-! # Bridges between rank permutations, Boolean selection and full sorting -/

@[expose] public section

namespace Kahale

open Finset

theorem monotone_rank_identity {n : ℕ} (w : Fin n → Fin n) (hm : Monotone w)
    (hi : Function.Injective w) : w = id := by
  let e : Fin n ≃o Fin n :=
    { toEquiv := Equiv.ofBijective w (Finite.injective_iff_bijective.mp hi)
      map_rel_iff' := fun {_ _} ↦ (hm.strictMono_iff_injective.mpr hi).le_iff_le }
  have he : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
  funext i
  exact congrArg (fun f : Fin n ≃o Fin n ↦ f i) he

theorem sorting_rank_identity {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (σ : Equiv.Perm (Fin n)) : net.exec σ = id :=
  monotone_rank_identity _ (hs _ σ) (net.exec_injective σ.injective)

theorem permuted_zero_count {n : ℕ} (v : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    (univ.filter (fun i ↦ (v ∘ σ.symm) i = false)).card =
      (univ.filter (fun i ↦ v i = false)).card := by
  apply card_nbij' σ.symm σ
  · intro i hi
    simpa only [mem_coe, mem_filter, mem_univ, true_and, Function.comp_apply] using hi
  · intro i hi
    simpa only [mem_coe, mem_filter, mem_univ, true_and, Function.comp_apply, σ.symm_apply_apply] using hi
  · intro i _
    exact σ.apply_symm_apply i
  · intro i _
    exact σ.symm_apply_apply i

theorem monotone_zero_rank {n : ℕ} (g : Fin n → Bool) (hg : Monotone g) (i : Fin n)
    (hi : g i = false) : i.val < (univ.filter (fun j ↦ g j = false)).card := by
  have hsub : Iic i ⊆ univ.filter (fun j ↦ g j = false) := by
    intro j hj
    refine mem_filter.mpr ⟨mem_univ j, ?_⟩
    have he : g j ≤ false := hi ▸ hg (mem_Iic.mp hj)
    cases hjg : g j
    · rfl
    · rw [hjg] at he
      exact False.elim ((show ¬(true : Bool) ≤ false by decide) he)
  have hh := card_le_card hsub
  rw [Fin.card_Iic] at hh
  omega

theorem approx_select_zeros {n t B : ℕ} (net : ComparatorNetwork n)
    (hs : ApproxSelect net t B) : SelectZeros net t B := by
  intro v hc i hi
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g := v ∘ σ.symm
  have hv : v = g ∘ σ := by funext j; simp [g]
  have ho : g (net.exec σ i) = false := by
    rw [hv, ComparatorNetwork.exec_comp_mono net hg] at hi
    exact hi
  have hr := monotone_zero_rank g hg (net.exec σ i) ho
  have he := permuted_zero_count v σ
  change (univ.filter (fun j ↦ g j = false)).card = _ at he
  rw [he] at hr
  exact (hs σ i).1 (by omega)

end Kahale
