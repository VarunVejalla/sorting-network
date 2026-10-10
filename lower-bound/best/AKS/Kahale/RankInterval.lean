module

public import AKS.Sort.Monotone
public import Mathlib.GroupTheory.Perm.Sign

/-! # Attainable ranks on a wire form an interval

Kahale et al., STOC 1995, Lemma 5.2 (attributed there to Knuth).
The proof uses adjacent rank transpositions and the fact that min/max gates
preserve a pointwise change of at most one. No sorting hypothesis is needed.
-/

@[expose] public section

namespace Kahale

theorem exec_nat_add_one {n : ℕ} (net : ComparatorNetwork n)
    (u v : Fin n → ℕ) (h : ∀ i, u i ≤ v i + 1) :
    ∀ i, net.exec u i ≤ net.exec v i + 1 := by
  obtain ⟨cs⟩ := net
  induction cs generalizing u v with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    intro i
    have hi := h i
    have hl := h c.i
    have hr := h c.j
    simp only [Comparator.apply]
    split_ifs <;> omega

theorem exec_rank_add_one {n : ℕ} (net : ComparatorNetwork n)
    (u v : Fin n → Fin n) (h : ∀ i, (u i).val ≤ (v i).val + 1) (i : Fin n) :
    (net.exec u i).val ≤ (net.exec v i).val + 1 := by
  have hv (w : Fin n → Fin n) :
      net.exec (Fin.val ∘ w) i = (net.exec w i).val :=
    (congrFun (net.exec_comp_monotone (f := Fin.val) (fun _ _ hab ↦ hab) w) i).symm
  have hh := exec_nat_add_one net (Fin.val ∘ u) (Fin.val ∘ v) h i
  rwa [hv u, hv v] at hh

theorem adjacent_swap_rank_step {n : ℕ} (j : Fin n) (a : Fin (n + 1)) :
    (Equiv.swap j.castSucc j.succ a).val ≤ a.val + 1 ∧
      a.val ≤ (Equiv.swap j.castSucc j.succ a).val + 1 := by
  by_cases hl : a = j.castSucc
  · subst a
    simp
    omega
  · by_cases hr : a = j.succ
    · subst a
      simp
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      omega

theorem wire_rank_interval {n : ℕ} (net : ComparatorNetwork n) (wire k : Fin n)
    (σ τ : Equiv.Perm (Fin n))
    (hl : net.exec σ wire ≤ k) (hr : k ≤ net.exec τ wire) :
    ∃ π : Equiv.Perm (Fin n), net.exec π wire = k := by
  classical
  cases n with
  | zero => exact Fin.elim0 wire
  | succ n =>
    by_contra hn
    have hne (π : Equiv.Perm (Fin (n + 1))) : (net.exec π wire).val ≠ k.val := by
      intro h
      exact hn ⟨π, Fin.ext h⟩
    let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {g | ∀ π : Equiv.Perm (Fin (n + 1)),
          (net.exec ⇑(g * π) wire).val < k.val ↔ (net.exec π wire).val < k.val}
        one_mem' := by intro π; simp
        mul_mem' := by
          intro g h hg hh π
          simpa only [mul_assoc] using (hg (h * π)).trans (hh π) }
    have hgen : Set.range (fun j : Fin n ↦ Equiv.swap j.castSucc j.succ) ⊆ S := by
      rintro g ⟨j, rfl⟩ π
      have h₁ := exec_rank_add_one net ⇑(Equiv.swap j.castSucc j.succ * π) π
        (fun i ↦ (adjacent_swap_rank_step j (π i)).1) wire
      have h₂ := exec_rank_add_one net π ⇑(Equiv.swap j.castSucc j.succ * π)
        (fun i ↦ (adjacent_swap_rank_step j (π i)).2) wire
      have ha := hne (Equiv.swap j.castSucc j.succ * π)
      have hb := hne π
      change (net.exec ⇑(Equiv.swap j.castSucc j.succ * π) wire).val < k.val ↔ _
      omega
    have htop : (⊤ : Submonoid (Equiv.Perm (Fin (n + 1)))) ≤ S := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ n]
      exact Submonoid.closure_le.mpr hgen
    have hg : τ * σ⁻¹ ∈ S := htop (by trivial)
    have he := hg σ
    simp only [inv_mul_cancel_right] at he
    have hσ := hne σ
    have hτ := hne τ
    change (net.exec σ wire).val ≤ k.val at hl
    change k.val ≤ (net.exec τ wire).val at hr
    omega

end Kahale
