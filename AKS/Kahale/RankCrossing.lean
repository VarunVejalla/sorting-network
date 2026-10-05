module

public import AKS.Kahale.RankInputs

/-! # An active pair of wires can receive adjacent ranks

Adjacent rank transpositions change each output rank by at most one. Since
output ranks are distinct, their relative order can change only through an
adjacent-rank pair. The permutation generators supply the global crossing.
-/

@[expose] public section

namespace Kahale

theorem inverted_ranks_have_adjacent_witness {n : ℕ} (net : ComparatorNetwork n)
    (i j : Fin n) (hij : i < j) (τ : Equiv.Perm (Fin n))
    (hinv : net.exec τ j < net.exec τ i) :
    ∃ σ : Equiv.Perm (Fin n),
      (net.exec σ i).val + 1 = (net.exec σ j).val ∨
      (net.exec σ j).val + 1 = (net.exec σ i).val := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    by_contra hn
    have hgap (π : Equiv.Perm (Fin (n + 1))) :
        (net.exec π i).val + 1 ≠ (net.exec π j).val ∧
        (net.exec π j).val + 1 ≠ (net.exec π i).val := by
      constructor
      · intro h; exact hn ⟨π, Or.inl h⟩
      · intro h; exact hn ⟨π, Or.inr h⟩
    have hne (π : Equiv.Perm (Fin (n + 1))) :
        (net.exec π i).val ≠ (net.exec π j).val := by
      intro h
      exact (ne_of_lt hij) (net.exec_injective π.injective (Fin.ext h))
    let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {g | ∀ π : Equiv.Perm (Fin (n + 1)),
          (net.exec ⇑(g * π) i).val < (net.exec ⇑(g * π) j).val ↔
            (net.exec π i).val < (net.exec π j).val}
        one_mem' := by intro π; simp
        mul_mem' := by
          intro g h hg hh π
          simpa only [mul_assoc] using (hg (h * π)).trans (hh π) }
    have hgen : Set.range (fun k : Fin n ↦ Equiv.swap k.castSucc k.succ) ⊆ S := by
      rintro g ⟨k, rfl⟩ π
      have hi₁ := exec_rank_add_one net ⇑(Equiv.swap k.castSucc k.succ * π) π
        (fun a ↦ (adjacent_swap_rank_step k (π a)).1) i
      have hi₂ := exec_rank_add_one net π ⇑(Equiv.swap k.castSucc k.succ * π)
        (fun a ↦ (adjacent_swap_rank_step k (π a)).2) i
      have hj₁ := exec_rank_add_one net ⇑(Equiv.swap k.castSucc k.succ * π) π
        (fun a ↦ (adjacent_swap_rank_step k (π a)).1) j
      have hj₂ := exec_rank_add_one net π ⇑(Equiv.swap k.castSucc k.succ * π)
        (fun a ↦ (adjacent_swap_rank_step k (π a)).2) j
      have h₁ := hgap π
      have h₂ := hgap (Equiv.swap k.castSucc k.succ * π)
      have he₁ := hne π
      have he₂ := hne (Equiv.swap k.castSucc k.succ * π)
      change (net.exec ⇑(Equiv.swap k.castSucc k.succ * π) i).val <
        (net.exec ⇑(Equiv.swap k.castSucc k.succ * π) j).val ↔ _
      omega
    have htop : (⊤ : Submonoid (Equiv.Perm (Fin (n + 1)))) ≤ S := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ n]
      exact Submonoid.closure_le.mpr hgen
    have hg : τ ∈ S := htop (by trivial)
    have he := hg (1 : Equiv.Perm (Fin (n + 1)))
    have hid : net.exec ⇑(1 : Equiv.Perm (Fin (n + 1))) = id :=
      net.exec_eq_of_monotone monotone_id
    simp only [mul_one, hid] at he
    have hi : (net.exec τ j).val < (net.exec τ i).val := hinv
    have hj : i.val < j.val := hij
    change (net.exec τ i).val < (net.exec τ j).val ↔ i.val < j.val at he
    omega

theorem boolean_inversion_rank_witness {n : ℕ} (net : ComparatorNetwork n)
    (i j : Fin n) (v : Fin n → Bool) (hi : net.exec v i = true)
    (hj : net.exec v j = false) :
    ∃ σ : Equiv.Perm (Fin n), net.exec σ j < net.exec σ i := by
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g := v ∘ σ.symm
  have hv : v = g ∘ σ := by funext k; simp [g]
  rw [hv, ComparatorNetwork.exec_comp_mono net hg] at hi hj
  simp only [Function.comp_apply] at hi hj
  refine ⟨σ, ?_⟩
  by_contra hn
  have h := hg (le_of_not_gt hn)
  simp only [Function.comp_apply] at h
  rw [hi, hj] at h
  exact (show ¬(true : Bool) ≤ false by decide) h

end Kahale
