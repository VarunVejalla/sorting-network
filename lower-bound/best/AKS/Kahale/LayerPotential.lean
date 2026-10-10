module

public import AKS.Kahale.BinomialPotential
public import AKS.Kahale.Certificates
public import AKS.Sort.Depth

/-! # Potential accounting through actual parallel comparator layers -/

@[expose] public section

namespace Kahale

open Finset

theorem height_fold_outside {n : ℕ} (cs : List (Comparator n)) (h : Fin n → ℕ)
    (i : Fin n) (hi : ∀ c ∈ cs, i ≠ c.i ∧ i ≠ c.j) :
    cs.foldl heightStep h i = h i := by
  induction cs generalizing h with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih _ (fun d hd ↦ hi d (List.mem_cons_of_mem c hd))]
    obtain ⟨h₁, h₂⟩ := hi c (List.mem_cons_self)
    simp [heightStep, h₁, h₂]

theorem sum_remove_pair {n : ℕ} (T : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (f : Fin n → ℕ) :
    ∑ i ∈ T, f i = f a + f b + ∑ i ∈ (T.erase a).erase b, f i := by
  have h₁ := sum_erase_add T f ha
  have hba : b ∈ T.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have h₂ := sum_erase_add (T.erase a) f hba
  omega

theorem parallel_layer_potential {n : ℕ} (cs : List (Comparator n))
    (hp : IsParallelLayer cs) (T : Finset (Fin n))
    (hT : ∀ c ∈ cs, c.i ∈ T ∧ c.j ∈ T) (h : Fin n → ℕ) (r L : ℕ) :
    (∑ i ∈ T, deficitPotential (r + 1) L (h i)) ≤
      2 * ∑ i ∈ T, deficitPotential r L (cs.foldl heightStep h i) := by
  induction cs generalizing T h with
  | nil =>
    simpa only [List.foldl_nil, mul_sum] using
      sum_le_sum (fun i (_ : i ∈ T) ↦ deficitPotential_idle r L (h i))
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    obtain ⟨hci, hcj⟩ := hT c List.mem_cons_self
    have hcne : c.i ≠ c.j := ne_of_lt c.h
    let T' := (T.erase c.i).erase c.j
    let h' := heightStep h c
    have hend : ∀ d ∈ cs, d.i ∈ T' ∧ d.j ∈ T' := by
      intro d hd
      have hm := hT d (List.mem_cons_of_mem c hd)
      have hn := hhead d hd
      unfold Comparator.overlaps at hn
      push_neg at hn
      simp only [T', mem_erase]
      exact ⟨⟨hn.2.2.1.symm, hn.1.symm, hm.1⟩,
        ⟨hn.2.2.2.symm, hn.2.1.symm, hm.2⟩⟩
    have hh := ih htail T' hend h'
    have heq : (∑ i ∈ T', deficitPotential (r + 1) L (h' i)) =
        ∑ i ∈ T', deficitPotential (r + 1) L (h i) := by
      apply sum_congr rfl
      intro i hi
      have hn := mem_erase.mp hi
      have hn' := mem_erase.mp hn.2
      simp [h', heightStep, hn.1, hn'.1]
    rw [heq] at hh
    have houti : cs.foldl heightStep h' c.i = min (h c.i) (h c.j) := by
      rw [height_fold_outside]
      · simp [h', heightStep]
      · intro d hd
        have hn := hhead d hd
        unfold Comparator.overlaps at hn
        tauto
    have houtj : cs.foldl heightStep h' c.j = max (h c.i) (h c.j) + 1 := by
      rw [height_fold_outside]
      · simp [h', heightStep, hcne.symm]
      · intro d hd
        have hn := hhead d hd
        unfold Comparator.overlaps at hn
        tauto
    have hin := sum_remove_pair T c.i c.j hci hcj hcne
      (fun i ↦ deficitPotential (r + 1) L (h i))
    have hout := sum_remove_pair T c.i c.j hci hcj hcne
      (fun i ↦ deficitPotential r L (cs.foldl heightStep h' i))
    rw [houti, houtj] at hout
    have hpair := deficitPotential_pair r L (h c.i) (h c.j)
    change (∑ i ∈ T, deficitPotential (r + 1) L (h i)) ≤
      2 * ∑ i ∈ T, deficitPotential r L (cs.foldl heightStep h' i)
    change (∑ i ∈ (T.erase c.i).erase c.j, deficitPotential (r + 1) L (h i)) ≤
      2 * ∑ i ∈ (T.erase c.i).erase c.j, deficitPotential r L (cs.foldl heightStep h' i) at hh
    omega

theorem parallel_layers_potential {n : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs) (h : Fin n → ℕ) (L : ℕ) :
    (∑ i : Fin n, deficitPotential layers.length L (h i)) ≤
      2 ^ layers.length * ∑ i : Fin n, deficitPotential 0 L (layers.flatten.foldl heightStep h i) := by
  induction layers generalizing h with
  | nil => simp
  | cons cs layers ih =>
    have h₁ := parallel_layer_potential cs (hp cs List.mem_cons_self) univ
      (by simp) h layers.length L
    have h₂ := ih (fun ds hd ↦ hp ds (List.mem_cons_of_mem cs hd)) (cs.foldl heightStep h)
    simp only [List.length_cons, List.flatten_cons, List.foldl_append]
    calc (∑ i, deficitPotential (layers.length + 1) L (h i))
        ≤ 2 * ∑ i, deficitPotential layers.length L (cs.foldl heightStep h i) := h₁
      _ ≤ 2 * (2 ^ layers.length * ∑ i,
          deficitPotential 0 L (layers.flatten.foldl heightStep (cs.foldl heightStep h) i)) :=
        Nat.mul_le_mul_left 2 h₂
      _ = _ := by rw [pow_succ']; ring

end Kahale
