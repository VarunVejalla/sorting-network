module

public import AKS.Sort.Depth

/-! Exact execution at the endpoints of a comparator in a parallel layer. -/

@[expose] public section

theorem Comparator.apply_nonoverlap {n : ℕ} {α : Type*} [LinearOrder α]
    {d c : Comparator n} (h : ¬d.overlaps c) (w : Fin n → α) :
    d.apply w c.i = w c.i ∧ d.apply w c.j = w c.j := by
  unfold Comparator.overlaps at h
  push_neg at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp [Comparator.apply, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄]

theorem parallel_layer_exec_endpoints {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (hp : IsParallelLayer cs) (c : Comparator n)
    (hc : c ∈ cs) (w : Fin n → α) :
    (ComparatorNetwork.mk cs).exec w c.i = min (w c.i) (w c.j) ∧
    (ComparatorNetwork.mk cs).exec w c.j = max (w c.i) (w c.j) := by
  induction cs generalizing w with
  | nil => simp at hc
  | cons d ds ih =>
    obtain ⟨hd, hds⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hc with h | h
    · subst d
      have hi : ∀ e ∈ ds, c.i ≠ e.i ∧ c.i ≠ e.j := by
        intro e he
        have hn := hd e he
        unfold Comparator.overlaps at hn
        tauto
      have hj : ∀ e ∈ ds, c.j ≠ e.i ∧ c.j ≠ e.j := by
        intro e he
        have hn := hd e he
        unfold Comparator.overlaps at hn
        tauto
      change ds.foldl (fun v e ↦ e.apply v) (c.apply w) c.i = _ ∧
        ds.foldl (fun v e ↦ e.apply v) (c.apply w) c.j = _
      rw [foldl_comparators_outside ds (c.apply w) c.i hi,
        foldl_comparators_outside ds (c.apply w) c.j hj]
      have hne : c.j ≠ c.i := ne_of_gt c.h
      simp [Comparator.apply, hne]
    · have hr := ih hds h (d.apply w)
      have he := Comparator.apply_nonoverlap (hd c h) w
      simpa only [ComparatorNetwork.exec, List.foldl_cons, he.1, he.2] using hr
