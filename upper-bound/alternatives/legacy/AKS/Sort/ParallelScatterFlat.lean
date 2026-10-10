module

public import AKS.Sort.Depth

/-! FlatMap of identical scatter-embedded networks on pairwise-disjoint wire ranges. -/

@[expose] public section

/-- Sequential composition of `net` scatter-embedded along each embedding in `xs`. -/
def parallelScatterFlat {ι : Type*} {m n : ℕ}
    (xs : List ι) (e : ι → (Fin m ↪o Fin n)) (net : ComparatorNetwork m) :
    ComparatorNetwork n :=
  ⟨xs.flatMap fun a ↦ (net.scatterEmbed n (e a)).comparators⟩

private theorem scatterEmbed_preserves_foreign {m n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (e e' : Fin m ↪o Fin n)
    (hdis : ∀ i j, e i ≠ e' j) (v : Fin n → α) (l : Fin m) :
    (net.scatterEmbed n e').exec v (e l) = v (e l) := by
  apply ComparatorNetwork.scatterEmbed_exec_outside
  rintro ⟨i, hi⟩
  exact (hdis l i).symm hi

/-- On wires of block `s ∈ xs`, `parallelScatterFlat` agrees with `net` on the local view. -/
theorem parallelScatterFlat_exec_inside {ι : Type*} {m n : ℕ} {α : Type*} [LinearOrder α]
    [DecidableEq ι] (xs : List ι) (hxs : xs.Nodup)
    (e : ι → (Fin m ↪o Fin n)) (net : ComparatorNetwork m)
    (hdis : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ i j, e a i ≠ e b j)
    (w : Fin n → α) (s : ι) (hs : s ∈ xs) (j : Fin m) :
    (parallelScatterFlat xs e net).exec w (e s j) = net.exec (w ∘ e s) j := by
  have hflat :=
    ComparatorNetwork.exec_flatMap xs (fun a => net.scatterEmbed n (e a)) w
  change (⟨xs.flatMap fun a ↦ (net.scatterEmbed n (e a)).comparators⟩ :
      ComparatorNetwork n).exec w (e s j) = _
  rw [hflat]
  -- Abstract foldl statement by induction on `xs`.
  have hgen : ∀ (ys : List ι) (v : Fin n → α),
      ys.Nodup →
      (∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → ∀ i j, e a i ≠ e b j) →
      ∀ t ∈ ys, ∀ k : Fin m,
        ys.foldl (fun v' a => (net.scatterEmbed n (e a)).exec v') v (e t k) =
          net.exec (v ∘ e t) k := by
    intro ys
    induction ys with
    | nil =>
      intro v _ _ t ht; cases ht
    | cons x ys ih =>
      intro v hnodup hdis' t ht k
      have hnodup_t : ys.Nodup := (List.nodup_cons.mp hnodup).2
      have hx_nin : x ∉ ys := (List.nodup_cons.mp hnodup).1
      have hdis_t : ∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → ∀ i j, e a i ≠ e b j :=
        fun a ha b hb hne =>
          hdis' a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hne
      simp only [List.foldl_cons, List.mem_cons] at ht ⊢
      rcases ht with rfl | ht
      · have hinside :=
          ComparatorNetwork.scatterEmbed_exec_inside net n (e t) v k
        have hrest :
            ys.foldl (fun v' a => (net.scatterEmbed n (e a)).exec v')
              ((net.scatterEmbed n (e t)).exec v) (e t k) =
              (net.scatterEmbed n (e t)).exec v (e t k) := by
          refine ComparatorNetwork.foldl_exec_outside ys
            (fun a => net.scatterEmbed n (e a)) _ (e t k) ?_
          intro a ha c hc
          have hne : a ≠ t := fun heq => hx_nin (heq ▸ ha)
          have hj : e t k ∉ Set.range (e a) := by
            rintro ⟨p, hp⟩
            exact hdis' t List.mem_cons_self a (List.mem_cons_of_mem _ ha)
              (Ne.symm hne) k p hp.symm
          exact ComparatorNetwork.scatterEmbed_comparators_outside net n (e a)
            (e t k) hj c hc
        rw [hrest, hinside]
      · have hne : x ≠ t := fun heq => hx_nin (heq ▸ ht)
        have hforeign : ∀ i j : Fin m, e t i ≠ e x j :=
          fun i j => hdis' t (List.mem_cons_of_mem _ ht) x List.mem_cons_self
            (Ne.symm hne) i j
        have hw' : ((net.scatterEmbed n (e x)).exec v) ∘ e t = v ∘ e t := by
          funext l
          exact scatterEmbed_preserves_foreign net (e t) (e x) hforeign v l
        have hih := ih ((net.scatterEmbed n (e x)).exec v) hnodup_t hdis_t t ht k
        simpa [hw'] using hih
  exact hgen xs w hxs hdis s hs j

end
