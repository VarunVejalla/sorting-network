module

public import AKS.Sort.Depth

/-! Parallel composition through two disjoint increasing wire embeddings. -/

@[expose] public section

def parallelEmbeddings {m n : ℕ} (e : Fin 2 → (Fin m ↪o Fin n))
    (nets : Fin 2 → ComparatorNetwork m) : ComparatorNetwork n :=
  ⟨([0, 1] : List (Fin 2)).flatMap fun s ↦ ((nets s).scatterEmbed n (e s)).comparators⟩

theorem parallelEmbeddings_depth_le {m n d : ℕ} (e : Fin 2 → (Fin m ↪o Fin n))
    (nets : Fin 2 → ComparatorNetwork m) (hdis : ∀ i j, e 0 i ≠ e 1 j)
    (hd : ∀ s, (nets s).depth ≤ d) : (parallelEmbeddings e nets).depth ≤ d := by
  apply depth_flatMap_disjoint
  · intro s _
    exact (depth_scatterEmbed_le _ _ _).trans (hd s)
  · apply List.pairwise_cons.mpr
    constructor
    · intro s hs
      have he : s = 1 := List.mem_singleton.mp hs
      subst s
      intro c hc d hd
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
      exact ⟨⟨hdis a.i b.i, hdis a.i b.j⟩, ⟨hdis a.j b.i, hdis a.j b.j⟩⟩
    · simp

theorem parallelEmbeddings_exec_inside {m n : ℕ} {α : Type*} [LinearOrder α]
    (e : Fin 2 → (Fin m ↪o Fin n)) (nets : Fin 2 → ComparatorNetwork m)
    (hdis : ∀ i j, e 0 i ≠ e 1 j) (w : Fin n → α) (s : Fin 2) (j : Fin m) :
    (parallelEmbeddings e nets).exec w (e s j) = (nets s).exec (w ∘ e s) j := by
  have hout (a b : Fin 2) (h : ∀ i j, e a i ≠ e b j) (v : Fin n → α) (l : Fin m) :
      ((nets b).scatterEmbed n (e b)).exec v (e a l) = v (e a l) := by
    apply ComparatorNetwork.scatterEmbed_exec_outside
    rintro ⟨i, hi⟩
    exact h l i hi.symm
  unfold parallelEmbeddings
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [ComparatorNetwork.exec_append]
  fin_cases s <;> dsimp only
  · change ((nets 1).scatterEmbed n (e 1)).exec (((nets 0).scatterEmbed n (e 0)).exec w)
      (e 0 j) = (nets 0).exec (w ∘ e 0) j
    rw [hout 0 1 hdis, ComparatorNetwork.scatterEmbed_exec_inside]
  · change ((nets 1).scatterEmbed n (e 1)).exec (((nets 0).scatterEmbed n (e 0)).exec w)
      (e 1 j) = (nets 1).exec (w ∘ e 1) j
    rw [ComparatorNetwork.scatterEmbed_exec_inside]
    have hv : (((nets 0).scatterEmbed n (e 0)).exec w) ∘ e 1 = w ∘ e 1 := by
      funext l
      exact hout 1 0 (fun i j ↦ (hdis j i).symm) w l
    rw [hv]
